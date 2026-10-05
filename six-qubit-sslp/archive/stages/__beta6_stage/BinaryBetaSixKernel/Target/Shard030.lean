-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R017.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R019.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R021.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R022.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard030

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(0, 1, 3, 3, 5, 6)`. -/
def targetTop_0480 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 0;
     0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0480 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0480 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0480 : BottomDetBound targetTop_0480 9 := by
  have hU : rowTransform_0480.det.natAbs = 1 := by
    have hdet : rowTransform_0480.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R022.Aggregate.bottomBound.transformTopRows rowTransform_0480 hU
  have hcols := hrows.permuteColumns columnPerm_0480
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0480 MainTheory.Generated.BinaryBetaSixKernel.Representative.R022.Base.explicitTop)
          columnPerm_0480 = targetTop_0480 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0480 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 3 3 5 6)) 9 := by
  have htop : targetTop_0480 =
      topOfPattern (R := ℤ) (angle6 0 1 3 3 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0480

/-- Explicit target top block for canonical pattern `(0, 1, 3, 3, 5, 7)`. -/
def targetTop_0481 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0481 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_0481 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 5, 4]
  invFun := ![0, 2, 3, 1, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0481 : BottomDetBound targetTop_0481 9 := by
  have hU : rowTransform_0481.det.natAbs = 1 := by
    have hdet : rowTransform_0481.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Aggregate.bottomBound.transformTopRows rowTransform_0481 hU
  have hcols := hrows.permuteColumns columnPerm_0481
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0481 MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Base.explicitTop)
          columnPerm_0481 = targetTop_0481 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0481 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 3 3 5 7)) 9 := by
  have htop : targetTop_0481 =
      topOfPattern (R := ℤ) (angle6 0 1 3 3 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0481

/-- Explicit target top block for canonical pattern `(0, 1, 3, 3, 6, 6)`. -/
def targetTop_0482 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 0;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0482 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 1, 0;
     0, 1, 0]

def columnPerm_0482 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0482 : BottomDetBound targetTop_0482 9 := by
  have hU : rowTransform_0482.det.natAbs = 1 := by
    have hdet : rowTransform_0482.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0482 hU
  have hcols := hrows.permuteColumns columnPerm_0482
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0482 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0482 = targetTop_0482 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0482 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 3 3 6 6)) 9 := by
  have htop : targetTop_0482 =
      topOfPattern (R := ℤ) (angle6 0 1 3 3 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0482

/-- Explicit target top block for canonical pattern `(0, 1, 3, 3, 6, 7)`. -/
def targetTop_0483 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0483 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 1;
     0, 0, 1]

def columnPerm_0483 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 4, 5]
  invFun := ![0, 2, 3, 1, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0483 : BottomDetBound targetTop_0483 9 := by
  have hU : rowTransform_0483.det.natAbs = 1 := by
    have hdet : rowTransform_0483.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate.bottomBound.transformTopRows rowTransform_0483 hU
  have hcols := hrows.permuteColumns columnPerm_0483
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0483 MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Base.explicitTop)
          columnPerm_0483 = targetTop_0483 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0483 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 3 3 6 7)) 9 := by
  have htop : targetTop_0483 =
      topOfPattern (R := ℤ) (angle6 0 1 3 3 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0483

/-- Explicit target top block for canonical pattern `(0, 1, 3, 3, 7, 7)`. -/
def targetTop_0484 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0484 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     1, 1, 0;
     0, 1, 0]

def columnPerm_0484 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0484 : BottomDetBound targetTop_0484 9 := by
  have hU : rowTransform_0484.det.natAbs = 1 := by
    have hdet : rowTransform_0484.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0484 hU
  have hcols := hrows.permuteColumns columnPerm_0484
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0484 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0484 = targetTop_0484 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0484 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 3 3 7 7)) 9 := by
  have htop : targetTop_0484 =
      topOfPattern (R := ℤ) (angle6 0 1 3 3 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0484

/-- Explicit target top block for canonical pattern `(0, 1, 3, 4, 4, 4)`. -/
def targetTop_0485 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0485 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 0, 1;
     1, 0, 0]

def columnPerm_0485 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0485 : BottomDetBound targetTop_0485 9 := by
  have hU : rowTransform_0485.det.natAbs = 1 := by
    have hdet : rowTransform_0485.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0485 hU
  have hcols := hrows.permuteColumns columnPerm_0485
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0485 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0485 = targetTop_0485 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0485 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 3 4 4 4)) 9 := by
  have htop : targetTop_0485 =
      topOfPattern (R := ℤ) (angle6 0 1 3 4 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0485

/-- Explicit target top block for canonical pattern `(0, 1, 3, 4, 4, 5)`. -/
def targetTop_0486 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 1;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0486 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 0, 1;
     1, 0, 0]

def columnPerm_0486 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 5, 1, 2, 4]
  invFun := ![0, 3, 4, 1, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0486 : BottomDetBound targetTop_0486 9 := by
  have hU : rowTransform_0486.det.natAbs = 1 := by
    have hdet : rowTransform_0486.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0486 hU
  have hcols := hrows.permuteColumns columnPerm_0486
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0486 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0486 = targetTop_0486 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0486 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 3 4 4 5)) 9 := by
  have htop : targetTop_0486 =
      topOfPattern (R := ℤ) (angle6 0 1 3 4 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0486

/-- Explicit target top block for canonical pattern `(0, 1, 3, 4, 4, 6)`. -/
def targetTop_0487 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 0;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0487 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_0487 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 5, 1, 2, 4]
  invFun := ![0, 3, 4, 1, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0487 : BottomDetBound targetTop_0487 9 := by
  have hU : rowTransform_0487.det.natAbs = 1 := by
    have hdet : rowTransform_0487.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Aggregate.bottomBound.transformTopRows rowTransform_0487 hU
  have hcols := hrows.permuteColumns columnPerm_0487
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0487 MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Base.explicitTop)
          columnPerm_0487 = targetTop_0487 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0487 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 3 4 4 6)) 9 := by
  have htop : targetTop_0487 =
      topOfPattern (R := ℤ) (angle6 0 1 3 4 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0487

/-- Explicit target top block for canonical pattern `(0, 1, 3, 4, 4, 7)`. -/
def targetTop_0488 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 1;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0488 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 1, 0;
     1, 0, 0]

def columnPerm_0488 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 3, 1, 2, 4]
  invFun := ![0, 3, 4, 2, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0488 : BottomDetBound targetTop_0488 9 := by
  have hU : rowTransform_0488.det.natAbs = 1 := by
    have hdet : rowTransform_0488.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0488 hU
  have hcols := hrows.permuteColumns columnPerm_0488
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0488 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0488 = targetTop_0488 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0488 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 3 4 4 7)) 9 := by
  have htop : targetTop_0488 =
      topOfPattern (R := ℤ) (angle6 0 1 3 4 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0488

/-- Explicit target top block for canonical pattern `(0, 1, 3, 4, 5, 5)`. -/
def targetTop_0489 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 1, 1;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0489 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 0, 1;
     0, 1, 0]

def columnPerm_0489 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0489 : BottomDetBound targetTop_0489 9 := by
  have hU : rowTransform_0489.det.natAbs = 1 := by
    have hdet : rowTransform_0489.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Aggregate.bottomBound.transformTopRows rowTransform_0489 hU
  have hcols := hrows.permuteColumns columnPerm_0489
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0489 MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Base.explicitTop)
          columnPerm_0489 = targetTop_0489 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0489 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 3 4 5 5)) 9 := by
  have htop : targetTop_0489 =
      topOfPattern (R := ℤ) (angle6 0 1 3 4 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0489

/-- Explicit target top block for canonical pattern `(0, 1, 3, 4, 5, 6)`. -/
def targetTop_0490 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 1, 0;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0490 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_0490 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0490 : BottomDetBound targetTop_0490 9 := by
  have hU : rowTransform_0490.det.natAbs = 1 := by
    have hdet : rowTransform_0490.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R019.Aggregate.bottomBound.transformTopRows rowTransform_0490 hU
  have hcols := hrows.permuteColumns columnPerm_0490
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0490 MainTheory.Generated.BinaryBetaSixKernel.Representative.R019.Base.explicitTop)
          columnPerm_0490 = targetTop_0490 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0490 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 3 4 5 6)) 9 := by
  have htop : targetTop_0490 =
      topOfPattern (R := ℤ) (angle6 0 1 3 4 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0490

/-- Explicit target top block for canonical pattern `(0, 1, 3, 4, 5, 7)`. -/
def targetTop_0491 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 1, 1;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0491 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 0, 1;
     1, 0, 0]

def columnPerm_0491 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 4, 1, 3, 5]
  invFun := ![0, 3, 1, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0491 : BottomDetBound targetTop_0491 9 := by
  have hU : rowTransform_0491.det.natAbs = 1 := by
    have hdet : rowTransform_0491.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R017.Aggregate.bottomBound.transformTopRows rowTransform_0491 hU
  have hcols := hrows.permuteColumns columnPerm_0491
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0491 MainTheory.Generated.BinaryBetaSixKernel.Representative.R017.Base.explicitTop)
          columnPerm_0491 = targetTop_0491 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0491 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 3 4 5 7)) 9 := by
  have htop : targetTop_0491 =
      topOfPattern (R := ℤ) (angle6 0 1 3 4 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0491

/-- Explicit target top block for canonical pattern `(0, 1, 3, 4, 6, 6)`. -/
def targetTop_0492 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 0;
     0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0492 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, (-1);
     1, 0, 0]

def columnPerm_0492 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 3, 4, 1, 2]
  invFun := ![0, 4, 5, 2, 3, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0492 : BottomDetBound targetTop_0492 9 := by
  have hU : rowTransform_0492.det.natAbs = 1 := by
    have hdet : rowTransform_0492.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Aggregate.bottomBound.transformTopRows rowTransform_0492 hU
  have hcols := hrows.permuteColumns columnPerm_0492
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0492 MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Base.explicitTop)
          columnPerm_0492 = targetTop_0492 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0492 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 3 4 6 6)) 9 := by
  have htop : targetTop_0492 =
      topOfPattern (R := ℤ) (angle6 0 1 3 4 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0492

/-- Explicit target top block for canonical pattern `(0, 1, 3, 4, 6, 7)`. -/
def targetTop_0493 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 1;
     0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0493 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, (-1);
     0, 1, 0;
     0, 0, 1]

def columnPerm_0493 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0493 : BottomDetBound targetTop_0493 9 := by
  have hU : rowTransform_0493.det.natAbs = 1 := by
    have hdet : rowTransform_0493.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R021.Aggregate.bottomBound.transformTopRows rowTransform_0493 hU
  have hcols := hrows.permuteColumns columnPerm_0493
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0493 MainTheory.Generated.BinaryBetaSixKernel.Representative.R021.Base.explicitTop)
          columnPerm_0493 = targetTop_0493 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0493 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 3 4 6 7)) 9 := by
  have htop : targetTop_0493 =
      topOfPattern (R := ℤ) (angle6 0 1 3 4 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0493

/-- Explicit target top block for canonical pattern `(0, 1, 3, 4, 7, 7)`. -/
def targetTop_0494 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 1, 1;
     0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0494 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_0494 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0494 : BottomDetBound targetTop_0494 9 := by
  have hU : rowTransform_0494.det.natAbs = 1 := by
    have hdet : rowTransform_0494.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Aggregate.bottomBound.transformTopRows rowTransform_0494 hU
  have hcols := hrows.permuteColumns columnPerm_0494
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0494 MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Base.explicitTop)
          columnPerm_0494 = targetTop_0494 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0494 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 3 4 7 7)) 9 := by
  have htop : targetTop_0494 =
      topOfPattern (R := ℤ) (angle6 0 1 3 4 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0494

/-- Explicit target top block for canonical pattern `(0, 1, 3, 5, 5, 5)`. -/
def targetTop_0495 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0495 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 0, 1;
     1, 0, 0]

def columnPerm_0495 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0495 : BottomDetBound targetTop_0495 9 := by
  have hU : rowTransform_0495.det.natAbs = 1 := by
    have hdet : rowTransform_0495.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0495 hU
  have hcols := hrows.permuteColumns columnPerm_0495
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0495 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0495 = targetTop_0495 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0495 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 3 5 5 5)) 9 := by
  have htop : targetTop_0495 =
      topOfPattern (R := ℤ) (angle6 0 1 3 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0495

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard030
