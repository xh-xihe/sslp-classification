-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R013.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R017.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R018.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R020.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard028

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(0, 1, 2, 3, 6, 7)`. -/
def targetTop_0448 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 0, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0448 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0448 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0448 : BottomDetBound targetTop_0448 9 := by
  have hU : rowTransform_0448.det.natAbs = 1 := by
    have hdet : rowTransform_0448.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R017.Aggregate.bottomBound.transformTopRows rowTransform_0448 hU
  have hcols := hrows.permuteColumns columnPerm_0448
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0448 MainTheory.Generated.BinaryBetaSixKernel.Representative.R017.Base.explicitTop)
          columnPerm_0448 = targetTop_0448 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0448 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 3 6 7)) 9 := by
  have htop : targetTop_0448 =
      topOfPattern (R := ℤ) (angle6 0 1 2 3 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0448

/-- Explicit target top block for canonical pattern `(0, 1, 2, 3, 7, 7)`. -/
def targetTop_0449 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0449 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 1;
     1, 0, 0]

def columnPerm_0449 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 4, 5, 1, 2]
  invFun := ![0, 4, 5, 1, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0449 : BottomDetBound targetTop_0449 9 := by
  have hU : rowTransform_0449.det.natAbs = 1 := by
    have hdet : rowTransform_0449.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate.bottomBound.transformTopRows rowTransform_0449 hU
  have hcols := hrows.permuteColumns columnPerm_0449
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0449 MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Base.explicitTop)
          columnPerm_0449 = targetTop_0449 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0449 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 3 7 7)) 9 := by
  have htop : targetTop_0449 =
      topOfPattern (R := ℤ) (angle6 0 1 2 3 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0449

/-- Explicit target top block for canonical pattern `(0, 1, 2, 4, 4, 4)`. -/
def targetTop_0450 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0450 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_0450 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0450 : BottomDetBound targetTop_0450 9 := by
  have hU : rowTransform_0450.det.natAbs = 1 := by
    have hdet : rowTransform_0450.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0450 hU
  have hcols := hrows.permuteColumns columnPerm_0450
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0450 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0450 = targetTop_0450 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0450 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 4 4 4)) 9 := by
  have htop : targetTop_0450 =
      topOfPattern (R := ℤ) (angle6 0 1 2 4 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0450

/-- Explicit target top block for canonical pattern `(0, 1, 2, 4, 4, 5)`. -/
def targetTop_0451 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 1;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0451 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_0451 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 5, 1, 2, 4]
  invFun := ![0, 3, 4, 1, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0451 : BottomDetBound targetTop_0451 9 := by
  have hU : rowTransform_0451.det.natAbs = 1 := by
    have hdet : rowTransform_0451.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0451 hU
  have hcols := hrows.permuteColumns columnPerm_0451
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0451 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0451 = targetTop_0451 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0451 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 4 4 5)) 9 := by
  have htop : targetTop_0451 =
      topOfPattern (R := ℤ) (angle6 0 1 2 4 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0451

/-- Explicit target top block for canonical pattern `(0, 1, 2, 4, 4, 6)`. -/
def targetTop_0452 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0452 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 0]

def columnPerm_0452 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 3, 1, 2, 4]
  invFun := ![0, 3, 4, 2, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0452 : BottomDetBound targetTop_0452 9 := by
  have hU : rowTransform_0452.det.natAbs = 1 := by
    have hdet : rowTransform_0452.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0452 hU
  have hcols := hrows.permuteColumns columnPerm_0452
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0452 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0452 = targetTop_0452 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0452 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 4 4 6)) 9 := by
  have htop : targetTop_0452 =
      topOfPattern (R := ℤ) (angle6 0 1 2 4 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0452

/-- Explicit target top block for canonical pattern `(0, 1, 2, 4, 4, 7)`. -/
def targetTop_0453 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 1;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0453 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_0453 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 4, 1, 2, 5]
  invFun := ![0, 3, 4, 1, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0453 : BottomDetBound targetTop_0453 9 := by
  have hU : rowTransform_0453.det.natAbs = 1 := by
    have hdet : rowTransform_0453.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R013.Aggregate.bottomBound.transformTopRows rowTransform_0453 hU
  have hcols := hrows.permuteColumns columnPerm_0453
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0453 MainTheory.Generated.BinaryBetaSixKernel.Representative.R013.Base.explicitTop)
          columnPerm_0453 = targetTop_0453 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0453 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 4 4 7)) 9 := by
  have htop : targetTop_0453 =
      topOfPattern (R := ℤ) (angle6 0 1 2 4 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0453

/-- Explicit target top block for canonical pattern `(0, 1, 2, 4, 5, 5)`. -/
def targetTop_0454 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 1, 1;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0454 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_0454 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0454 : BottomDetBound targetTop_0454 9 := by
  have hU : rowTransform_0454.det.natAbs = 1 := by
    have hdet : rowTransform_0454.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Aggregate.bottomBound.transformTopRows rowTransform_0454 hU
  have hcols := hrows.permuteColumns columnPerm_0454
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0454 MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Base.explicitTop)
          columnPerm_0454 = targetTop_0454 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0454 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 4 5 5)) 9 := by
  have htop : targetTop_0454 =
      topOfPattern (R := ℤ) (angle6 0 1 2 4 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0454

/-- Explicit target top block for canonical pattern `(0, 1, 2, 4, 5, 6)`. -/
def targetTop_0455 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 1, 0;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0455 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_0455 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 4, 1, 3, 5]
  invFun := ![0, 3, 1, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0455 : BottomDetBound targetTop_0455 9 := by
  have hU : rowTransform_0455.det.natAbs = 1 := by
    have hdet : rowTransform_0455.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R017.Aggregate.bottomBound.transformTopRows rowTransform_0455 hU
  have hcols := hrows.permuteColumns columnPerm_0455
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0455 MainTheory.Generated.BinaryBetaSixKernel.Representative.R017.Base.explicitTop)
          columnPerm_0455 = targetTop_0455 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0455 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 4 5 6)) 9 := by
  have htop : targetTop_0455 =
      topOfPattern (R := ℤ) (angle6 0 1 2 4 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0455

/-- Explicit target top block for canonical pattern `(0, 1, 2, 4, 5, 7)`. -/
def targetTop_0456 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 1, 1;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0456 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_0456 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0456 : BottomDetBound targetTop_0456 9 := by
  have hU : rowTransform_0456.det.natAbs = 1 := by
    have hdet : rowTransform_0456.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R018.Aggregate.bottomBound.transformTopRows rowTransform_0456 hU
  have hcols := hrows.permuteColumns columnPerm_0456
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0456 MainTheory.Generated.BinaryBetaSixKernel.Representative.R018.Base.explicitTop)
          columnPerm_0456 = targetTop_0456 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0456 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 4 5 7)) 9 := by
  have htop : targetTop_0456 =
      topOfPattern (R := ℤ) (angle6 0 1 2 4 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0456

/-- Explicit target top block for canonical pattern `(0, 1, 2, 4, 6, 6)`. -/
def targetTop_0457 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 0;
     0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0457 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_0457 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0457 : BottomDetBound targetTop_0457 9 := by
  have hU : rowTransform_0457.det.natAbs = 1 := by
    have hdet : rowTransform_0457.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Aggregate.bottomBound.transformTopRows rowTransform_0457 hU
  have hcols := hrows.permuteColumns columnPerm_0457
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0457 MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Base.explicitTop)
          columnPerm_0457 = targetTop_0457 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0457 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 4 6 6)) 9 := by
  have htop : targetTop_0457 =
      topOfPattern (R := ℤ) (angle6 0 1 2 4 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0457

/-- Explicit target top block for canonical pattern `(0, 1, 2, 4, 6, 7)`. -/
def targetTop_0458 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 1;
     0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0458 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_0458 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 3, 5]
  invFun := ![0, 2, 3, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0458 : BottomDetBound targetTop_0458 9 := by
  have hU : rowTransform_0458.det.natAbs = 1 := by
    have hdet : rowTransform_0458.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R018.Aggregate.bottomBound.transformTopRows rowTransform_0458 hU
  have hcols := hrows.permuteColumns columnPerm_0458
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0458 MainTheory.Generated.BinaryBetaSixKernel.Representative.R018.Base.explicitTop)
          columnPerm_0458 = targetTop_0458 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0458 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 4 6 7)) 9 := by
  have htop : targetTop_0458 =
      topOfPattern (R := ℤ) (angle6 0 1 2 4 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0458

/-- Explicit target top block for canonical pattern `(0, 1, 2, 4, 7, 7)`. -/
def targetTop_0459 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 1, 1;
     0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0459 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0459 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0459 : BottomDetBound targetTop_0459 9 := by
  have hU : rowTransform_0459.det.natAbs = 1 := by
    have hdet : rowTransform_0459.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R020.Aggregate.bottomBound.transformTopRows rowTransform_0459 hU
  have hcols := hrows.permuteColumns columnPerm_0459
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0459 MainTheory.Generated.BinaryBetaSixKernel.Representative.R020.Base.explicitTop)
          columnPerm_0459 = targetTop_0459 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0459 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 4 7 7)) 9 := by
  have htop : targetTop_0459 =
      topOfPattern (R := ℤ) (angle6 0 1 2 4 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0459

/-- Explicit target top block for canonical pattern `(0, 1, 2, 5, 5, 5)`. -/
def targetTop_0460 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 1, 1;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0460 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_0460 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0460 : BottomDetBound targetTop_0460 9 := by
  have hU : rowTransform_0460.det.natAbs = 1 := by
    have hdet : rowTransform_0460.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0460 hU
  have hcols := hrows.permuteColumns columnPerm_0460
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0460 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0460 = targetTop_0460 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0460 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 5 5 5)) 9 := by
  have htop : targetTop_0460 =
      topOfPattern (R := ℤ) (angle6 0 1 2 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0460

/-- Explicit target top block for canonical pattern `(0, 1, 2, 5, 5, 6)`. -/
def targetTop_0461 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 1, 0;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0461 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, (-1);
     0, 0, 1;
     1, 0, 0]

def columnPerm_0461 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 5, 1, 2, 4]
  invFun := ![0, 3, 4, 1, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0461 : BottomDetBound targetTop_0461 9 := by
  have hU : rowTransform_0461.det.natAbs = 1 := by
    have hdet : rowTransform_0461.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Aggregate.bottomBound.transformTopRows rowTransform_0461 hU
  have hcols := hrows.permuteColumns columnPerm_0461
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0461 MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Base.explicitTop)
          columnPerm_0461 = targetTop_0461 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0461 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 5 5 6)) 9 := by
  have htop : targetTop_0461 =
      topOfPattern (R := ℤ) (angle6 0 1 2 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0461

/-- Explicit target top block for canonical pattern `(0, 1, 2, 5, 5, 7)`. -/
def targetTop_0462 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 1, 1;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0462 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 0;
     1, 0, 0]

def columnPerm_0462 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 3, 1, 2, 4]
  invFun := ![0, 3, 4, 2, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0462 : BottomDetBound targetTop_0462 9 := by
  have hU : rowTransform_0462.det.natAbs = 1 := by
    have hdet : rowTransform_0462.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0462 hU
  have hcols := hrows.permuteColumns columnPerm_0462
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0462 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0462 = targetTop_0462 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0462 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 5 5 7)) 9 := by
  have htop : targetTop_0462 =
      topOfPattern (R := ℤ) (angle6 0 1 2 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0462

/-- Explicit target top block for canonical pattern `(0, 1, 2, 5, 6, 6)`. -/
def targetTop_0463 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 0, 0;
     0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0463 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, (-1);
     1, 0, 0]

def columnPerm_0463 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 3, 4, 1, 2]
  invFun := ![0, 4, 5, 2, 3, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0463 : BottomDetBound targetTop_0463 9 := by
  have hU : rowTransform_0463.det.natAbs = 1 := by
    have hdet : rowTransform_0463.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Aggregate.bottomBound.transformTopRows rowTransform_0463 hU
  have hcols := hrows.permuteColumns columnPerm_0463
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0463 MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Base.explicitTop)
          columnPerm_0463 = targetTop_0463 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0463 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 5 6 6)) 9 := by
  have htop : targetTop_0463 =
      topOfPattern (R := ℤ) (angle6 0 1 2 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0463

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard028
