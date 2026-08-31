-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R013.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard023

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(0, 1, 1, 2, 3, 7)`. -/
def targetTop_0368 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0368 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0368 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0368 : BottomDetBound targetTop_0368 9 := by
  have hU : rowTransform_0368.det.natAbs = 1 := by
    have hdet : rowTransform_0368.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0368 hU
  have hcols := hrows.permuteColumns columnPerm_0368
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0368 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0368 = targetTop_0368 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0368 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 2 3 7)) 9 := by
  have htop : targetTop_0368 =
      topOfPattern (R := ℤ) (angle6 0 1 1 2 3 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0368

/-- Explicit target top block for canonical pattern `(0, 1, 1, 2, 4, 4)`. -/
def targetTop_0369 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0369 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_0369 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0369 : BottomDetBound targetTop_0369 9 := by
  have hU : rowTransform_0369.det.natAbs = 1 := by
    have hdet : rowTransform_0369.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0369 hU
  have hcols := hrows.permuteColumns columnPerm_0369
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0369 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0369 = targetTop_0369 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0369 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 2 4 4)) 9 := by
  have htop : targetTop_0369 =
      topOfPattern (R := ℤ) (angle6 0 1 1 2 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0369

/-- Explicit target top block for canonical pattern `(0, 1, 1, 2, 4, 5)`. -/
def targetTop_0370 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0370 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_0370 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0370 : BottomDetBound targetTop_0370 9 := by
  have hU : rowTransform_0370.det.natAbs = 1 := by
    have hdet : rowTransform_0370.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0370 hU
  have hcols := hrows.permuteColumns columnPerm_0370
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0370 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0370 = targetTop_0370 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0370 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 2 4 5)) 9 := by
  have htop : targetTop_0370 =
      topOfPattern (R := ℤ) (angle6 0 1 1 2 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0370

/-- Explicit target top block for canonical pattern `(0, 1, 1, 2, 4, 6)`. -/
def targetTop_0371 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0371 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0371 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0371 : BottomDetBound targetTop_0371 9 := by
  have hU : rowTransform_0371.det.natAbs = 1 := by
    have hdet : rowTransform_0371.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate.bottomBound.transformTopRows rowTransform_0371 hU
  have hcols := hrows.permuteColumns columnPerm_0371
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0371 MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Base.explicitTop)
          columnPerm_0371 = targetTop_0371 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0371 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 2 4 6)) 9 := by
  have htop : targetTop_0371 =
      topOfPattern (R := ℤ) (angle6 0 1 1 2 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0371

/-- Explicit target top block for canonical pattern `(0, 1, 1, 2, 4, 7)`. -/
def targetTop_0372 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0372 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0372 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0372 : BottomDetBound targetTop_0372 9 := by
  have hU : rowTransform_0372.det.natAbs = 1 := by
    have hdet : rowTransform_0372.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R013.Aggregate.bottomBound.transformTopRows rowTransform_0372 hU
  have hcols := hrows.permuteColumns columnPerm_0372
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0372 MainTheory.Generated.BinaryBetaSixKernel.Representative.R013.Base.explicitTop)
          columnPerm_0372 = targetTop_0372 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0372 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 2 4 7)) 9 := by
  have htop : targetTop_0372 =
      topOfPattern (R := ℤ) (angle6 0 1 1 2 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0372

/-- Explicit target top block for canonical pattern `(0, 1, 1, 2, 5, 5)`. -/
def targetTop_0373 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0373 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_0373 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0373 : BottomDetBound targetTop_0373 9 := by
  have hU : rowTransform_0373.det.natAbs = 1 := by
    have hdet : rowTransform_0373.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0373 hU
  have hcols := hrows.permuteColumns columnPerm_0373
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0373 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0373 = targetTop_0373 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0373 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 2 5 5)) 9 := by
  have htop : targetTop_0373 =
      topOfPattern (R := ℤ) (angle6 0 1 1 2 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0373

/-- Explicit target top block for canonical pattern `(0, 1, 1, 2, 5, 6)`. -/
def targetTop_0374 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 1, 0;
     0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0374 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0374 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0374 : BottomDetBound targetTop_0374 9 := by
  have hU : rowTransform_0374.det.natAbs = 1 := by
    have hdet : rowTransform_0374.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Aggregate.bottomBound.transformTopRows rowTransform_0374 hU
  have hcols := hrows.permuteColumns columnPerm_0374
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0374 MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Base.explicitTop)
          columnPerm_0374 = targetTop_0374 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0374 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 2 5 6)) 9 := by
  have htop : targetTop_0374 =
      topOfPattern (R := ℤ) (angle6 0 1 1 2 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0374

/-- Explicit target top block for canonical pattern `(0, 1, 1, 2, 5, 7)`. -/
def targetTop_0375 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0375 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0375 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0375 : BottomDetBound targetTop_0375 9 := by
  have hU : rowTransform_0375.det.natAbs = 1 := by
    have hdet : rowTransform_0375.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate.bottomBound.transformTopRows rowTransform_0375 hU
  have hcols := hrows.permuteColumns columnPerm_0375
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0375 MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Base.explicitTop)
          columnPerm_0375 = targetTop_0375 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0375 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 2 5 7)) 9 := by
  have htop : targetTop_0375 =
      topOfPattern (R := ℤ) (angle6 0 1 1 2 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0375

/-- Explicit target top block for canonical pattern `(0, 1, 1, 2, 6, 6)`. -/
def targetTop_0376 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0376 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     0, 1, 0]

def columnPerm_0376 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0376 : BottomDetBound targetTop_0376 9 := by
  have hU : rowTransform_0376.det.natAbs = 1 := by
    have hdet : rowTransform_0376.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0376 hU
  have hcols := hrows.permuteColumns columnPerm_0376
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0376 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0376 = targetTop_0376 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0376 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 2 6 6)) 9 := by
  have htop : targetTop_0376 =
      topOfPattern (R := ℤ) (angle6 0 1 1 2 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0376

/-- Explicit target top block for canonical pattern `(0, 1, 1, 2, 6, 7)`. -/
def targetTop_0377 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0377 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     0, 1, 0]

def columnPerm_0377 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0377 : BottomDetBound targetTop_0377 9 := by
  have hU : rowTransform_0377.det.natAbs = 1 := by
    have hdet : rowTransform_0377.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0377 hU
  have hcols := hrows.permuteColumns columnPerm_0377
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0377 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0377 = targetTop_0377 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0377 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 2 6 7)) 9 := by
  have htop : targetTop_0377 =
      topOfPattern (R := ℤ) (angle6 0 1 1 2 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0377

/-- Explicit target top block for canonical pattern `(0, 1, 1, 2, 7, 7)`. -/
def targetTop_0378 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0378 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 1;
     0, 1, 0]

def columnPerm_0378 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0378 : BottomDetBound targetTop_0378 9 := by
  have hU : rowTransform_0378.det.natAbs = 1 := by
    have hdet : rowTransform_0378.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0378 hU
  have hcols := hrows.permuteColumns columnPerm_0378
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0378 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0378 = targetTop_0378 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0378 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 2 7 7)) 9 := by
  have htop : targetTop_0378 =
      topOfPattern (R := ℤ) (angle6 0 1 1 2 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0378

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 1, 3, 3, 3)`. -/
def targetTop_0379 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0379 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0379 :
    TopRowRelation targetTop_0379 relationCoefficients_0379 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0379, relationCoefficients_0379, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0379 : BottomDetBound targetTop_0379 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0379

theorem canonicalBound_0379 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 3 3 3)) 9 := by
  have htop : targetTop_0379 =
      topOfPattern (R := ℤ) (angle6 0 1 1 3 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0379

/-- Explicit target top block for canonical pattern `(0, 1, 1, 3, 3, 4)`. -/
def targetTop_0380 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 0;
     0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0380 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0380 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0380 : BottomDetBound targetTop_0380 9 := by
  have hU : rowTransform_0380.det.natAbs = 1 := by
    have hdet : rowTransform_0380.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0380 hU
  have hcols := hrows.permuteColumns columnPerm_0380
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0380 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0380 = targetTop_0380 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0380 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 3 3 4)) 9 := by
  have htop : targetTop_0380 =
      topOfPattern (R := ℤ) (angle6 0 1 1 3 3 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0380

/-- Explicit target top block for canonical pattern `(0, 1, 1, 3, 3, 5)`. -/
def targetTop_0381 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0381 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0381 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0381 : BottomDetBound targetTop_0381 9 := by
  have hU : rowTransform_0381.det.natAbs = 1 := by
    have hdet : rowTransform_0381.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0381 hU
  have hcols := hrows.permuteColumns columnPerm_0381
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0381 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0381 = targetTop_0381 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0381 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 3 3 5)) 9 := by
  have htop : targetTop_0381 =
      topOfPattern (R := ℤ) (angle6 0 1 1 3 3 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0381

/-- Explicit target top block for canonical pattern `(0, 1, 1, 3, 3, 6)`. -/
def targetTop_0382 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 0;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0382 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0382 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0382 : BottomDetBound targetTop_0382 9 := by
  have hU : rowTransform_0382.det.natAbs = 1 := by
    have hdet : rowTransform_0382.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0382 hU
  have hcols := hrows.permuteColumns columnPerm_0382
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0382 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0382 = targetTop_0382 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0382 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 3 3 6)) 9 := by
  have htop : targetTop_0382 =
      topOfPattern (R := ℤ) (angle6 0 1 1 3 3 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0382

/-- Explicit target top block for canonical pattern `(0, 1, 1, 3, 3, 7)`. -/
def targetTop_0383 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0383 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0383 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0383 : BottomDetBound targetTop_0383 9 := by
  have hU : rowTransform_0383.det.natAbs = 1 := by
    have hdet : rowTransform_0383.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0383 hU
  have hcols := hrows.permuteColumns columnPerm_0383
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0383 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0383 = targetTop_0383 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0383 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 3 3 7)) 9 := by
  have htop : targetTop_0383 =
      topOfPattern (R := ℤ) (angle6 0 1 1 3 3 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0383

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard023
