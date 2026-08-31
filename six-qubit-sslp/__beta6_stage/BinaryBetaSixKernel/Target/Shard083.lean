-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R045.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R049.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R050.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R051.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R052.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R053.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard083

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(2, 2, 3, 4, 4, 7)`. -/
def targetTop_1328 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 1;
     1, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1328 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 1;
     1, 0, 0]

def columnPerm_1328 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 4, 0, 1, 5]
  invFun := ![3, 4, 0, 1, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1328 : BottomDetBound targetTop_1328 9 := by
  have hU : rowTransform_1328.det.natAbs = 1 := by
    have hdet : rowTransform_1328.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_1328 hU
  have hcols := hrows.permuteColumns columnPerm_1328
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1328 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_1328 = targetTop_1328 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1328 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 4 4 7)) 9 := by
  have htop : targetTop_1328 =
      topOfPattern (R := ℤ) (angle6 2 2 3 4 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1328

/-- Explicit target top block for canonical pattern `(2, 2, 3, 4, 5, 5)`. -/
def targetTop_1329 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 1, 1;
     1, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1329 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, (-1);
     0, 0, 1]

def columnPerm_1329 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1329 : BottomDetBound targetTop_1329 9 := by
  have hU : rowTransform_1329.det.natAbs = 1 := by
    have hdet : rowTransform_1329.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R049.Aggregate.bottomBound.transformTopRows rowTransform_1329 hU
  have hcols := hrows.permuteColumns columnPerm_1329
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1329 MainTheory.Generated.BinaryBetaSixKernel.Representative.R049.Base.explicitTop)
          columnPerm_1329 = targetTop_1329 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1329 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 4 5 5)) 9 := by
  have htop : targetTop_1329 =
      topOfPattern (R := ℤ) (angle6 2 2 3 4 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1329

/-- Explicit target top block for canonical pattern `(2, 2, 3, 4, 5, 6)`. -/
def targetTop_1330 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 1, 0;
     1, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1330 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1330 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 5, 3]
  invFun := ![0, 1, 3, 5, 2, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1330 : BottomDetBound targetTop_1330 9 := by
  have hU : rowTransform_1330.det.natAbs = 1 := by
    have hdet : rowTransform_1330.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R045.Aggregate.bottomBound.transformTopRows rowTransform_1330 hU
  have hcols := hrows.permuteColumns columnPerm_1330
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1330 MainTheory.Generated.BinaryBetaSixKernel.Representative.R045.Base.explicitTop)
          columnPerm_1330 = targetTop_1330 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1330 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 4 5 6)) 9 := by
  have htop : targetTop_1330 =
      topOfPattern (R := ℤ) (angle6 2 2 3 4 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1330

/-- Explicit target top block for canonical pattern `(2, 2, 3, 4, 5, 7)`. -/
def targetTop_1331 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 1, 1;
     1, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1331 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, (-1);
     0, 0, 1]

def columnPerm_1331 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1331 : BottomDetBound targetTop_1331 9 := by
  have hU : rowTransform_1331.det.natAbs = 1 := by
    have hdet : rowTransform_1331.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R050.Aggregate.bottomBound.transformTopRows rowTransform_1331 hU
  have hcols := hrows.permuteColumns columnPerm_1331
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1331 MainTheory.Generated.BinaryBetaSixKernel.Representative.R050.Base.explicitTop)
          columnPerm_1331 = targetTop_1331 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1331 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 4 5 7)) 9 := by
  have htop : targetTop_1331 =
      topOfPattern (R := ℤ) (angle6 2 2 3 4 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1331

/-- Explicit target top block for canonical pattern `(2, 2, 3, 4, 6, 6)`. -/
def targetTop_1332 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 0;
     1, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1332 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 1;
     0, 1, 0]

def columnPerm_1332 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1332 : BottomDetBound targetTop_1332 9 := by
  have hU : rowTransform_1332.det.natAbs = 1 := by
    have hdet : rowTransform_1332.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_1332 hU
  have hcols := hrows.permuteColumns columnPerm_1332
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1332 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_1332 = targetTop_1332 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1332 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 4 6 6)) 9 := by
  have htop : targetTop_1332 =
      topOfPattern (R := ℤ) (angle6 2 2 3 4 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1332

/-- Explicit target top block for canonical pattern `(2, 2, 3, 4, 6, 7)`. -/
def targetTop_1333 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 1;
     1, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1333 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 1;
     0, 1, 0]

def columnPerm_1333 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1333 : BottomDetBound targetTop_1333 9 := by
  have hU : rowTransform_1333.det.natAbs = 1 := by
    have hdet : rowTransform_1333.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Aggregate.bottomBound.transformTopRows rowTransform_1333 hU
  have hcols := hrows.permuteColumns columnPerm_1333
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1333 MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Base.explicitTop)
          columnPerm_1333 = targetTop_1333 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1333 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 4 6 7)) 9 := by
  have htop : targetTop_1333 =
      topOfPattern (R := ℤ) (angle6 2 2 3 4 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1333

/-- Explicit target top block for canonical pattern `(2, 2, 3, 4, 7, 7)`. -/
def targetTop_1334 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 1, 1;
     1, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1334 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 0;
     0, 0, 1]

def columnPerm_1334 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1334 : BottomDetBound targetTop_1334 9 := by
  have hU : rowTransform_1334.det.natAbs = 1 := by
    have hdet : rowTransform_1334.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate.bottomBound.transformTopRows rowTransform_1334 hU
  have hcols := hrows.permuteColumns columnPerm_1334
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1334 MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Base.explicitTop)
          columnPerm_1334 = targetTop_1334 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1334 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 4 7 7)) 9 := by
  have htop : targetTop_1334 =
      topOfPattern (R := ℤ) (angle6 2 2 3 4 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1334

/-- Explicit target top block for canonical pattern `(2, 2, 3, 5, 5, 5)`. -/
def targetTop_1335 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     1, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1335 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 1;
     1, 0, 0]

def columnPerm_1335 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1335 : BottomDetBound targetTop_1335 9 := by
  have hU : rowTransform_1335.det.natAbs = 1 := by
    have hdet : rowTransform_1335.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1335 hU
  have hcols := hrows.permuteColumns columnPerm_1335
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1335 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1335 = targetTop_1335 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1335 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 5 5 5)) 9 := by
  have htop : targetTop_1335 =
      topOfPattern (R := ℤ) (angle6 2 2 3 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1335

/-- Explicit target top block for canonical pattern `(2, 2, 3, 5, 5, 6)`. -/
def targetTop_1336 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 0;
     1, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1336 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1336 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 4, 5, 3]
  invFun := ![0, 1, 2, 5, 3, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1336 : BottomDetBound targetTop_1336 9 := by
  have hU : rowTransform_1336.det.natAbs = 1 := by
    have hdet : rowTransform_1336.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R052.Aggregate.bottomBound.transformTopRows rowTransform_1336 hU
  have hcols := hrows.permuteColumns columnPerm_1336
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1336 MainTheory.Generated.BinaryBetaSixKernel.Representative.R052.Base.explicitTop)
          columnPerm_1336 = targetTop_1336 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1336 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 5 5 6)) 9 := by
  have htop : targetTop_1336 =
      topOfPattern (R := ℤ) (angle6 2 2 3 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1336

/-- Explicit target top block for canonical pattern `(2, 2, 3, 5, 5, 7)`. -/
def targetTop_1337 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     1, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1337 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 1;
     0, 1, 0]

def columnPerm_1337 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1337 : BottomDetBound targetTop_1337 9 := by
  have hU : rowTransform_1337.det.natAbs = 1 := by
    have hdet : rowTransform_1337.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate.bottomBound.transformTopRows rowTransform_1337 hU
  have hcols := hrows.permuteColumns columnPerm_1337
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1337 MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Base.explicitTop)
          columnPerm_1337 = targetTop_1337 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1337 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 5 5 7)) 9 := by
  have htop : targetTop_1337 =
      topOfPattern (R := ℤ) (angle6 2 2 3 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1337

/-- Explicit target top block for canonical pattern `(2, 2, 3, 5, 6, 6)`. -/
def targetTop_1338 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 0;
     1, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1338 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1338 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1338 : BottomDetBound targetTop_1338 9 := by
  have hU : rowTransform_1338.det.natAbs = 1 := by
    have hdet : rowTransform_1338.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R051.Aggregate.bottomBound.transformTopRows rowTransform_1338 hU
  have hcols := hrows.permuteColumns columnPerm_1338
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1338 MainTheory.Generated.BinaryBetaSixKernel.Representative.R051.Base.explicitTop)
          columnPerm_1338 = targetTop_1338 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1338 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 5 6 6)) 9 := by
  have htop : targetTop_1338 =
      topOfPattern (R := ℤ) (angle6 2 2 3 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1338

/-- Explicit target top block for canonical pattern `(2, 2, 3, 5, 6, 7)`. -/
def targetTop_1339 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 1;
     1, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1339 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1339 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 4, 3, 5]
  invFun := ![0, 1, 2, 4, 3, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1339 : BottomDetBound targetTop_1339 9 := by
  have hU : rowTransform_1339.det.natAbs = 1 := by
    have hdet : rowTransform_1339.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R053.Aggregate.bottomBound.transformTopRows rowTransform_1339 hU
  have hcols := hrows.permuteColumns columnPerm_1339
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1339 MainTheory.Generated.BinaryBetaSixKernel.Representative.R053.Base.explicitTop)
          columnPerm_1339 = targetTop_1339 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1339 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 5 6 7)) 9 := by
  have htop : targetTop_1339 =
      topOfPattern (R := ℤ) (angle6 2 2 3 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1339

/-- Explicit target top block for canonical pattern `(2, 2, 3, 5, 7, 7)`. -/
def targetTop_1340 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     1, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1340 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 1;
     0, 1, 0]

def columnPerm_1340 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1340 : BottomDetBound targetTop_1340 9 := by
  have hU : rowTransform_1340.det.natAbs = 1 := by
    have hdet : rowTransform_1340.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_1340 hU
  have hcols := hrows.permuteColumns columnPerm_1340
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1340 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_1340 = targetTop_1340 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1340 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 5 7 7)) 9 := by
  have htop : targetTop_1340 =
      topOfPattern (R := ℤ) (angle6 2 2 3 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1340

/-- Explicit target top block for canonical pattern `(2, 2, 3, 6, 6, 6)`. -/
def targetTop_1341 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 0;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1341 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, 1;
     1, 0, 0]

def columnPerm_1341 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1341 : BottomDetBound targetTop_1341 9 := by
  have hU : rowTransform_1341.det.natAbs = 1 := by
    have hdet : rowTransform_1341.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1341 hU
  have hcols := hrows.permuteColumns columnPerm_1341
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1341 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1341 = targetTop_1341 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1341 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 6 6 6)) 9 := by
  have htop : targetTop_1341 =
      topOfPattern (R := ℤ) (angle6 2 2 3 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1341

/-- Explicit target top block for canonical pattern `(2, 2, 3, 6, 6, 7)`. -/
def targetTop_1342 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1342 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, 0;
     0, 1, 0]

def columnPerm_1342 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1342 : BottomDetBound targetTop_1342 9 := by
  have hU : rowTransform_1342.det.natAbs = 1 := by
    have hdet : rowTransform_1342.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate.bottomBound.transformTopRows rowTransform_1342 hU
  have hcols := hrows.permuteColumns columnPerm_1342
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1342 MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Base.explicitTop)
          columnPerm_1342 = targetTop_1342 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1342 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 6 6 7)) 9 := by
  have htop : targetTop_1342 =
      topOfPattern (R := ℤ) (angle6 2 2 3 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1342

/-- Explicit target top block for canonical pattern `(2, 2, 3, 6, 7, 7)`. -/
def targetTop_1343 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1343 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 0;
     0, 0, 1]

def columnPerm_1343 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1343 : BottomDetBound targetTop_1343 9 := by
  have hU : rowTransform_1343.det.natAbs = 1 := by
    have hdet : rowTransform_1343.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R049.Aggregate.bottomBound.transformTopRows rowTransform_1343 hU
  have hcols := hrows.permuteColumns columnPerm_1343
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1343 MainTheory.Generated.BinaryBetaSixKernel.Representative.R049.Base.explicitTop)
          columnPerm_1343 = targetTop_1343 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1343 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 6 7 7)) 9 := by
  have htop : targetTop_1343 =
      topOfPattern (R := ℤ) (angle6 2 2 3 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1343

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard083
