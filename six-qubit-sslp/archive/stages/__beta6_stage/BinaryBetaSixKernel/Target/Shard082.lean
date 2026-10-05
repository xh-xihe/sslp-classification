-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R051.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard082

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(2, 2, 3, 3, 3, 5)`. -/
def targetTop_1312 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1312 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 1, 0;
     0, 0, 1]

def columnPerm_1312 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1312 : BottomDetBound targetTop_1312 9 := by
  have hU : rowTransform_1312.det.natAbs = 1 := by
    have hdet : rowTransform_1312.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1312 hU
  have hcols := hrows.permuteColumns columnPerm_1312
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1312 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1312 = targetTop_1312 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1312 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 3 3 5)) 9 := by
  have htop : targetTop_1312 =
      topOfPattern (R := ℤ) (angle6 2 2 3 3 3 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1312

/-- Explicit target top block for canonical pattern `(2, 2, 3, 3, 3, 6)`. -/
def targetTop_1313 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 0;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1313 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, 1;
     0, 0, 1]

def columnPerm_1313 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1313 : BottomDetBound targetTop_1313 9 := by
  have hU : rowTransform_1313.det.natAbs = 1 := by
    have hdet : rowTransform_1313.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1313 hU
  have hcols := hrows.permuteColumns columnPerm_1313
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1313 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1313 = targetTop_1313 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1313 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 3 3 6)) 9 := by
  have htop : targetTop_1313 =
      topOfPattern (R := ℤ) (angle6 2 2 3 3 3 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1313

/-- Explicit target top block for canonical pattern `(2, 2, 3, 3, 3, 7)`. -/
def targetTop_1314 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1314 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 1, 1;
     0, 0, 1]

def columnPerm_1314 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1314 : BottomDetBound targetTop_1314 9 := by
  have hU : rowTransform_1314.det.natAbs = 1 := by
    have hdet : rowTransform_1314.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1314 hU
  have hcols := hrows.permuteColumns columnPerm_1314
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1314 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1314 = targetTop_1314 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1314 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 3 3 7)) 9 := by
  have htop : targetTop_1314 =
      topOfPattern (R := ℤ) (angle6 2 2 3 3 3 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1314

/-- Explicit target top block for canonical pattern `(2, 2, 3, 3, 4, 4)`. -/
def targetTop_1315 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 0;
     1, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1315 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 0;
     0, 0, 1]

def columnPerm_1315 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1315 : BottomDetBound targetTop_1315 9 := by
  have hU : rowTransform_1315.det.natAbs = 1 := by
    have hdet : rowTransform_1315.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate.bottomBound.transformTopRows rowTransform_1315 hU
  have hcols := hrows.permuteColumns columnPerm_1315
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1315 MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Base.explicitTop)
          columnPerm_1315 = targetTop_1315 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1315 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 3 4 4)) 9 := by
  have htop : targetTop_1315 =
      topOfPattern (R := ℤ) (angle6 2 2 3 3 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1315

/-- Explicit target top block for canonical pattern `(2, 2, 3, 3, 4, 5)`. -/
def targetTop_1316 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 1;
     1, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1316 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, (-1);
     0, 0, 1]

def columnPerm_1316 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1316 : BottomDetBound targetTop_1316 9 := by
  have hU : rowTransform_1316.det.natAbs = 1 := by
    have hdet : rowTransform_1316.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate.bottomBound.transformTopRows rowTransform_1316 hU
  have hcols := hrows.permuteColumns columnPerm_1316
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1316 MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Base.explicitTop)
          columnPerm_1316 = targetTop_1316 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1316 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 3 4 5)) 9 := by
  have htop : targetTop_1316 =
      topOfPattern (R := ℤ) (angle6 2 2 3 3 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1316

/-- Explicit target top block for canonical pattern `(2, 2, 3, 3, 4, 6)`. -/
def targetTop_1317 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 0;
     1, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1317 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 0;
     0, 0, 1]

def columnPerm_1317 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1317 : BottomDetBound targetTop_1317 9 := by
  have hU : rowTransform_1317.det.natAbs = 1 := by
    have hdet : rowTransform_1317.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_1317 hU
  have hcols := hrows.permuteColumns columnPerm_1317
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1317 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_1317 = targetTop_1317 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1317 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 3 4 6)) 9 := by
  have htop : targetTop_1317 =
      topOfPattern (R := ℤ) (angle6 2 2 3 3 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1317

/-- Explicit target top block for canonical pattern `(2, 2, 3, 3, 4, 7)`. -/
def targetTop_1318 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 1;
     1, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1318 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, 0;
     0, 0, 1]

def columnPerm_1318 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 0, 1, 4, 5]
  invFun := ![2, 3, 0, 1, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1318 : BottomDetBound targetTop_1318 9 := by
  have hU : rowTransform_1318.det.natAbs = 1 := by
    have hdet : rowTransform_1318.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_1318 hU
  have hcols := hrows.permuteColumns columnPerm_1318
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1318 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_1318 = targetTop_1318 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1318 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 3 4 7)) 9 := by
  have htop : targetTop_1318 =
      topOfPattern (R := ℤ) (angle6 2 2 3 3 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1318

/-- Explicit target top block for canonical pattern `(2, 2, 3, 3, 5, 5)`. -/
def targetTop_1319 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     1, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1319 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 1, 0;
     0, 0, 1]

def columnPerm_1319 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1319 : BottomDetBound targetTop_1319 9 := by
  have hU : rowTransform_1319.det.natAbs = 1 := by
    have hdet : rowTransform_1319.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate.bottomBound.transformTopRows rowTransform_1319 hU
  have hcols := hrows.permuteColumns columnPerm_1319
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1319 MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Base.explicitTop)
          columnPerm_1319 = targetTop_1319 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1319 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 3 5 5)) 9 := by
  have htop : targetTop_1319 =
      topOfPattern (R := ℤ) (angle6 2 2 3 3 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1319

/-- Explicit target top block for canonical pattern `(2, 2, 3, 3, 5, 6)`. -/
def targetTop_1320 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 0;
     1, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1320 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1320 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 5, 4]
  invFun := ![0, 1, 2, 3, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1320 : BottomDetBound targetTop_1320 9 := by
  have hU : rowTransform_1320.det.natAbs = 1 := by
    have hdet : rowTransform_1320.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R051.Aggregate.bottomBound.transformTopRows rowTransform_1320 hU
  have hcols := hrows.permuteColumns columnPerm_1320
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1320 MainTheory.Generated.BinaryBetaSixKernel.Representative.R051.Base.explicitTop)
          columnPerm_1320 = targetTop_1320 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1320 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 3 5 6)) 9 := by
  have htop : targetTop_1320 =
      topOfPattern (R := ℤ) (angle6 2 2 3 3 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1320

/-- Explicit target top block for canonical pattern `(2, 2, 3, 3, 5, 7)`. -/
def targetTop_1321 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     1, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1321 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 1, 0;
     0, 0, 1]

def columnPerm_1321 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1321 : BottomDetBound targetTop_1321 9 := by
  have hU : rowTransform_1321.det.natAbs = 1 := by
    have hdet : rowTransform_1321.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_1321 hU
  have hcols := hrows.permuteColumns columnPerm_1321
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1321 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_1321 = targetTop_1321 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1321 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 3 5 7)) 9 := by
  have htop : targetTop_1321 =
      topOfPattern (R := ℤ) (angle6 2 2 3 3 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1321

/-- Explicit target top block for canonical pattern `(2, 2, 3, 3, 6, 6)`. -/
def targetTop_1322 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 0;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1322 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 1;
     0, 0, 1]

def columnPerm_1322 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1322 : BottomDetBound targetTop_1322 9 := by
  have hU : rowTransform_1322.det.natAbs = 1 := by
    have hdet : rowTransform_1322.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate.bottomBound.transformTopRows rowTransform_1322 hU
  have hcols := hrows.permuteColumns columnPerm_1322
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1322 MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Base.explicitTop)
          columnPerm_1322 = targetTop_1322 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1322 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 3 6 6)) 9 := by
  have htop : targetTop_1322 =
      topOfPattern (R := ℤ) (angle6 2 2 3 3 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1322

/-- Explicit target top block for canonical pattern `(2, 2, 3, 3, 6, 7)`. -/
def targetTop_1323 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1323 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 0;
     0, 0, 1]

def columnPerm_1323 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1323 : BottomDetBound targetTop_1323 9 := by
  have hU : rowTransform_1323.det.natAbs = 1 := by
    have hdet : rowTransform_1323.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate.bottomBound.transformTopRows rowTransform_1323 hU
  have hcols := hrows.permuteColumns columnPerm_1323
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1323 MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Base.explicitTop)
          columnPerm_1323 = targetTop_1323 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1323 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 3 6 7)) 9 := by
  have htop : targetTop_1323 =
      topOfPattern (R := ℤ) (angle6 2 2 3 3 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1323

/-- Explicit target top block for canonical pattern `(2, 2, 3, 3, 7, 7)`. -/
def targetTop_1324 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1324 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 1, 1;
     0, 0, 1]

def columnPerm_1324 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1324 : BottomDetBound targetTop_1324 9 := by
  have hU : rowTransform_1324.det.natAbs = 1 := by
    have hdet : rowTransform_1324.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate.bottomBound.transformTopRows rowTransform_1324 hU
  have hcols := hrows.permuteColumns columnPerm_1324
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1324 MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Base.explicitTop)
          columnPerm_1324 = targetTop_1324 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1324 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 3 7 7)) 9 := by
  have htop : targetTop_1324 =
      topOfPattern (R := ℤ) (angle6 2 2 3 3 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1324

/-- Explicit target top block for canonical pattern `(2, 2, 3, 4, 4, 4)`. -/
def targetTop_1325 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 0;
     1, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1325 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 1;
     1, 0, 0]

def columnPerm_1325 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1325 : BottomDetBound targetTop_1325 9 := by
  have hU : rowTransform_1325.det.natAbs = 1 := by
    have hdet : rowTransform_1325.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1325 hU
  have hcols := hrows.permuteColumns columnPerm_1325
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1325 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1325 = targetTop_1325 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1325 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 4 4 4)) 9 := by
  have htop : targetTop_1325 =
      topOfPattern (R := ℤ) (angle6 2 2 3 4 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1325

/-- Explicit target top block for canonical pattern `(2, 2, 3, 4, 4, 5)`. -/
def targetTop_1326 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 1;
     1, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1326 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1326 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1326 : BottomDetBound targetTop_1326 9 := by
  have hU : rowTransform_1326.det.natAbs = 1 := by
    have hdet : rowTransform_1326.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate.bottomBound.transformTopRows rowTransform_1326 hU
  have hcols := hrows.permuteColumns columnPerm_1326
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1326 MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Base.explicitTop)
          columnPerm_1326 = targetTop_1326 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1326 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 4 4 5)) 9 := by
  have htop : targetTop_1326 =
      topOfPattern (R := ℤ) (angle6 2 2 3 4 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1326

/-- Explicit target top block for canonical pattern `(2, 2, 3, 4, 4, 6)`. -/
def targetTop_1327 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 0;
     1, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1327 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 1;
     0, 1, 0]

def columnPerm_1327 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1327 : BottomDetBound targetTop_1327 9 := by
  have hU : rowTransform_1327.det.natAbs = 1 := by
    have hdet : rowTransform_1327.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate.bottomBound.transformTopRows rowTransform_1327 hU
  have hcols := hrows.permuteColumns columnPerm_1327
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1327 MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Base.explicitTop)
          columnPerm_1327 = targetTop_1327 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1327 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 4 4 6)) 9 := by
  have htop : targetTop_1327 =
      topOfPattern (R := ℤ) (angle6 2 2 3 4 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1327

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard082
