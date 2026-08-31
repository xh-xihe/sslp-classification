-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard085

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(2, 2, 4, 5, 7, 7)`. -/
def targetTop_1360 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     1, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1360 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 1, 1]

def columnPerm_1360 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1360 : BottomDetBound targetTop_1360 9 := by
  have hU : rowTransform_1360.det.natAbs = 1 := by
    have hdet : rowTransform_1360.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_1360 hU
  have hcols := hrows.permuteColumns columnPerm_1360
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1360 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_1360 = targetTop_1360 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1360 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 4 5 7 7)) 9 := by
  have htop : targetTop_1360 =
      topOfPattern (R := ℤ) (angle6 2 2 4 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1360

/-- Explicit rank-deficient target for canonical pattern `(2, 2, 4, 6, 6, 6)`. -/
def targetTop_1361 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     1, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1361 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_1361 :
    TopRowRelation targetTop_1361 relationCoefficients_1361 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1361, relationCoefficients_1361, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1361 : BottomDetBound targetTop_1361 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1361

theorem canonicalBound_1361 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 4 6 6 6)) 9 := by
  have htop : targetTop_1361 =
      topOfPattern (R := ℤ) (angle6 2 2 4 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1361

/-- Explicit target top block for canonical pattern `(2, 2, 4, 6, 6, 7)`. -/
def targetTop_1362 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     1, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1362 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 1;
     0, 1, 1]

def columnPerm_1362 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1362 : BottomDetBound targetTop_1362 9 := by
  have hU : rowTransform_1362.det.natAbs = 1 := by
    have hdet : rowTransform_1362.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_1362 hU
  have hcols := hrows.permuteColumns columnPerm_1362
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1362 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_1362 = targetTop_1362 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1362 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 4 6 6 7)) 9 := by
  have htop : targetTop_1362 =
      topOfPattern (R := ℤ) (angle6 2 2 4 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1362

/-- Explicit target top block for canonical pattern `(2, 2, 4, 6, 7, 7)`. -/
def targetTop_1363 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     1, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1363 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 0;
     0, 1, 1]

def columnPerm_1363 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1363 : BottomDetBound targetTop_1363 9 := by
  have hU : rowTransform_1363.det.natAbs = 1 := by
    have hdet : rowTransform_1363.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_1363 hU
  have hcols := hrows.permuteColumns columnPerm_1363
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1363 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_1363 = targetTop_1363 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1363 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 4 6 7 7)) 9 := by
  have htop : targetTop_1363 =
      topOfPattern (R := ℤ) (angle6 2 2 4 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1363

/-- Explicit target top block for canonical pattern `(2, 2, 4, 7, 7, 7)`. -/
def targetTop_1364 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     1, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1364 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, 0;
     1, 0, 1]

def columnPerm_1364 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1364 : BottomDetBound targetTop_1364 9 := by
  have hU : rowTransform_1364.det.natAbs = 1 := by
    have hdet : rowTransform_1364.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1364 hU
  have hcols := hrows.permuteColumns columnPerm_1364
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1364 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1364 = targetTop_1364 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1364 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 4 7 7 7)) 9 := by
  have htop : targetTop_1364 =
      topOfPattern (R := ℤ) (angle6 2 2 4 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1364

/-- Explicit rank-deficient target for canonical pattern `(2, 2, 5, 5, 5, 5)`. -/
def targetTop_1365 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     1, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1365 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_1365 :
    TopRowRelation targetTop_1365 relationCoefficients_1365 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1365, relationCoefficients_1365, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1365 : BottomDetBound targetTop_1365 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1365

theorem canonicalBound_1365 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 5 5 5 5)) 9 := by
  have htop : targetTop_1365 =
      topOfPattern (R := ℤ) (angle6 2 2 5 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1365

/-- Explicit target top block for canonical pattern `(2, 2, 5, 5, 5, 6)`. -/
def targetTop_1366 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 0;
     1, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1366 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     1, 0, 1]

def columnPerm_1366 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1366 : BottomDetBound targetTop_1366 9 := by
  have hU : rowTransform_1366.det.natAbs = 1 := by
    have hdet : rowTransform_1366.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1366 hU
  have hcols := hrows.permuteColumns columnPerm_1366
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1366 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1366 = targetTop_1366 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1366 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 5 5 5 6)) 9 := by
  have htop : targetTop_1366 =
      topOfPattern (R := ℤ) (angle6 2 2 5 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1366

/-- Explicit rank-deficient target for canonical pattern `(2, 2, 5, 5, 5, 7)`. -/
def targetTop_1367 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     1, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1367 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_1367 :
    TopRowRelation targetTop_1367 relationCoefficients_1367 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1367, relationCoefficients_1367, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1367 : BottomDetBound targetTop_1367 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1367

theorem canonicalBound_1367 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 5 5 5 7)) 9 := by
  have htop : targetTop_1367 =
      topOfPattern (R := ℤ) (angle6 2 2 5 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1367

/-- Explicit target top block for canonical pattern `(2, 2, 5, 5, 6, 6)`. -/
def targetTop_1368 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 0;
     1, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1368 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 1;
     0, 1, 1]

def columnPerm_1368 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1368 : BottomDetBound targetTop_1368 9 := by
  have hU : rowTransform_1368.det.natAbs = 1 := by
    have hdet : rowTransform_1368.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate.bottomBound.transformTopRows rowTransform_1368 hU
  have hcols := hrows.permuteColumns columnPerm_1368
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1368 MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Base.explicitTop)
          columnPerm_1368 = targetTop_1368 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1368 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 5 5 6 6)) 9 := by
  have htop : targetTop_1368 =
      topOfPattern (R := ℤ) (angle6 2 2 5 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1368

/-- Explicit target top block for canonical pattern `(2, 2, 5, 5, 6, 7)`. -/
def targetTop_1369 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 1;
     1, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1369 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 1;
     0, 1, 1]

def columnPerm_1369 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 5, 4]
  invFun := ![0, 1, 2, 3, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1369 : BottomDetBound targetTop_1369 9 := by
  have hU : rowTransform_1369.det.natAbs = 1 := by
    have hdet : rowTransform_1369.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate.bottomBound.transformTopRows rowTransform_1369 hU
  have hcols := hrows.permuteColumns columnPerm_1369
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1369 MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Base.explicitTop)
          columnPerm_1369 = targetTop_1369 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1369 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 5 5 6 7)) 9 := by
  have htop : targetTop_1369 =
      topOfPattern (R := ℤ) (angle6 2 2 5 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1369

/-- Explicit rank-deficient target for canonical pattern `(2, 2, 5, 5, 7, 7)`. -/
def targetTop_1370 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     1, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1370 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_1370 :
    TopRowRelation targetTop_1370 relationCoefficients_1370 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1370, relationCoefficients_1370, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1370 : BottomDetBound targetTop_1370 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1370

theorem canonicalBound_1370 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 5 5 7 7)) 9 := by
  have htop : targetTop_1370 =
      topOfPattern (R := ℤ) (angle6 2 2 5 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1370

/-- Explicit target top block for canonical pattern `(2, 2, 5, 6, 6, 6)`. -/
def targetTop_1371 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 0;
     1, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1371 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, 0;
     1, 0, 1]

def columnPerm_1371 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1371 : BottomDetBound targetTop_1371 9 := by
  have hU : rowTransform_1371.det.natAbs = 1 := by
    have hdet : rowTransform_1371.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1371 hU
  have hcols := hrows.permuteColumns columnPerm_1371
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1371 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1371 = targetTop_1371 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1371 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 5 6 6 6)) 9 := by
  have htop : targetTop_1371 =
      topOfPattern (R := ℤ) (angle6 2 2 5 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1371

/-- Explicit target top block for canonical pattern `(2, 2, 5, 6, 6, 7)`. -/
def targetTop_1372 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 1;
     1, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1372 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, 0;
     0, 1, 1]

def columnPerm_1372 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1372 : BottomDetBound targetTop_1372 9 := by
  have hU : rowTransform_1372.det.natAbs = 1 := by
    have hdet : rowTransform_1372.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_1372 hU
  have hcols := hrows.permuteColumns columnPerm_1372
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1372 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_1372 = targetTop_1372 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1372 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 5 6 6 7)) 9 := by
  have htop : targetTop_1372 =
      topOfPattern (R := ℤ) (angle6 2 2 5 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1372

/-- Explicit target top block for canonical pattern `(2, 2, 5, 6, 7, 7)`. -/
def targetTop_1373 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 1, 1;
     1, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1373 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 1;
     0, 1, 1]

def columnPerm_1373 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1373 : BottomDetBound targetTop_1373 9 := by
  have hU : rowTransform_1373.det.natAbs = 1 := by
    have hdet : rowTransform_1373.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_1373 hU
  have hcols := hrows.permuteColumns columnPerm_1373
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1373 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_1373 = targetTop_1373 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1373 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 5 6 7 7)) 9 := by
  have htop : targetTop_1373 =
      topOfPattern (R := ℤ) (angle6 2 2 5 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1373

/-- Explicit rank-deficient target for canonical pattern `(2, 2, 5, 7, 7, 7)`. -/
def targetTop_1374 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     1, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1374 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_1374 :
    TopRowRelation targetTop_1374 relationCoefficients_1374 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1374, relationCoefficients_1374, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1374 : BottomDetBound targetTop_1374 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1374

theorem canonicalBound_1374 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 5 7 7 7)) 9 := by
  have htop : targetTop_1374 =
      topOfPattern (R := ℤ) (angle6 2 2 5 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1374

/-- Explicit rank-deficient target for canonical pattern `(2, 2, 6, 6, 6, 6)`. -/
def targetTop_1375 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     1, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1375 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_1375 :
    TopRowRelation targetTop_1375 relationCoefficients_1375 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1375, relationCoefficients_1375, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1375 : BottomDetBound targetTop_1375 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1375

theorem canonicalBound_1375 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 6 6 6 6)) 9 := by
  have htop : targetTop_1375 =
      topOfPattern (R := ℤ) (angle6 2 2 6 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1375

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard085
