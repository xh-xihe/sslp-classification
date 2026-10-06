-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R042.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard084

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(2, 2, 3, 7, 7, 7)`. -/
def targetTop_1344 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1344 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 1, 1;
     1, 0, 0]

def columnPerm_1344 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1344 : BottomDetBound targetTop_1344 9 := by
  have hU : rowTransform_1344.det.natAbs = 1 := by
    have hdet : rowTransform_1344.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1344 hU
  have hcols := hrows.permuteColumns columnPerm_1344
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1344 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1344 = targetTop_1344 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1344 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 7 7 7)) 9 := by
  have htop : targetTop_1344 =
      topOfPattern (R := ℤ) (angle6 2 2 3 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1344

/-- Explicit rank-deficient target for canonical pattern `(2, 2, 4, 4, 4, 4)`. -/
def targetTop_1345 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     1, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1345 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_1345 :
    TopRowRelation targetTop_1345 relationCoefficients_1345 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1345, relationCoefficients_1345, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1345 : BottomDetBound targetTop_1345 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1345

theorem canonicalBound_1345 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 4 4 4 4)) 9 := by
  have htop : targetTop_1345 =
      topOfPattern (R := ℤ) (angle6 2 2 4 4 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1345

/-- Explicit target top block for canonical pattern `(2, 2, 4, 4, 4, 5)`. -/
def targetTop_1346 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     1, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1346 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 1]

def columnPerm_1346 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1346 : BottomDetBound targetTop_1346 9 := by
  have hU : rowTransform_1346.det.natAbs = 1 := by
    have hdet : rowTransform_1346.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1346 hU
  have hcols := hrows.permuteColumns columnPerm_1346
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1346 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1346 = targetTop_1346 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1346 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 4 4 4 5)) 9 := by
  have htop : targetTop_1346 =
      topOfPattern (R := ℤ) (angle6 2 2 4 4 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1346

/-- Explicit rank-deficient target for canonical pattern `(2, 2, 4, 4, 4, 6)`. -/
def targetTop_1347 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     1, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1347 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_1347 :
    TopRowRelation targetTop_1347 relationCoefficients_1347 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1347, relationCoefficients_1347, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1347 : BottomDetBound targetTop_1347 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1347

theorem canonicalBound_1347 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 4 4 4 6)) 9 := by
  have htop : targetTop_1347 =
      topOfPattern (R := ℤ) (angle6 2 2 4 4 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1347

/-- Explicit target top block for canonical pattern `(2, 2, 4, 4, 4, 7)`. -/
def targetTop_1348 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     1, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1348 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 1;
     1, 0, 1]

def columnPerm_1348 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1348 : BottomDetBound targetTop_1348 9 := by
  have hU : rowTransform_1348.det.natAbs = 1 := by
    have hdet : rowTransform_1348.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1348 hU
  have hcols := hrows.permuteColumns columnPerm_1348
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1348 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1348 = targetTop_1348 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1348 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 4 4 4 7)) 9 := by
  have htop : targetTop_1348 =
      topOfPattern (R := ℤ) (angle6 2 2 4 4 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1348

/-- Explicit target top block for canonical pattern `(2, 2, 4, 4, 5, 5)`. -/
def targetTop_1349 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     1, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1349 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 1]

def columnPerm_1349 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1349 : BottomDetBound targetTop_1349 9 := by
  have hU : rowTransform_1349.det.natAbs = 1 := by
    have hdet : rowTransform_1349.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate.bottomBound.transformTopRows rowTransform_1349 hU
  have hcols := hrows.permuteColumns columnPerm_1349
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1349 MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Base.explicitTop)
          columnPerm_1349 = targetTop_1349 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1349 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 4 4 5 5)) 9 := by
  have htop : targetTop_1349 =
      topOfPattern (R := ℤ) (angle6 2 2 4 4 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1349

/-- Explicit target top block for canonical pattern `(2, 2, 4, 4, 5, 6)`. -/
def targetTop_1350 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 0;
     1, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1350 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 1]

def columnPerm_1350 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 5, 4]
  invFun := ![0, 1, 2, 3, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1350 : BottomDetBound targetTop_1350 9 := by
  have hU : rowTransform_1350.det.natAbs = 1 := by
    have hdet : rowTransform_1350.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate.bottomBound.transformTopRows rowTransform_1350 hU
  have hcols := hrows.permuteColumns columnPerm_1350
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1350 MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Base.explicitTop)
          columnPerm_1350 = targetTop_1350 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1350 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 4 4 5 6)) 9 := by
  have htop : targetTop_1350 =
      topOfPattern (R := ℤ) (angle6 2 2 4 4 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1350

/-- Explicit target top block for canonical pattern `(2, 2, 4, 4, 5, 7)`. -/
def targetTop_1351 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     1, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1351 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 1]

def columnPerm_1351 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1351 : BottomDetBound targetTop_1351 9 := by
  have hU : rowTransform_1351.det.natAbs = 1 := by
    have hdet : rowTransform_1351.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_1351 hU
  have hcols := hrows.permuteColumns columnPerm_1351
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1351 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_1351 = targetTop_1351 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1351 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 4 4 5 7)) 9 := by
  have htop : targetTop_1351 =
      topOfPattern (R := ℤ) (angle6 2 2 4 4 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1351

/-- Explicit rank-deficient target for canonical pattern `(2, 2, 4, 4, 6, 6)`. -/
def targetTop_1352 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     1, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1352 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_1352 :
    TopRowRelation targetTop_1352 relationCoefficients_1352 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1352, relationCoefficients_1352, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1352 : BottomDetBound targetTop_1352 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1352

theorem canonicalBound_1352 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 4 4 6 6)) 9 := by
  have htop : targetTop_1352 =
      topOfPattern (R := ℤ) (angle6 2 2 4 4 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1352

/-- Explicit target top block for canonical pattern `(2, 2, 4, 4, 6, 7)`. -/
def targetTop_1353 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     1, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1353 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 1;
     0, 1, 1]

def columnPerm_1353 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1353 : BottomDetBound targetTop_1353 9 := by
  have hU : rowTransform_1353.det.natAbs = 1 := by
    have hdet : rowTransform_1353.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate.bottomBound.transformTopRows rowTransform_1353 hU
  have hcols := hrows.permuteColumns columnPerm_1353
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1353 MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Base.explicitTop)
          columnPerm_1353 = targetTop_1353 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1353 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 4 4 6 7)) 9 := by
  have htop : targetTop_1353 =
      topOfPattern (R := ℤ) (angle6 2 2 4 4 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1353

/-- Explicit target top block for canonical pattern `(2, 2, 4, 4, 7, 7)`. -/
def targetTop_1354 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     1, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1354 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 1;
     0, 1, 1]

def columnPerm_1354 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1354 : BottomDetBound targetTop_1354 9 := by
  have hU : rowTransform_1354.det.natAbs = 1 := by
    have hdet : rowTransform_1354.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate.bottomBound.transformTopRows rowTransform_1354 hU
  have hcols := hrows.permuteColumns columnPerm_1354
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1354 MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Base.explicitTop)
          columnPerm_1354 = targetTop_1354 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1354 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 4 4 7 7)) 9 := by
  have htop : targetTop_1354 =
      topOfPattern (R := ℤ) (angle6 2 2 4 4 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1354

/-- Explicit target top block for canonical pattern `(2, 2, 4, 5, 5, 5)`. -/
def targetTop_1355 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     1, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1355 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     1, 0, 1]

def columnPerm_1355 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1355 : BottomDetBound targetTop_1355 9 := by
  have hU : rowTransform_1355.det.natAbs = 1 := by
    have hdet : rowTransform_1355.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1355 hU
  have hcols := hrows.permuteColumns columnPerm_1355
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1355 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1355 = targetTop_1355 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1355 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 4 5 5 5)) 9 := by
  have htop : targetTop_1355 =
      topOfPattern (R := ℤ) (angle6 2 2 4 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1355

/-- Explicit target top block for canonical pattern `(2, 2, 4, 5, 5, 6)`. -/
def targetTop_1356 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 0;
     1, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1356 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 1, 1]

def columnPerm_1356 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1356 : BottomDetBound targetTop_1356 9 := by
  have hU : rowTransform_1356.det.natAbs = 1 := by
    have hdet : rowTransform_1356.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_1356 hU
  have hcols := hrows.permuteColumns columnPerm_1356
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1356 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_1356 = targetTop_1356 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1356 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 4 5 5 6)) 9 := by
  have htop : targetTop_1356 =
      topOfPattern (R := ℤ) (angle6 2 2 4 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1356

/-- Explicit target top block for canonical pattern `(2, 2, 4, 5, 5, 7)`. -/
def targetTop_1357 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     1, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1357 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 1, 1]

def columnPerm_1357 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1357 : BottomDetBound targetTop_1357 9 := by
  have hU : rowTransform_1357.det.natAbs = 1 := by
    have hdet : rowTransform_1357.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate.bottomBound.transformTopRows rowTransform_1357 hU
  have hcols := hrows.permuteColumns columnPerm_1357
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1357 MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Base.explicitTop)
          columnPerm_1357 = targetTop_1357 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1357 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 4 5 5 7)) 9 := by
  have htop : targetTop_1357 =
      topOfPattern (R := ℤ) (angle6 2 2 4 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1357

/-- Explicit target top block for canonical pattern `(2, 2, 4, 5, 6, 6)`. -/
def targetTop_1358 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 0;
     1, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1358 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 1]

def columnPerm_1358 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1358 : BottomDetBound targetTop_1358 9 := by
  have hU : rowTransform_1358.det.natAbs = 1 := by
    have hdet : rowTransform_1358.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_1358 hU
  have hcols := hrows.permuteColumns columnPerm_1358
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1358 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_1358 = targetTop_1358 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1358 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 4 5 6 6)) 9 := by
  have htop : targetTop_1358 =
      topOfPattern (R := ℤ) (angle6 2 2 4 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1358

/-- Explicit target top block for canonical pattern `(2, 2, 4, 5, 6, 7)`. -/
def targetTop_1359 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 1;
     1, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1359 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 1]

def columnPerm_1359 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 4, 3, 5]
  invFun := ![0, 1, 2, 4, 3, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1359 : BottomDetBound targetTop_1359 9 := by
  have hU : rowTransform_1359.det.natAbs = 1 := by
    have hdet : rowTransform_1359.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R042.Aggregate.bottomBound.transformTopRows rowTransform_1359 hU
  have hcols := hrows.permuteColumns columnPerm_1359
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1359 MainTheory.Generated.BinaryBetaSixKernel.Representative.R042.Base.explicitTop)
          columnPerm_1359 = targetTop_1359 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1359 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 4 5 6 7)) 9 := by
  have htop : targetTop_1359 =
      topOfPattern (R := ℤ) (angle6 2 2 4 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1359

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard084
