-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R050.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R057.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R061.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R062.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R064.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R067.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R069.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R070.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard089

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(2, 3, 4, 4, 7, 7)`. -/
def targetTop_1424 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 1, 1;
     1, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1424 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 1, 1;
     1, 0, 0]

def columnPerm_1424 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 0, 1, 3, 4]
  invFun := ![2, 3, 1, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1424 : BottomDetBound targetTop_1424 9 := by
  have hU : rowTransform_1424.det.natAbs = 1 := by
    have hdet : rowTransform_1424.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_1424 hU
  have hcols := hrows.permuteColumns columnPerm_1424
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1424 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_1424 = targetTop_1424 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1424 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 4 4 7 7)) 9 := by
  have htop : targetTop_1424 =
      topOfPattern (R := ℤ) (angle6 2 3 4 4 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1424

/-- Explicit target top block for canonical pattern `(2, 3, 4, 5, 5, 5)`. -/
def targetTop_1425 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 1, 1;
     1, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1425 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, (-1);
     0, 1, 0;
     1, 0, 0]

def columnPerm_1425 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1425 : BottomDetBound targetTop_1425 9 := by
  have hU : rowTransform_1425.det.natAbs = 1 := by
    have hdet : rowTransform_1425.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate.bottomBound.transformTopRows rowTransform_1425 hU
  have hcols := hrows.permuteColumns columnPerm_1425
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1425 MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Base.explicitTop)
          columnPerm_1425 = targetTop_1425 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1425 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 4 5 5 5)) 9 := by
  have htop : targetTop_1425 =
      topOfPattern (R := ℤ) (angle6 2 3 4 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1425

/-- Explicit target top block for canonical pattern `(2, 3, 4, 5, 5, 6)`. -/
def targetTop_1426 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 1, 0;
     1, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1426 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 0]

def columnPerm_1426 : Equiv.Perm (Fin 6) where
  toFun := ![1, 5, 0, 3, 4, 2]
  invFun := ![2, 0, 5, 3, 4, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1426 : BottomDetBound targetTop_1426 9 := by
  have hU : rowTransform_1426.det.natAbs = 1 := by
    have hdet : rowTransform_1426.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R061.Aggregate.bottomBound.transformTopRows rowTransform_1426 hU
  have hcols := hrows.permuteColumns columnPerm_1426
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1426 MainTheory.Generated.BinaryBetaSixKernel.Representative.R061.Base.explicitTop)
          columnPerm_1426 = targetTop_1426 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1426 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 4 5 5 6)) 9 := by
  have htop : targetTop_1426 =
      topOfPattern (R := ℤ) (angle6 2 3 4 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1426

/-- Explicit target top block for canonical pattern `(2, 3, 4, 5, 5, 7)`. -/
def targetTop_1427 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 1, 1;
     1, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1427 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, (-1);
     0, 1, 0;
     1, 0, 0]

def columnPerm_1427 : Equiv.Perm (Fin 6) where
  toFun := ![4, 2, 3, 0, 1, 5]
  invFun := ![3, 4, 1, 2, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1427 : BottomDetBound targetTop_1427 9 := by
  have hU : rowTransform_1427.det.natAbs = 1 := by
    have hdet : rowTransform_1427.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R050.Aggregate.bottomBound.transformTopRows rowTransform_1427 hU
  have hcols := hrows.permuteColumns columnPerm_1427
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1427 MainTheory.Generated.BinaryBetaSixKernel.Representative.R050.Base.explicitTop)
          columnPerm_1427 = targetTop_1427 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1427 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 4 5 5 7)) 9 := by
  have htop : targetTop_1427 =
      topOfPattern (R := ℤ) (angle6 2 3 4 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1427

/-- Explicit target top block for canonical pattern `(2, 3, 4, 5, 6, 6)`. -/
def targetTop_1428 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 0, 0;
     1, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1428 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1428 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 5, 2, 3]
  invFun := ![0, 2, 4, 5, 1, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1428 : BottomDetBound targetTop_1428 9 := by
  have hU : rowTransform_1428.det.natAbs = 1 := by
    have hdet : rowTransform_1428.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R057.Aggregate.bottomBound.transformTopRows rowTransform_1428 hU
  have hcols := hrows.permuteColumns columnPerm_1428
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1428 MainTheory.Generated.BinaryBetaSixKernel.Representative.R057.Base.explicitTop)
          columnPerm_1428 = targetTop_1428 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1428 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 4 5 6 6)) 9 := by
  have htop : targetTop_1428 =
      topOfPattern (R := ℤ) (angle6 2 3 4 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1428

/-- Explicit target top block for canonical pattern `(2, 3, 4, 5, 6, 7)`. -/
def targetTop_1429 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 0, 1;
     1, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1429 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1429 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 4, 2, 5]
  invFun := ![0, 2, 4, 1, 3, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1429 : BottomDetBound targetTop_1429 9 := by
  have hU : rowTransform_1429.det.natAbs = 1 := by
    have hdet : rowTransform_1429.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R062.Aggregate.bottomBound.transformTopRows rowTransform_1429 hU
  have hcols := hrows.permuteColumns columnPerm_1429
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1429 MainTheory.Generated.BinaryBetaSixKernel.Representative.R062.Base.explicitTop)
          columnPerm_1429 = targetTop_1429 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1429 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 4 5 6 7)) 9 := by
  have htop : targetTop_1429 =
      topOfPattern (R := ℤ) (angle6 2 3 4 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1429

/-- Explicit target top block for canonical pattern `(2, 3, 4, 5, 7, 7)`. -/
def targetTop_1430 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 1, 1;
     1, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1430 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, (-1);
     0, 0, 1]

def columnPerm_1430 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1430 : BottomDetBound targetTop_1430 9 := by
  have hU : rowTransform_1430.det.natAbs = 1 := by
    have hdet : rowTransform_1430.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R064.Aggregate.bottomBound.transformTopRows rowTransform_1430 hU
  have hcols := hrows.permuteColumns columnPerm_1430
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1430 MainTheory.Generated.BinaryBetaSixKernel.Representative.R064.Base.explicitTop)
          columnPerm_1430 = targetTop_1430 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1430 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 4 5 7 7)) 9 := by
  have htop : targetTop_1430 =
      topOfPattern (R := ℤ) (angle6 2 3 4 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1430

/-- Explicit target top block for canonical pattern `(2, 3, 4, 6, 6, 6)`. -/
def targetTop_1431 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 0;
     1, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1431 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 1;
     0, 1, 0]

def columnPerm_1431 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1431 : BottomDetBound targetTop_1431 9 := by
  have hU : rowTransform_1431.det.natAbs = 1 := by
    have hdet : rowTransform_1431.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Aggregate.bottomBound.transformTopRows rowTransform_1431 hU
  have hcols := hrows.permuteColumns columnPerm_1431
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1431 MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Base.explicitTop)
          columnPerm_1431 = targetTop_1431 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1431 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 4 6 6 6)) 9 := by
  have htop : targetTop_1431 =
      topOfPattern (R := ℤ) (angle6 2 3 4 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1431

/-- Explicit target top block for canonical pattern `(2, 3, 4, 6, 6, 7)`. -/
def targetTop_1432 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 1;
     1, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1432 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 1;
     1, 0, 0]

def columnPerm_1432 : Equiv.Perm (Fin 6) where
  toFun := ![1, 4, 0, 2, 3, 5]
  invFun := ![2, 0, 3, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1432 : BottomDetBound targetTop_1432 9 := by
  have hU : rowTransform_1432.det.natAbs = 1 := by
    have hdet : rowTransform_1432.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Aggregate.bottomBound.transformTopRows rowTransform_1432 hU
  have hcols := hrows.permuteColumns columnPerm_1432
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1432 MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Base.explicitTop)
          columnPerm_1432 = targetTop_1432 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1432 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 4 6 6 7)) 9 := by
  have htop : targetTop_1432 =
      topOfPattern (R := ℤ) (angle6 2 3 4 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1432

/-- Explicit target top block for canonical pattern `(2, 3, 4, 6, 7, 7)`. -/
def targetTop_1433 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 1, 1;
     1, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1433 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 1, 1;
     1, 0, 0]

def columnPerm_1433 : Equiv.Perm (Fin 6) where
  toFun := ![4, 1, 0, 5, 2, 3]
  invFun := ![2, 1, 4, 5, 0, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1433 : BottomDetBound targetTop_1433 9 := by
  have hU : rowTransform_1433.det.natAbs = 1 := by
    have hdet : rowTransform_1433.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Aggregate.bottomBound.transformTopRows rowTransform_1433 hU
  have hcols := hrows.permuteColumns columnPerm_1433
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1433 MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Base.explicitTop)
          columnPerm_1433 = targetTop_1433 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1433 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 4 6 7 7)) 9 := by
  have htop : targetTop_1433 =
      topOfPattern (R := ℤ) (angle6 2 3 4 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1433

/-- Explicit target top block for canonical pattern `(2, 3, 4, 7, 7, 7)`. -/
def targetTop_1434 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 1, 1;
     1, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1434 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 0, 1;
     0, 1, 0]

def columnPerm_1434 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1434 : BottomDetBound targetTop_1434 9 := by
  have hU : rowTransform_1434.det.natAbs = 1 := by
    have hdet : rowTransform_1434.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Aggregate.bottomBound.transformTopRows rowTransform_1434 hU
  have hcols := hrows.permuteColumns columnPerm_1434
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1434 MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Base.explicitTop)
          columnPerm_1434 = targetTop_1434 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1434 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 4 7 7 7)) 9 := by
  have htop : targetTop_1434 =
      topOfPattern (R := ℤ) (angle6 2 3 4 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1434

/-- Explicit target top block for canonical pattern `(2, 3, 5, 5, 5, 5)`. -/
def targetTop_1435 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     1, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1435 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 1;
     1, 0, 0]

def columnPerm_1435 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1435 : BottomDetBound targetTop_1435 9 := by
  have hU : rowTransform_1435.det.natAbs = 1 := by
    have hdet : rowTransform_1435.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1435 hU
  have hcols := hrows.permuteColumns columnPerm_1435
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1435 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1435 = targetTop_1435 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1435 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 5 5 5 5)) 9 := by
  have htop : targetTop_1435 =
      topOfPattern (R := ℤ) (angle6 2 3 5 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1435

/-- Explicit target top block for canonical pattern `(2, 3, 5, 5, 5, 6)`. -/
def targetTop_1436 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 0;
     1, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1436 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1436 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 3, 4, 5, 2]
  invFun := ![0, 1, 5, 2, 3, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1436 : BottomDetBound targetTop_1436 9 := by
  have hU : rowTransform_1436.det.natAbs = 1 := by
    have hdet : rowTransform_1436.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R069.Aggregate.bottomBound.transformTopRows rowTransform_1436 hU
  have hcols := hrows.permuteColumns columnPerm_1436
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1436 MainTheory.Generated.BinaryBetaSixKernel.Representative.R069.Base.explicitTop)
          columnPerm_1436 = targetTop_1436 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1436 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 5 5 5 6)) 9 := by
  have htop : targetTop_1436 =
      topOfPattern (R := ℤ) (angle6 2 3 5 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1436

/-- Explicit target top block for canonical pattern `(2, 3, 5, 5, 5, 7)`. -/
def targetTop_1437 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     1, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1437 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 1;
     1, 0, 0]

def columnPerm_1437 : Equiv.Perm (Fin 6) where
  toFun := ![3, 5, 0, 1, 2, 4]
  invFun := ![2, 3, 4, 0, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1437 : BottomDetBound targetTop_1437 9 := by
  have hU : rowTransform_1437.det.natAbs = 1 := by
    have hdet : rowTransform_1437.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_1437 hU
  have hcols := hrows.permuteColumns columnPerm_1437
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1437 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_1437 = targetTop_1437 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1437 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 5 5 5 7)) 9 := by
  have htop : targetTop_1437 =
      topOfPattern (R := ℤ) (angle6 2 3 5 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1437

/-- Explicit target top block for canonical pattern `(2, 3, 5, 5, 6, 6)`. -/
def targetTop_1438 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 0;
     1, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1438 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1438 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 4, 5, 1, 2]
  invFun := ![0, 4, 5, 1, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1438 : BottomDetBound targetTop_1438 9 := by
  have hU : rowTransform_1438.det.natAbs = 1 := by
    have hdet : rowTransform_1438.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R067.Aggregate.bottomBound.transformTopRows rowTransform_1438 hU
  have hcols := hrows.permuteColumns columnPerm_1438
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1438 MainTheory.Generated.BinaryBetaSixKernel.Representative.R067.Base.explicitTop)
          columnPerm_1438 = targetTop_1438 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1438 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 5 5 6 6)) 9 := by
  have htop : targetTop_1438 =
      topOfPattern (R := ℤ) (angle6 2 3 5 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1438

/-- Explicit target top block for canonical pattern `(2, 3, 5, 5, 6, 7)`. -/
def targetTop_1439 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 1;
     1, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1439 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1439 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 3, 4, 2, 5]
  invFun := ![0, 1, 4, 2, 3, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1439 : BottomDetBound targetTop_1439 9 := by
  have hU : rowTransform_1439.det.natAbs = 1 := by
    have hdet : rowTransform_1439.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R070.Aggregate.bottomBound.transformTopRows rowTransform_1439 hU
  have hcols := hrows.permuteColumns columnPerm_1439
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1439 MainTheory.Generated.BinaryBetaSixKernel.Representative.R070.Base.explicitTop)
          columnPerm_1439 = targetTop_1439 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1439 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 5 5 6 7)) 9 := by
  have htop : targetTop_1439 =
      topOfPattern (R := ℤ) (angle6 2 3 5 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1439

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard089
