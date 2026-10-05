-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R065.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R068.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R071.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard090

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(2, 3, 5, 5, 7, 7)`. -/
def targetTop_1440 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     1, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1440 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 1;
     1, 0, 0]

def columnPerm_1440 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 0, 1, 3, 4]
  invFun := ![2, 3, 0, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1440 : BottomDetBound targetTop_1440 9 := by
  have hU : rowTransform_1440.det.natAbs = 1 := by
    have hdet : rowTransform_1440.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_1440 hU
  have hcols := hrows.permuteColumns columnPerm_1440
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1440 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_1440 = targetTop_1440 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1440 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 5 5 7 7)) 9 := by
  have htop : targetTop_1440 =
      topOfPattern (R := ℤ) (angle6 2 3 5 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1440

/-- Explicit target top block for canonical pattern `(2, 3, 5, 6, 6, 6)`. -/
def targetTop_1441 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 0;
     1, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1441 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1441 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1441 : BottomDetBound targetTop_1441 9 := by
  have hU : rowTransform_1441.det.natAbs = 1 := by
    have hdet : rowTransform_1441.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R065.Aggregate.bottomBound.transformTopRows rowTransform_1441 hU
  have hcols := hrows.permuteColumns columnPerm_1441
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1441 MainTheory.Generated.BinaryBetaSixKernel.Representative.R065.Base.explicitTop)
          columnPerm_1441 = targetTop_1441 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1441 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 5 6 6 6)) 9 := by
  have htop : targetTop_1441 =
      topOfPattern (R := ℤ) (angle6 2 3 5 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1441

/-- Explicit target top block for canonical pattern `(2, 3, 5, 6, 6, 7)`. -/
def targetTop_1442 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 1;
     1, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1442 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1442 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 4, 1, 2, 5]
  invFun := ![0, 3, 4, 1, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1442 : BottomDetBound targetTop_1442 9 := by
  have hU : rowTransform_1442.det.natAbs = 1 := by
    have hdet : rowTransform_1442.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R068.Aggregate.bottomBound.transformTopRows rowTransform_1442 hU
  have hcols := hrows.permuteColumns columnPerm_1442
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1442 MainTheory.Generated.BinaryBetaSixKernel.Representative.R068.Base.explicitTop)
          columnPerm_1442 = targetTop_1442 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1442 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 5 6 6 7)) 9 := by
  have htop : targetTop_1442 =
      topOfPattern (R := ℤ) (angle6 2 3 5 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1442

/-- Explicit target top block for canonical pattern `(2, 3, 5, 6, 7, 7)`. -/
def targetTop_1443 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 1, 1;
     1, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1443 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1443 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 3, 2, 4, 5]
  invFun := ![0, 1, 3, 2, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1443 : BottomDetBound targetTop_1443 9 := by
  have hU : rowTransform_1443.det.natAbs = 1 := by
    have hdet : rowTransform_1443.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R071.Aggregate.bottomBound.transformTopRows rowTransform_1443 hU
  have hcols := hrows.permuteColumns columnPerm_1443
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1443 MainTheory.Generated.BinaryBetaSixKernel.Representative.R071.Base.explicitTop)
          columnPerm_1443 = targetTop_1443 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1443 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 5 6 7 7)) 9 := by
  have htop : targetTop_1443 =
      topOfPattern (R := ℤ) (angle6 2 3 5 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1443

/-- Explicit target top block for canonical pattern `(2, 3, 5, 7, 7, 7)`. -/
def targetTop_1444 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     1, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1444 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 1;
     0, 1, 0]

def columnPerm_1444 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1444 : BottomDetBound targetTop_1444 9 := by
  have hU : rowTransform_1444.det.natAbs = 1 := by
    have hdet : rowTransform_1444.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Aggregate.bottomBound.transformTopRows rowTransform_1444 hU
  have hcols := hrows.permuteColumns columnPerm_1444
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1444 MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Base.explicitTop)
          columnPerm_1444 = targetTop_1444 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1444 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 5 7 7 7)) 9 := by
  have htop : targetTop_1444 =
      topOfPattern (R := ℤ) (angle6 2 3 5 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1444

/-- Explicit target top block for canonical pattern `(2, 3, 6, 6, 6, 6)`. -/
def targetTop_1445 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 0;
     1, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1445 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, 1;
     1, 0, 0]

def columnPerm_1445 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1445 : BottomDetBound targetTop_1445 9 := by
  have hU : rowTransform_1445.det.natAbs = 1 := by
    have hdet : rowTransform_1445.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1445 hU
  have hcols := hrows.permuteColumns columnPerm_1445
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1445 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1445 = targetTop_1445 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1445 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 6 6 6 6)) 9 := by
  have htop : targetTop_1445 =
      topOfPattern (R := ℤ) (angle6 2 3 6 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1445

/-- Explicit target top block for canonical pattern `(2, 3, 6, 6, 6, 7)`. -/
def targetTop_1446 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1446 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, 0;
     1, 0, 0]

def columnPerm_1446 : Equiv.Perm (Fin 6) where
  toFun := ![3, 5, 0, 1, 2, 4]
  invFun := ![2, 3, 4, 0, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1446 : BottomDetBound targetTop_1446 9 := by
  have hU : rowTransform_1446.det.natAbs = 1 := by
    have hdet : rowTransform_1446.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate.bottomBound.transformTopRows rowTransform_1446 hU
  have hcols := hrows.permuteColumns columnPerm_1446
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1446 MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Base.explicitTop)
          columnPerm_1446 = targetTop_1446 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1446 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 6 6 6 7)) 9 := by
  have htop : targetTop_1446 =
      topOfPattern (R := ℤ) (angle6 2 3 6 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1446

/-- Explicit target top block for canonical pattern `(2, 3, 6, 6, 7, 7)`. -/
def targetTop_1447 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1447 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 0;
     1, 1, (-1)]

def columnPerm_1447 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1447 : BottomDetBound targetTop_1447 9 := by
  have hU : rowTransform_1447.det.natAbs = 1 := by
    have hdet : rowTransform_1447.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate.bottomBound.transformTopRows rowTransform_1447 hU
  have hcols := hrows.permuteColumns columnPerm_1447
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1447 MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Base.explicitTop)
          columnPerm_1447 = targetTop_1447 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1447 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 6 6 7 7)) 9 := by
  have htop : targetTop_1447 =
      topOfPattern (R := ℤ) (angle6 2 3 6 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1447

/-- Explicit target top block for canonical pattern `(2, 3, 6, 7, 7, 7)`. -/
def targetTop_1448 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1448 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, (-1);
     1, 1, 0;
     1, 0, 0]

def columnPerm_1448 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1448 : BottomDetBound targetTop_1448 9 := by
  have hU : rowTransform_1448.det.natAbs = 1 := by
    have hdet : rowTransform_1448.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate.bottomBound.transformTopRows rowTransform_1448 hU
  have hcols := hrows.permuteColumns columnPerm_1448
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1448 MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Base.explicitTop)
          columnPerm_1448 = targetTop_1448 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1448 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 6 7 7 7)) 9 := by
  have htop : targetTop_1448 =
      topOfPattern (R := ℤ) (angle6 2 3 6 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1448

/-- Explicit target top block for canonical pattern `(2, 3, 7, 7, 7, 7)`. -/
def targetTop_1449 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1449 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 1, 1;
     1, 0, 0]

def columnPerm_1449 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1449 : BottomDetBound targetTop_1449 9 := by
  have hU : rowTransform_1449.det.natAbs = 1 := by
    have hdet : rowTransform_1449.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1449 hU
  have hcols := hrows.permuteColumns columnPerm_1449
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1449 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1449 = targetTop_1449 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1449 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 7 7 7 7)) 9 := by
  have htop : targetTop_1449 =
      topOfPattern (R := ℤ) (angle6 2 3 7 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1449

/-- Explicit rank-deficient target for canonical pattern `(2, 4, 4, 4, 4, 4)`. -/
def targetTop_1450 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1450 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_1450 :
    TopRowRelation targetTop_1450 relationCoefficients_1450 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1450, relationCoefficients_1450, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1450 : BottomDetBound targetTop_1450 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1450

theorem canonicalBound_1450 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 4 4 4 4)) 9 := by
  have htop : targetTop_1450 =
      topOfPattern (R := ℤ) (angle6 2 4 4 4 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1450

/-- Explicit target top block for canonical pattern `(2, 4, 4, 4, 4, 5)`. -/
def targetTop_1451 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     1, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1451 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 1]

def columnPerm_1451 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1451 : BottomDetBound targetTop_1451 9 := by
  have hU : rowTransform_1451.det.natAbs = 1 := by
    have hdet : rowTransform_1451.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1451 hU
  have hcols := hrows.permuteColumns columnPerm_1451
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1451 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1451 = targetTop_1451 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1451 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 4 4 4 5)) 9 := by
  have htop : targetTop_1451 =
      topOfPattern (R := ℤ) (angle6 2 4 4 4 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1451

/-- Explicit rank-deficient target for canonical pattern `(2, 4, 4, 4, 4, 6)`. -/
def targetTop_1452 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1452 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_1452 :
    TopRowRelation targetTop_1452 relationCoefficients_1452 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1452, relationCoefficients_1452, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1452 : BottomDetBound targetTop_1452 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1452

theorem canonicalBound_1452 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 4 4 4 6)) 9 := by
  have htop : targetTop_1452 =
      topOfPattern (R := ℤ) (angle6 2 4 4 4 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1452

/-- Explicit target top block for canonical pattern `(2, 4, 4, 4, 4, 7)`. -/
def targetTop_1453 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     1, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1453 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 1;
     1, 0, 1]

def columnPerm_1453 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1453 : BottomDetBound targetTop_1453 9 := by
  have hU : rowTransform_1453.det.natAbs = 1 := by
    have hdet : rowTransform_1453.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1453 hU
  have hcols := hrows.permuteColumns columnPerm_1453
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1453 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1453 = targetTop_1453 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1453 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 4 4 4 7)) 9 := by
  have htop : targetTop_1453 =
      topOfPattern (R := ℤ) (angle6 2 4 4 4 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1453

/-- Explicit target top block for canonical pattern `(2, 4, 4, 4, 5, 5)`. -/
def targetTop_1454 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     1, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1454 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 1, 0]

def columnPerm_1454 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1454 : BottomDetBound targetTop_1454 9 := by
  have hU : rowTransform_1454.det.natAbs = 1 := by
    have hdet : rowTransform_1454.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1454 hU
  have hcols := hrows.permuteColumns columnPerm_1454
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1454 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1454 = targetTop_1454 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1454 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 4 4 5 5)) 9 := by
  have htop : targetTop_1454 =
      topOfPattern (R := ℤ) (angle6 2 4 4 4 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1454

/-- Explicit target top block for canonical pattern `(2, 4, 4, 4, 5, 6)`. -/
def targetTop_1455 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 0;
     1, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1455 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 1]

def columnPerm_1455 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 5, 4]
  invFun := ![1, 2, 3, 0, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1455 : BottomDetBound targetTop_1455 9 := by
  have hU : rowTransform_1455.det.natAbs = 1 := by
    have hdet : rowTransform_1455.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_1455 hU
  have hcols := hrows.permuteColumns columnPerm_1455
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1455 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_1455 = targetTop_1455 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1455 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 4 4 5 6)) 9 := by
  have htop : targetTop_1455 =
      topOfPattern (R := ℤ) (angle6 2 4 4 4 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1455

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard090
