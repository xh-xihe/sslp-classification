-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R017.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R018.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R019.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard027

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(0, 1, 2, 2, 6, 6)`. -/
def targetTop_0432 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0432 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, 0;
     0, 1, 0]

def columnPerm_0432 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0432 : BottomDetBound targetTop_0432 9 := by
  have hU : rowTransform_0432.det.natAbs = 1 := by
    have hdet : rowTransform_0432.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0432 hU
  have hcols := hrows.permuteColumns columnPerm_0432
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0432 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0432 = targetTop_0432 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0432 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 2 6 6)) 9 := by
  have htop : targetTop_0432 =
      topOfPattern (R := ℤ) (angle6 0 1 2 2 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0432

/-- Explicit target top block for canonical pattern `(0, 1, 2, 2, 6, 7)`. -/
def targetTop_0433 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0433 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 1;
     0, 0, 1]

def columnPerm_0433 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 4, 5]
  invFun := ![0, 2, 3, 1, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0433 : BottomDetBound targetTop_0433 9 := by
  have hU : rowTransform_0433.det.natAbs = 1 := by
    have hdet : rowTransform_0433.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate.bottomBound.transformTopRows rowTransform_0433 hU
  have hcols := hrows.permuteColumns columnPerm_0433
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0433 MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Base.explicitTop)
          columnPerm_0433 = targetTop_0433 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0433 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 2 6 7)) 9 := by
  have htop : targetTop_0433 =
      topOfPattern (R := ℤ) (angle6 0 1 2 2 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0433

/-- Explicit target top block for canonical pattern `(0, 1, 2, 2, 7, 7)`. -/
def targetTop_0434 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0434 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 1, 0;
     0, 1, 0]

def columnPerm_0434 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0434 : BottomDetBound targetTop_0434 9 := by
  have hU : rowTransform_0434.det.natAbs = 1 := by
    have hdet : rowTransform_0434.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0434 hU
  have hcols := hrows.permuteColumns columnPerm_0434
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0434 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0434 = targetTop_0434 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0434 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 2 7 7)) 9 := by
  have htop : targetTop_0434 =
      topOfPattern (R := ℤ) (angle6 0 1 2 2 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0434

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 2, 3, 3, 3)`. -/
def targetTop_0435 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0435 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0435 :
    TopRowRelation targetTop_0435 relationCoefficients_0435 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0435, relationCoefficients_0435, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0435 : BottomDetBound targetTop_0435 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0435

theorem canonicalBound_0435 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 3 3 3)) 9 := by
  have htop : targetTop_0435 =
      topOfPattern (R := ℤ) (angle6 0 1 2 3 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0435

/-- Explicit target top block for canonical pattern `(0, 1, 2, 3, 3, 4)`. -/
def targetTop_0436 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 1, 0;
     0, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0436 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0436 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0436 : BottomDetBound targetTop_0436 9 := by
  have hU : rowTransform_0436.det.natAbs = 1 := by
    have hdet : rowTransform_0436.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Aggregate.bottomBound.transformTopRows rowTransform_0436 hU
  have hcols := hrows.permuteColumns columnPerm_0436
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0436 MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Base.explicitTop)
          columnPerm_0436 = targetTop_0436 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0436 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 3 3 4)) 9 := by
  have htop : targetTop_0436 =
      topOfPattern (R := ℤ) (angle6 0 1 2 3 3 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0436

/-- Explicit target top block for canonical pattern `(0, 1, 2, 3, 3, 5)`. -/
def targetTop_0437 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0437 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0437 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0437 : BottomDetBound targetTop_0437 9 := by
  have hU : rowTransform_0437.det.natAbs = 1 := by
    have hdet : rowTransform_0437.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Aggregate.bottomBound.transformTopRows rowTransform_0437 hU
  have hcols := hrows.permuteColumns columnPerm_0437
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0437 MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Base.explicitTop)
          columnPerm_0437 = targetTop_0437 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0437 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 3 3 5)) 9 := by
  have htop : targetTop_0437 =
      topOfPattern (R := ℤ) (angle6 0 1 2 3 3 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0437

/-- Explicit target top block for canonical pattern `(0, 1, 2, 3, 3, 6)`. -/
def targetTop_0438 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 1, 0;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0438 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0438 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0438 : BottomDetBound targetTop_0438 9 := by
  have hU : rowTransform_0438.det.natAbs = 1 := by
    have hdet : rowTransform_0438.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Aggregate.bottomBound.transformTopRows rowTransform_0438 hU
  have hcols := hrows.permuteColumns columnPerm_0438
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0438 MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Base.explicitTop)
          columnPerm_0438 = targetTop_0438 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0438 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 3 3 6)) 9 := by
  have htop : targetTop_0438 =
      topOfPattern (R := ℤ) (angle6 0 1 2 3 3 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0438

/-- Explicit target top block for canonical pattern `(0, 1, 2, 3, 3, 7)`. -/
def targetTop_0439 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0439 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0439 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0439 : BottomDetBound targetTop_0439 9 := by
  have hU : rowTransform_0439.det.natAbs = 1 := by
    have hdet : rowTransform_0439.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Aggregate.bottomBound.transformTopRows rowTransform_0439 hU
  have hcols := hrows.permuteColumns columnPerm_0439
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0439 MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Base.explicitTop)
          columnPerm_0439 = targetTop_0439 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0439 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 3 3 7)) 9 := by
  have htop : targetTop_0439 =
      topOfPattern (R := ℤ) (angle6 0 1 2 3 3 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0439

/-- Explicit target top block for canonical pattern `(0, 1, 2, 3, 4, 4)`. -/
def targetTop_0440 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 0, 0;
     0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0440 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_0440 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 4, 5, 1, 2]
  invFun := ![0, 4, 5, 1, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0440 : BottomDetBound targetTop_0440 9 := by
  have hU : rowTransform_0440.det.natAbs = 1 := by
    have hdet : rowTransform_0440.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate.bottomBound.transformTopRows rowTransform_0440 hU
  have hcols := hrows.permuteColumns columnPerm_0440
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0440 MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Base.explicitTop)
          columnPerm_0440 = targetTop_0440 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0440 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 3 4 4)) 9 := by
  have htop : targetTop_0440 =
      topOfPattern (R := ℤ) (angle6 0 1 2 3 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0440

/-- Explicit target top block for canonical pattern `(0, 1, 2, 3, 4, 5)`. -/
def targetTop_0441 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 0, 1;
     0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0441 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0441 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0441 : BottomDetBound targetTop_0441 9 := by
  have hU : rowTransform_0441.det.natAbs = 1 := by
    have hdet : rowTransform_0441.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R017.Aggregate.bottomBound.transformTopRows rowTransform_0441 hU
  have hcols := hrows.permuteColumns columnPerm_0441
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0441 MainTheory.Generated.BinaryBetaSixKernel.Representative.R017.Base.explicitTop)
          columnPerm_0441 = targetTop_0441 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0441 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 3 4 5)) 9 := by
  have htop : targetTop_0441 =
      topOfPattern (R := ℤ) (angle6 0 1 2 3 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0441

/-- Explicit target top block for canonical pattern `(0, 1, 2, 3, 4, 6)`. -/
def targetTop_0442 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 0, 0;
     0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0442 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_0442 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 1, 3, 4, 5]
  invFun := ![0, 2, 1, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0442 : BottomDetBound targetTop_0442 9 := by
  have hU : rowTransform_0442.det.natAbs = 1 := by
    have hdet : rowTransform_0442.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R017.Aggregate.bottomBound.transformTopRows rowTransform_0442 hU
  have hcols := hrows.permuteColumns columnPerm_0442
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0442 MainTheory.Generated.BinaryBetaSixKernel.Representative.R017.Base.explicitTop)
          columnPerm_0442 = targetTop_0442 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0442 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 3 4 6)) 9 := by
  have htop : targetTop_0442 =
      topOfPattern (R := ℤ) (angle6 0 1 2 3 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0442

/-- Explicit target top block for canonical pattern `(0, 1, 2, 3, 4, 7)`. -/
def targetTop_0443 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 0, 1;
     0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0443 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0443 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0443 : BottomDetBound targetTop_0443 9 := by
  have hU : rowTransform_0443.det.natAbs = 1 := by
    have hdet : rowTransform_0443.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R018.Aggregate.bottomBound.transformTopRows rowTransform_0443 hU
  have hcols := hrows.permuteColumns columnPerm_0443
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0443 MainTheory.Generated.BinaryBetaSixKernel.Representative.R018.Base.explicitTop)
          columnPerm_0443 = targetTop_0443 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0443 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 3 4 7)) 9 := by
  have htop : targetTop_0443 =
      topOfPattern (R := ℤ) (angle6 0 1 2 3 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0443

/-- Explicit target top block for canonical pattern `(0, 1, 2, 3, 5, 5)`. -/
def targetTop_0444 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0444 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_0444 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 4, 5, 1, 2]
  invFun := ![0, 4, 5, 1, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0444 : BottomDetBound targetTop_0444 9 := by
  have hU : rowTransform_0444.det.natAbs = 1 := by
    have hdet : rowTransform_0444.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate.bottomBound.transformTopRows rowTransform_0444 hU
  have hcols := hrows.permuteColumns columnPerm_0444
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0444 MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Base.explicitTop)
          columnPerm_0444 = targetTop_0444 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0444 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 3 5 5)) 9 := by
  have htop : targetTop_0444 =
      topOfPattern (R := ℤ) (angle6 0 1 2 3 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0444

/-- Explicit target top block for canonical pattern `(0, 1, 2, 3, 5, 6)`. -/
def targetTop_0445 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 1, 0;
     0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0445 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0445 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0445 : BottomDetBound targetTop_0445 9 := by
  have hU : rowTransform_0445.det.natAbs = 1 := by
    have hdet : rowTransform_0445.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R019.Aggregate.bottomBound.transformTopRows rowTransform_0445 hU
  have hcols := hrows.permuteColumns columnPerm_0445
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0445 MainTheory.Generated.BinaryBetaSixKernel.Representative.R019.Base.explicitTop)
          columnPerm_0445 = targetTop_0445 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0445 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 3 5 6)) 9 := by
  have htop : targetTop_0445 =
      topOfPattern (R := ℤ) (angle6 0 1 2 3 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0445

/-- Explicit target top block for canonical pattern `(0, 1, 2, 3, 5, 7)`. -/
def targetTop_0446 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0446 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 0;
     0, 0, 1]

def columnPerm_0446 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 1, 3, 4, 5]
  invFun := ![0, 2, 1, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0446 : BottomDetBound targetTop_0446 9 := by
  have hU : rowTransform_0446.det.natAbs = 1 := by
    have hdet : rowTransform_0446.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R017.Aggregate.bottomBound.transformTopRows rowTransform_0446 hU
  have hcols := hrows.permuteColumns columnPerm_0446
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0446 MainTheory.Generated.BinaryBetaSixKernel.Representative.R017.Base.explicitTop)
          columnPerm_0446 = targetTop_0446 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0446 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 3 5 7)) 9 := by
  have htop : targetTop_0446 =
      topOfPattern (R := ℤ) (angle6 0 1 2 3 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0446

/-- Explicit target top block for canonical pattern `(0, 1, 2, 3, 6, 6)`. -/
def targetTop_0447 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 0, 0;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0447 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 1;
     1, 0, 0]

def columnPerm_0447 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 4, 5, 1, 2]
  invFun := ![0, 4, 5, 1, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0447 : BottomDetBound targetTop_0447 9 := by
  have hU : rowTransform_0447.det.natAbs = 1 := by
    have hdet : rowTransform_0447.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate.bottomBound.transformTopRows rowTransform_0447 hU
  have hcols := hrows.permuteColumns columnPerm_0447
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0447 MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Base.explicitTop)
          columnPerm_0447 = targetTop_0447 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0447 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 3 6 6)) 9 := by
  have htop : targetTop_0447 =
      topOfPattern (R := ℤ) (angle6 0 1 2 3 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0447

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard027
