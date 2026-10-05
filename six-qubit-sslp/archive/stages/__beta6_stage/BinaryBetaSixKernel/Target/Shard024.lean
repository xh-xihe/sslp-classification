-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R015.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard024

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(0, 1, 1, 3, 4, 4)`. -/
def targetTop_0384 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0384 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 0, 1;
     0, 1, 0]

def columnPerm_0384 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0384 : BottomDetBound targetTop_0384 9 := by
  have hU : rowTransform_0384.det.natAbs = 1 := by
    have hdet : rowTransform_0384.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0384 hU
  have hcols := hrows.permuteColumns columnPerm_0384
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0384 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0384 = targetTop_0384 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0384 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 3 4 4)) 9 := by
  have htop : targetTop_0384 =
      topOfPattern (R := ℤ) (angle6 0 1 1 3 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0384

/-- Explicit target top block for canonical pattern `(0, 1, 1, 3, 4, 5)`. -/
def targetTop_0385 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 1;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0385 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 0, 1;
     0, 1, 0]

def columnPerm_0385 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0385 : BottomDetBound targetTop_0385 9 := by
  have hU : rowTransform_0385.det.natAbs = 1 := by
    have hdet : rowTransform_0385.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0385 hU
  have hcols := hrows.permuteColumns columnPerm_0385
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0385 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0385 = targetTop_0385 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0385 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 3 4 5)) 9 := by
  have htop : targetTop_0385 =
      topOfPattern (R := ℤ) (angle6 0 1 1 3 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0385

/-- Explicit target top block for canonical pattern `(0, 1, 1, 3, 4, 6)`. -/
def targetTop_0386 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 0;
     0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0386 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, (-1);
     0, 1, 0;
     0, 0, 1]

def columnPerm_0386 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0386 : BottomDetBound targetTop_0386 9 := by
  have hU : rowTransform_0386.det.natAbs = 1 := by
    have hdet : rowTransform_0386.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Aggregate.bottomBound.transformTopRows rowTransform_0386 hU
  have hcols := hrows.permuteColumns columnPerm_0386
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0386 MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Base.explicitTop)
          columnPerm_0386 = targetTop_0386 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0386 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 3 4 6)) 9 := by
  have htop : targetTop_0386 =
      topOfPattern (R := ℤ) (angle6 0 1 1 3 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0386

/-- Explicit target top block for canonical pattern `(0, 1, 1, 3, 4, 7)`. -/
def targetTop_0387 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 1;
     0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0387 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0387 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0387 : BottomDetBound targetTop_0387 9 := by
  have hU : rowTransform_0387.det.natAbs = 1 := by
    have hdet : rowTransform_0387.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate.bottomBound.transformTopRows rowTransform_0387 hU
  have hcols := hrows.permuteColumns columnPerm_0387
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0387 MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Base.explicitTop)
          columnPerm_0387 = targetTop_0387 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0387 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 3 4 7)) 9 := by
  have htop : targetTop_0387 =
      topOfPattern (R := ℤ) (angle6 0 1 1 3 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0387

/-- Explicit target top block for canonical pattern `(0, 1, 1, 3, 5, 5)`. -/
def targetTop_0388 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0388 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 0, 1;
     0, 1, 0]

def columnPerm_0388 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0388 : BottomDetBound targetTop_0388 9 := by
  have hU : rowTransform_0388.det.natAbs = 1 := by
    have hdet : rowTransform_0388.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0388 hU
  have hcols := hrows.permuteColumns columnPerm_0388
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0388 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0388 = targetTop_0388 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0388 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 3 5 5)) 9 := by
  have htop : targetTop_0388 =
      topOfPattern (R := ℤ) (angle6 0 1 1 3 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0388

/-- Explicit target top block for canonical pattern `(0, 1, 1, 3, 5, 6)`. -/
def targetTop_0389 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 0;
     0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0389 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0389 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0389 : BottomDetBound targetTop_0389 9 := by
  have hU : rowTransform_0389.det.natAbs = 1 := by
    have hdet : rowTransform_0389.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R015.Aggregate.bottomBound.transformTopRows rowTransform_0389 hU
  have hcols := hrows.permuteColumns columnPerm_0389
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0389 MainTheory.Generated.BinaryBetaSixKernel.Representative.R015.Base.explicitTop)
          columnPerm_0389 = targetTop_0389 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0389 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 3 5 6)) 9 := by
  have htop : targetTop_0389 =
      topOfPattern (R := ℤ) (angle6 0 1 1 3 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0389

/-- Explicit target top block for canonical pattern `(0, 1, 1, 3, 5, 7)`. -/
def targetTop_0390 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0390 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0390 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0390 : BottomDetBound targetTop_0390 9 := by
  have hU : rowTransform_0390.det.natAbs = 1 := by
    have hdet : rowTransform_0390.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Aggregate.bottomBound.transformTopRows rowTransform_0390 hU
  have hcols := hrows.permuteColumns columnPerm_0390
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0390 MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Base.explicitTop)
          columnPerm_0390 = targetTop_0390 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0390 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 3 5 7)) 9 := by
  have htop : targetTop_0390 =
      topOfPattern (R := ℤ) (angle6 0 1 1 3 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0390

/-- Explicit target top block for canonical pattern `(0, 1, 1, 3, 6, 6)`. -/
def targetTop_0391 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 0;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0391 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 1;
     0, 1, 0]

def columnPerm_0391 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0391 : BottomDetBound targetTop_0391 9 := by
  have hU : rowTransform_0391.det.natAbs = 1 := by
    have hdet : rowTransform_0391.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0391 hU
  have hcols := hrows.permuteColumns columnPerm_0391
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0391 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0391 = targetTop_0391 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0391 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 3 6 6)) 9 := by
  have htop : targetTop_0391 =
      topOfPattern (R := ℤ) (angle6 0 1 1 3 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0391

/-- Explicit target top block for canonical pattern `(0, 1, 1, 3, 6, 7)`. -/
def targetTop_0392 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0392 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 1;
     0, 1, 0]

def columnPerm_0392 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0392 : BottomDetBound targetTop_0392 9 := by
  have hU : rowTransform_0392.det.natAbs = 1 := by
    have hdet : rowTransform_0392.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0392 hU
  have hcols := hrows.permuteColumns columnPerm_0392
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0392 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0392 = targetTop_0392 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0392 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 3 6 7)) 9 := by
  have htop : targetTop_0392 =
      topOfPattern (R := ℤ) (angle6 0 1 1 3 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0392

/-- Explicit target top block for canonical pattern `(0, 1, 1, 3, 7, 7)`. -/
def targetTop_0393 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0393 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 1, 1;
     0, 1, 0]

def columnPerm_0393 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0393 : BottomDetBound targetTop_0393 9 := by
  have hU : rowTransform_0393.det.natAbs = 1 := by
    have hdet : rowTransform_0393.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0393 hU
  have hcols := hrows.permuteColumns columnPerm_0393
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0393 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0393 = targetTop_0393 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0393 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 3 7 7)) 9 := by
  have htop : targetTop_0393 =
      topOfPattern (R := ℤ) (angle6 0 1 1 3 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0393

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 1, 4, 4, 4)`. -/
def targetTop_0394 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0394 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0394 :
    TopRowRelation targetTop_0394 relationCoefficients_0394 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0394, relationCoefficients_0394, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0394 : BottomDetBound targetTop_0394 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0394

theorem canonicalBound_0394 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 4 4 4)) 9 := by
  have htop : targetTop_0394 =
      topOfPattern (R := ℤ) (angle6 0 1 1 4 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0394

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 1, 4, 4, 5)`. -/
def targetTop_0395 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0395 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0395 :
    TopRowRelation targetTop_0395 relationCoefficients_0395 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0395, relationCoefficients_0395, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0395 : BottomDetBound targetTop_0395 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0395

theorem canonicalBound_0395 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 4 4 5)) 9 := by
  have htop : targetTop_0395 =
      topOfPattern (R := ℤ) (angle6 0 1 1 4 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0395

/-- Explicit target top block for canonical pattern `(0, 1, 1, 4, 4, 6)`. -/
def targetTop_0396 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0396 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0396 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0396 : BottomDetBound targetTop_0396 9 := by
  have hU : rowTransform_0396.det.natAbs = 1 := by
    have hdet : rowTransform_0396.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0396 hU
  have hcols := hrows.permuteColumns columnPerm_0396
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0396 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0396 = targetTop_0396 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0396 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 4 4 6)) 9 := by
  have htop : targetTop_0396 =
      topOfPattern (R := ℤ) (angle6 0 1 1 4 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0396

/-- Explicit target top block for canonical pattern `(0, 1, 1, 4, 4, 7)`. -/
def targetTop_0397 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0397 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0397 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0397 : BottomDetBound targetTop_0397 9 := by
  have hU : rowTransform_0397.det.natAbs = 1 := by
    have hdet : rowTransform_0397.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0397 hU
  have hcols := hrows.permuteColumns columnPerm_0397
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0397 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0397 = targetTop_0397 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0397 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 4 4 7)) 9 := by
  have htop : targetTop_0397 =
      topOfPattern (R := ℤ) (angle6 0 1 1 4 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0397

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 1, 4, 5, 5)`. -/
def targetTop_0398 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0398 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0398 :
    TopRowRelation targetTop_0398 relationCoefficients_0398 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0398, relationCoefficients_0398, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0398 : BottomDetBound targetTop_0398 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0398

theorem canonicalBound_0398 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 4 5 5)) 9 := by
  have htop : targetTop_0398 =
      topOfPattern (R := ℤ) (angle6 0 1 1 4 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0398

/-- Explicit target top block for canonical pattern `(0, 1, 1, 4, 5, 6)`. -/
def targetTop_0399 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0399 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0399 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0399 : BottomDetBound targetTop_0399 9 := by
  have hU : rowTransform_0399.det.natAbs = 1 := by
    have hdet : rowTransform_0399.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0399 hU
  have hcols := hrows.permuteColumns columnPerm_0399
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0399 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0399 = targetTop_0399 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0399 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 4 5 6)) 9 := by
  have htop : targetTop_0399 =
      topOfPattern (R := ℤ) (angle6 0 1 1 4 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0399

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard024
