-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard036

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit rank-deficient target for canonical pattern `(0, 2, 2, 4, 4, 4)`. -/
def targetTop_0576 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0576 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0576 :
    TopRowRelation targetTop_0576 relationCoefficients_0576 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0576, relationCoefficients_0576, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0576 : BottomDetBound targetTop_0576 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0576

theorem canonicalBound_0576 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 4 4 4)) 9 := by
  have htop : targetTop_0576 =
      topOfPattern (R := ℤ) (angle6 0 2 2 4 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0576

/-- Explicit target top block for canonical pattern `(0, 2, 2, 4, 4, 5)`. -/
def targetTop_0577 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0577 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 1]

def columnPerm_0577 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0577 : BottomDetBound targetTop_0577 9 := by
  have hU : rowTransform_0577.det.natAbs = 1 := by
    have hdet : rowTransform_0577.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0577 hU
  have hcols := hrows.permuteColumns columnPerm_0577
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0577 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0577 = targetTop_0577 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0577 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 4 4 5)) 9 := by
  have htop : targetTop_0577 =
      topOfPattern (R := ℤ) (angle6 0 2 2 4 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0577

/-- Explicit rank-deficient target for canonical pattern `(0, 2, 2, 4, 4, 6)`. -/
def targetTop_0578 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0578 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0578 :
    TopRowRelation targetTop_0578 relationCoefficients_0578 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0578, relationCoefficients_0578, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0578 : BottomDetBound targetTop_0578 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0578

theorem canonicalBound_0578 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 4 4 6)) 9 := by
  have htop : targetTop_0578 =
      topOfPattern (R := ℤ) (angle6 0 2 2 4 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0578

/-- Explicit target top block for canonical pattern `(0, 2, 2, 4, 4, 7)`. -/
def targetTop_0579 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0579 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 1;
     0, 1, 1]

def columnPerm_0579 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0579 : BottomDetBound targetTop_0579 9 := by
  have hU : rowTransform_0579.det.natAbs = 1 := by
    have hdet : rowTransform_0579.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0579 hU
  have hcols := hrows.permuteColumns columnPerm_0579
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0579 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0579 = targetTop_0579 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0579 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 4 4 7)) 9 := by
  have htop : targetTop_0579 =
      topOfPattern (R := ℤ) (angle6 0 2 2 4 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0579

/-- Explicit target top block for canonical pattern `(0, 2, 2, 4, 5, 5)`. -/
def targetTop_0580 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0580 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 1, 1]

def columnPerm_0580 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0580 : BottomDetBound targetTop_0580 9 := by
  have hU : rowTransform_0580.det.natAbs = 1 := by
    have hdet : rowTransform_0580.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0580 hU
  have hcols := hrows.permuteColumns columnPerm_0580
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0580 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0580 = targetTop_0580 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0580 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 4 5 5)) 9 := by
  have htop : targetTop_0580 =
      topOfPattern (R := ℤ) (angle6 0 2 2 4 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0580

/-- Explicit target top block for canonical pattern `(0, 2, 2, 4, 5, 6)`. -/
def targetTop_0581 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 0;
     0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0581 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 1]

def columnPerm_0581 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 5, 4]
  invFun := ![0, 1, 2, 3, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0581 : BottomDetBound targetTop_0581 9 := by
  have hU : rowTransform_0581.det.natAbs = 1 := by
    have hdet : rowTransform_0581.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0581 hU
  have hcols := hrows.permuteColumns columnPerm_0581
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0581 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0581 = targetTop_0581 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0581 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 4 5 6)) 9 := by
  have htop : targetTop_0581 =
      topOfPattern (R := ℤ) (angle6 0 2 2 4 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0581

/-- Explicit target top block for canonical pattern `(0, 2, 2, 4, 5, 7)`. -/
def targetTop_0582 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0582 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 1, 1]

def columnPerm_0582 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0582 : BottomDetBound targetTop_0582 9 := by
  have hU : rowTransform_0582.det.natAbs = 1 := by
    have hdet : rowTransform_0582.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0582 hU
  have hcols := hrows.permuteColumns columnPerm_0582
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0582 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0582 = targetTop_0582 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0582 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 4 5 7)) 9 := by
  have htop : targetTop_0582 =
      topOfPattern (R := ℤ) (angle6 0 2 2 4 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0582

/-- Explicit rank-deficient target for canonical pattern `(0, 2, 2, 4, 6, 6)`. -/
def targetTop_0583 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0583 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0583 :
    TopRowRelation targetTop_0583 relationCoefficients_0583 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0583, relationCoefficients_0583, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0583 : BottomDetBound targetTop_0583 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0583

theorem canonicalBound_0583 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 4 6 6)) 9 := by
  have htop : targetTop_0583 =
      topOfPattern (R := ℤ) (angle6 0 2 2 4 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0583

/-- Explicit target top block for canonical pattern `(0, 2, 2, 4, 6, 7)`. -/
def targetTop_0584 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0584 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 1;
     0, 1, 1]

def columnPerm_0584 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0584 : BottomDetBound targetTop_0584 9 := by
  have hU : rowTransform_0584.det.natAbs = 1 := by
    have hdet : rowTransform_0584.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0584 hU
  have hcols := hrows.permuteColumns columnPerm_0584
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0584 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0584 = targetTop_0584 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0584 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 4 6 7)) 9 := by
  have htop : targetTop_0584 =
      topOfPattern (R := ℤ) (angle6 0 2 2 4 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0584

/-- Explicit target top block for canonical pattern `(0, 2, 2, 4, 7, 7)`. -/
def targetTop_0585 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0585 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 0;
     0, 1, 1]

def columnPerm_0585 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0585 : BottomDetBound targetTop_0585 9 := by
  have hU : rowTransform_0585.det.natAbs = 1 := by
    have hdet : rowTransform_0585.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0585 hU
  have hcols := hrows.permuteColumns columnPerm_0585
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0585 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0585 = targetTop_0585 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0585 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 4 7 7)) 9 := by
  have htop : targetTop_0585 =
      topOfPattern (R := ℤ) (angle6 0 2 2 4 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0585

/-- Explicit rank-deficient target for canonical pattern `(0, 2, 2, 5, 5, 5)`. -/
def targetTop_0586 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0586 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0586 :
    TopRowRelation targetTop_0586 relationCoefficients_0586 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0586, relationCoefficients_0586, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0586 : BottomDetBound targetTop_0586 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0586

theorem canonicalBound_0586 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 5 5 5)) 9 := by
  have htop : targetTop_0586 =
      topOfPattern (R := ℤ) (angle6 0 2 2 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0586

/-- Explicit target top block for canonical pattern `(0, 2, 2, 5, 5, 6)`. -/
def targetTop_0587 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 0;
     0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0587 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 1;
     0, 1, 1]

def columnPerm_0587 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0587 : BottomDetBound targetTop_0587 9 := by
  have hU : rowTransform_0587.det.natAbs = 1 := by
    have hdet : rowTransform_0587.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0587 hU
  have hcols := hrows.permuteColumns columnPerm_0587
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0587 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0587 = targetTop_0587 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0587 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 5 5 6)) 9 := by
  have htop : targetTop_0587 =
      topOfPattern (R := ℤ) (angle6 0 2 2 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0587

/-- Explicit rank-deficient target for canonical pattern `(0, 2, 2, 5, 5, 7)`. -/
def targetTop_0588 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0588 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0588 :
    TopRowRelation targetTop_0588 relationCoefficients_0588 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0588, relationCoefficients_0588, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0588 : BottomDetBound targetTop_0588 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0588

theorem canonicalBound_0588 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 5 5 7)) 9 := by
  have htop : targetTop_0588 =
      topOfPattern (R := ℤ) (angle6 0 2 2 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0588

/-- Explicit target top block for canonical pattern `(0, 2, 2, 5, 6, 6)`. -/
def targetTop_0589 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 0;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0589 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, 0;
     0, 1, 1]

def columnPerm_0589 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0589 : BottomDetBound targetTop_0589 9 := by
  have hU : rowTransform_0589.det.natAbs = 1 := by
    have hdet : rowTransform_0589.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0589 hU
  have hcols := hrows.permuteColumns columnPerm_0589
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0589 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0589 = targetTop_0589 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0589 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 5 6 6)) 9 := by
  have htop : targetTop_0589 =
      topOfPattern (R := ℤ) (angle6 0 2 2 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0589

/-- Explicit target top block for canonical pattern `(0, 2, 2, 5, 6, 7)`. -/
def targetTop_0590 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 1;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0590 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 1;
     0, 1, 1]

def columnPerm_0590 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 5, 4]
  invFun := ![0, 1, 2, 3, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0590 : BottomDetBound targetTop_0590 9 := by
  have hU : rowTransform_0590.det.natAbs = 1 := by
    have hdet : rowTransform_0590.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0590 hU
  have hcols := hrows.permuteColumns columnPerm_0590
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0590 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0590 = targetTop_0590 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0590 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 5 6 7)) 9 := by
  have htop : targetTop_0590 =
      topOfPattern (R := ℤ) (angle6 0 2 2 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0590

/-- Explicit rank-deficient target for canonical pattern `(0, 2, 2, 5, 7, 7)`. -/
def targetTop_0591 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0591 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0591 :
    TopRowRelation targetTop_0591 relationCoefficients_0591 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0591, relationCoefficients_0591, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0591 : BottomDetBound targetTop_0591 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0591

theorem canonicalBound_0591 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 5 7 7)) 9 := by
  have htop : targetTop_0591 =
      topOfPattern (R := ℤ) (angle6 0 2 2 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0591

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard036
