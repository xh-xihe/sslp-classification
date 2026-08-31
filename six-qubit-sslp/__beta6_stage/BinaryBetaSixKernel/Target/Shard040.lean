-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R017.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard040

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(0, 2, 4, 4, 7, 7)`. -/
def targetTop_0640 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0640 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 1, 1;
     1, 1, 0]

def columnPerm_0640 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0640 : BottomDetBound targetTop_0640 9 := by
  have hU : rowTransform_0640.det.natAbs = 1 := by
    have hdet : rowTransform_0640.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0640 hU
  have hcols := hrows.permuteColumns columnPerm_0640
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0640 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0640 = targetTop_0640 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0640 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 4 4 7 7)) 9 := by
  have htop : targetTop_0640 =
      topOfPattern (R := ℤ) (angle6 0 2 4 4 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0640

/-- Explicit target top block for canonical pattern `(0, 2, 4, 5, 5, 5)`. -/
def targetTop_0641 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0641 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     1, 0, 1]

def columnPerm_0641 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0641 : BottomDetBound targetTop_0641 9 := by
  have hU : rowTransform_0641.det.natAbs = 1 := by
    have hdet : rowTransform_0641.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0641 hU
  have hcols := hrows.permuteColumns columnPerm_0641
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0641 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0641 = targetTop_0641 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0641 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 4 5 5 5)) 9 := by
  have htop : targetTop_0641 =
      topOfPattern (R := ℤ) (angle6 0 2 4 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0641

/-- Explicit target top block for canonical pattern `(0, 2, 4, 5, 5, 6)`. -/
def targetTop_0642 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 0;
     0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0642 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     1, 0, 1]

def columnPerm_0642 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 4, 1, 2, 5]
  invFun := ![0, 3, 4, 1, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0642 : BottomDetBound targetTop_0642 9 := by
  have hU : rowTransform_0642.det.natAbs = 1 := by
    have hdet : rowTransform_0642.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate.bottomBound.transformTopRows rowTransform_0642 hU
  have hcols := hrows.permuteColumns columnPerm_0642
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0642 MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Base.explicitTop)
          columnPerm_0642 = targetTop_0642 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0642 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 4 5 5 6)) 9 := by
  have htop : targetTop_0642 =
      topOfPattern (R := ℤ) (angle6 0 2 4 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0642

/-- Explicit target top block for canonical pattern `(0, 2, 4, 5, 5, 7)`. -/
def targetTop_0643 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0643 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     1, 0, 1]

def columnPerm_0643 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 5, 1, 2, 4]
  invFun := ![0, 3, 4, 1, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0643 : BottomDetBound targetTop_0643 9 := by
  have hU : rowTransform_0643.det.natAbs = 1 := by
    have hdet : rowTransform_0643.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0643 hU
  have hcols := hrows.permuteColumns columnPerm_0643
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0643 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0643 = targetTop_0643 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0643 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 4 5 5 7)) 9 := by
  have htop : targetTop_0643 =
      topOfPattern (R := ℤ) (angle6 0 2 4 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0643

/-- Explicit target top block for canonical pattern `(0, 2, 4, 5, 6, 6)`. -/
def targetTop_0644 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 0;
     0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0644 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 1]

def columnPerm_0644 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0644 : BottomDetBound targetTop_0644 9 := by
  have hU : rowTransform_0644.det.natAbs = 1 := by
    have hdet : rowTransform_0644.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Aggregate.bottomBound.transformTopRows rowTransform_0644 hU
  have hcols := hrows.permuteColumns columnPerm_0644
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0644 MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Base.explicitTop)
          columnPerm_0644 = targetTop_0644 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0644 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 4 5 6 6)) 9 := by
  have htop : targetTop_0644 =
      topOfPattern (R := ℤ) (angle6 0 2 4 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0644

/-- Explicit target top block for canonical pattern `(0, 2, 4, 5, 6, 7)`. -/
def targetTop_0645 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 1;
     0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0645 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 1]

def columnPerm_0645 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 4, 3, 5]
  invFun := ![0, 1, 2, 4, 3, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0645 : BottomDetBound targetTop_0645 9 := by
  have hU : rowTransform_0645.det.natAbs = 1 := by
    have hdet : rowTransform_0645.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R017.Aggregate.bottomBound.transformTopRows rowTransform_0645 hU
  have hcols := hrows.permuteColumns columnPerm_0645
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0645 MainTheory.Generated.BinaryBetaSixKernel.Representative.R017.Base.explicitTop)
          columnPerm_0645 = targetTop_0645 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0645 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 4 5 6 7)) 9 := by
  have htop : targetTop_0645 =
      topOfPattern (R := ℤ) (angle6 0 2 4 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0645

/-- Explicit target top block for canonical pattern `(0, 2, 4, 5, 7, 7)`. -/
def targetTop_0646 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0646 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 1, 1]

def columnPerm_0646 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0646 : BottomDetBound targetTop_0646 9 := by
  have hU : rowTransform_0646.det.natAbs = 1 := by
    have hdet : rowTransform_0646.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Aggregate.bottomBound.transformTopRows rowTransform_0646 hU
  have hcols := hrows.permuteColumns columnPerm_0646
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0646 MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Base.explicitTop)
          columnPerm_0646 = targetTop_0646 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0646 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 4 5 7 7)) 9 := by
  have htop : targetTop_0646 =
      topOfPattern (R := ℤ) (angle6 0 2 4 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0646

/-- Explicit rank-deficient target for canonical pattern `(0, 2, 4, 6, 6, 6)`. -/
def targetTop_0647 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0647 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0647 :
    TopRowRelation targetTop_0647 relationCoefficients_0647 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0647, relationCoefficients_0647, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0647 : BottomDetBound targetTop_0647 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0647

theorem canonicalBound_0647 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 4 6 6 6)) 9 := by
  have htop : targetTop_0647 =
      topOfPattern (R := ℤ) (angle6 0 2 4 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0647

/-- Explicit target top block for canonical pattern `(0, 2, 4, 6, 6, 7)`. -/
def targetTop_0648 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0648 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 1;
     0, 1, 1]

def columnPerm_0648 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0648 : BottomDetBound targetTop_0648 9 := by
  have hU : rowTransform_0648.det.natAbs = 1 := by
    have hdet : rowTransform_0648.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Aggregate.bottomBound.transformTopRows rowTransform_0648 hU
  have hcols := hrows.permuteColumns columnPerm_0648
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0648 MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Base.explicitTop)
          columnPerm_0648 = targetTop_0648 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0648 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 4 6 6 7)) 9 := by
  have htop : targetTop_0648 =
      topOfPattern (R := ℤ) (angle6 0 2 4 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0648

/-- Explicit target top block for canonical pattern `(0, 2, 4, 6, 7, 7)`. -/
def targetTop_0649 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0649 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, 0;
     1, 0, 1]

def columnPerm_0649 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 4, 5, 1, 2]
  invFun := ![0, 4, 5, 1, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0649 : BottomDetBound targetTop_0649 9 := by
  have hU : rowTransform_0649.det.natAbs = 1 := by
    have hdet : rowTransform_0649.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate.bottomBound.transformTopRows rowTransform_0649 hU
  have hcols := hrows.permuteColumns columnPerm_0649
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0649 MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Base.explicitTop)
          columnPerm_0649 = targetTop_0649 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0649 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 4 6 7 7)) 9 := by
  have htop : targetTop_0649 =
      topOfPattern (R := ℤ) (angle6 0 2 4 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0649

/-- Explicit target top block for canonical pattern `(0, 2, 4, 7, 7, 7)`. -/
def targetTop_0650 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0650 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, 0;
     1, 0, 1]

def columnPerm_0650 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0650 : BottomDetBound targetTop_0650 9 := by
  have hU : rowTransform_0650.det.natAbs = 1 := by
    have hdet : rowTransform_0650.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0650 hU
  have hcols := hrows.permuteColumns columnPerm_0650
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0650 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0650 = targetTop_0650 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0650 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 4 7 7 7)) 9 := by
  have htop : targetTop_0650 =
      topOfPattern (R := ℤ) (angle6 0 2 4 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0650

/-- Explicit rank-deficient target for canonical pattern `(0, 2, 5, 5, 5, 5)`. -/
def targetTop_0651 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0651 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0651 :
    TopRowRelation targetTop_0651 relationCoefficients_0651 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0651, relationCoefficients_0651, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0651 : BottomDetBound targetTop_0651 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0651

theorem canonicalBound_0651 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 5 5 5 5)) 9 := by
  have htop : targetTop_0651 =
      topOfPattern (R := ℤ) (angle6 0 2 5 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0651

/-- Explicit target top block for canonical pattern `(0, 2, 5, 5, 5, 6)`. -/
def targetTop_0652 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 0;
     0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0652 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     1, 0, 1]

def columnPerm_0652 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 3, 5]
  invFun := ![0, 2, 3, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0652 : BottomDetBound targetTop_0652 9 := by
  have hU : rowTransform_0652.det.natAbs = 1 := by
    have hdet : rowTransform_0652.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0652 hU
  have hcols := hrows.permuteColumns columnPerm_0652
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0652 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0652 = targetTop_0652 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0652 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 5 5 5 6)) 9 := by
  have htop : targetTop_0652 =
      topOfPattern (R := ℤ) (angle6 0 2 5 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0652

/-- Explicit rank-deficient target for canonical pattern `(0, 2, 5, 5, 5, 7)`. -/
def targetTop_0653 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0653 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0653 :
    TopRowRelation targetTop_0653 relationCoefficients_0653 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0653, relationCoefficients_0653, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0653 : BottomDetBound targetTop_0653 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0653

theorem canonicalBound_0653 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 5 5 5 7)) 9 := by
  have htop : targetTop_0653 =
      topOfPattern (R := ℤ) (angle6 0 2 5 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0653

/-- Explicit target top block for canonical pattern `(0, 2, 5, 5, 6, 6)`. -/
def targetTop_0654 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 0;
     0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0654 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     1, 1, 0]

def columnPerm_0654 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0654 : BottomDetBound targetTop_0654 9 := by
  have hU : rowTransform_0654.det.natAbs = 1 := by
    have hdet : rowTransform_0654.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0654 hU
  have hcols := hrows.permuteColumns columnPerm_0654
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0654 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0654 = targetTop_0654 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0654 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 5 5 6 6)) 9 := by
  have htop : targetTop_0654 =
      topOfPattern (R := ℤ) (angle6 0 2 5 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0654

/-- Explicit target top block for canonical pattern `(0, 2, 5, 5, 6, 7)`. -/
def targetTop_0655 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 1;
     0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0655 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     1, 0, 1]

def columnPerm_0655 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 5, 4]
  invFun := ![0, 2, 3, 1, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0655 : BottomDetBound targetTop_0655 9 := by
  have hU : rowTransform_0655.det.natAbs = 1 := by
    have hdet : rowTransform_0655.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0655 hU
  have hcols := hrows.permuteColumns columnPerm_0655
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0655 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0655 = targetTop_0655 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0655 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 5 5 6 7)) 9 := by
  have htop : targetTop_0655 =
      topOfPattern (R := ℤ) (angle6 0 2 5 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0655

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard040
