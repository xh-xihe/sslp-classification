-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R022.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard037

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit rank-deficient target for canonical pattern `(0, 2, 2, 6, 6, 6)`. -/
def targetTop_0592 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0592 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0592 :
    TopRowRelation targetTop_0592 relationCoefficients_0592 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0592, relationCoefficients_0592, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0592 : BottomDetBound targetTop_0592 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0592

theorem canonicalBound_0592 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 6 6 6)) 9 := by
  have htop : targetTop_0592 =
      topOfPattern (R := ℤ) (angle6 0 2 2 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0592

/-- Explicit target top block for canonical pattern `(0, 2, 2, 6, 6, 7)`. -/
def targetTop_0593 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0593 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, 1;
     0, 1, 1]

def columnPerm_0593 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0593 : BottomDetBound targetTop_0593 9 := by
  have hU : rowTransform_0593.det.natAbs = 1 := by
    have hdet : rowTransform_0593.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0593 hU
  have hcols := hrows.permuteColumns columnPerm_0593
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0593 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0593 = targetTop_0593 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0593 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 6 6 7)) 9 := by
  have htop : targetTop_0593 =
      topOfPattern (R := ℤ) (angle6 0 2 2 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0593

/-- Explicit target top block for canonical pattern `(0, 2, 2, 6, 7, 7)`. -/
def targetTop_0594 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0594 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 1;
     0, 1, 1]

def columnPerm_0594 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0594 : BottomDetBound targetTop_0594 9 := by
  have hU : rowTransform_0594.det.natAbs = 1 := by
    have hdet : rowTransform_0594.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0594 hU
  have hcols := hrows.permuteColumns columnPerm_0594
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0594 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0594 = targetTop_0594 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0594 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 6 7 7)) 9 := by
  have htop : targetTop_0594 =
      topOfPattern (R := ℤ) (angle6 0 2 2 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0594

/-- Explicit rank-deficient target for canonical pattern `(0, 2, 2, 7, 7, 7)`. -/
def targetTop_0595 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0595 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0595 :
    TopRowRelation targetTop_0595 relationCoefficients_0595 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0595, relationCoefficients_0595, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0595 : BottomDetBound targetTop_0595 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0595

theorem canonicalBound_0595 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 7 7 7)) 9 := by
  have htop : targetTop_0595 =
      topOfPattern (R := ℤ) (angle6 0 2 2 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0595

/-- Explicit rank-deficient target for canonical pattern `(0, 2, 3, 3, 3, 3)`. -/
def targetTop_0596 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0596 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0596 :
    TopRowRelation targetTop_0596 relationCoefficients_0596 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0596, relationCoefficients_0596, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0596 : BottomDetBound targetTop_0596 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0596

theorem canonicalBound_0596 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 3 3 3 3)) 9 := by
  have htop : targetTop_0596 =
      topOfPattern (R := ℤ) (angle6 0 2 3 3 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0596

/-- Explicit target top block for canonical pattern `(0, 2, 3, 3, 3, 4)`. -/
def targetTop_0597 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 0;
     0, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0597 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, 0;
     0, 0, 1]

def columnPerm_0597 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 3, 5]
  invFun := ![0, 2, 3, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0597 : BottomDetBound targetTop_0597 9 := by
  have hU : rowTransform_0597.det.natAbs = 1 := by
    have hdet : rowTransform_0597.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0597 hU
  have hcols := hrows.permuteColumns columnPerm_0597
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0597 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0597 = targetTop_0597 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0597 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 3 3 3 4)) 9 := by
  have htop : targetTop_0597 =
      topOfPattern (R := ℤ) (angle6 0 2 3 3 3 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0597

/-- Explicit target top block for canonical pattern `(0, 2, 3, 3, 3, 5)`. -/
def targetTop_0598 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0598 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 1, 0;
     0, 0, 1]

def columnPerm_0598 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 3, 5]
  invFun := ![0, 2, 3, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0598 : BottomDetBound targetTop_0598 9 := by
  have hU : rowTransform_0598.det.natAbs = 1 := by
    have hdet : rowTransform_0598.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0598 hU
  have hcols := hrows.permuteColumns columnPerm_0598
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0598 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0598 = targetTop_0598 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0598 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 3 3 3 5)) 9 := by
  have htop : targetTop_0598 =
      topOfPattern (R := ℤ) (angle6 0 2 3 3 3 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0598

/-- Explicit target top block for canonical pattern `(0, 2, 3, 3, 3, 6)`. -/
def targetTop_0599 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 0;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0599 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, 1;
     0, 0, 1]

def columnPerm_0599 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 3, 5]
  invFun := ![0, 2, 3, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0599 : BottomDetBound targetTop_0599 9 := by
  have hU : rowTransform_0599.det.natAbs = 1 := by
    have hdet : rowTransform_0599.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0599 hU
  have hcols := hrows.permuteColumns columnPerm_0599
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0599 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0599 = targetTop_0599 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0599 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 3 3 3 6)) 9 := by
  have htop : targetTop_0599 =
      topOfPattern (R := ℤ) (angle6 0 2 3 3 3 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0599

/-- Explicit target top block for canonical pattern `(0, 2, 3, 3, 3, 7)`. -/
def targetTop_0600 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0600 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 1, 1;
     0, 0, 1]

def columnPerm_0600 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 3, 5]
  invFun := ![0, 2, 3, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0600 : BottomDetBound targetTop_0600 9 := by
  have hU : rowTransform_0600.det.natAbs = 1 := by
    have hdet : rowTransform_0600.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0600 hU
  have hcols := hrows.permuteColumns columnPerm_0600
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0600 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0600 = targetTop_0600 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0600 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 3 3 3 7)) 9 := by
  have htop : targetTop_0600 =
      topOfPattern (R := ℤ) (angle6 0 2 3 3 3 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0600

/-- Explicit target top block for canonical pattern `(0, 2, 3, 3, 4, 4)`. -/
def targetTop_0601 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 0;
     0, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0601 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 0, 1;
     0, 1, 0]

def columnPerm_0601 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0601 : BottomDetBound targetTop_0601 9 := by
  have hU : rowTransform_0601.det.natAbs = 1 := by
    have hdet : rowTransform_0601.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0601 hU
  have hcols := hrows.permuteColumns columnPerm_0601
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0601 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0601 = targetTop_0601 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0601 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 3 3 4 4)) 9 := by
  have htop : targetTop_0601 =
      topOfPattern (R := ℤ) (angle6 0 2 3 3 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0601

/-- Explicit target top block for canonical pattern `(0, 2, 3, 3, 4, 5)`. -/
def targetTop_0602 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 1;
     0, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0602 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, (-1);
     0, 0, 1]

def columnPerm_0602 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 5, 4]
  invFun := ![0, 2, 3, 1, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0602 : BottomDetBound targetTop_0602 9 := by
  have hU : rowTransform_0602.det.natAbs = 1 := by
    have hdet : rowTransform_0602.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Aggregate.bottomBound.transformTopRows rowTransform_0602 hU
  have hcols := hrows.permuteColumns columnPerm_0602
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0602 MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Base.explicitTop)
          columnPerm_0602 = targetTop_0602 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0602 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 3 3 4 5)) 9 := by
  have htop : targetTop_0602 =
      topOfPattern (R := ℤ) (angle6 0 2 3 3 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0602

/-- Explicit target top block for canonical pattern `(0, 2, 3, 3, 4, 6)`. -/
def targetTop_0603 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 0;
     0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0603 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, 0;
     0, 0, 1]

def columnPerm_0603 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 4, 5]
  invFun := ![0, 2, 3, 1, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0603 : BottomDetBound targetTop_0603 9 := by
  have hU : rowTransform_0603.det.natAbs = 1 := by
    have hdet : rowTransform_0603.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate.bottomBound.transformTopRows rowTransform_0603 hU
  have hcols := hrows.permuteColumns columnPerm_0603
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0603 MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Base.explicitTop)
          columnPerm_0603 = targetTop_0603 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0603 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 3 3 4 6)) 9 := by
  have htop : targetTop_0603 =
      topOfPattern (R := ℤ) (angle6 0 2 3 3 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0603

/-- Explicit target top block for canonical pattern `(0, 2, 3, 3, 4, 7)`. -/
def targetTop_0604 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 1;
     0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0604 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 0, 1;
     0, 1, 0]

def columnPerm_0604 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0604 : BottomDetBound targetTop_0604 9 := by
  have hU : rowTransform_0604.det.natAbs = 1 := by
    have hdet : rowTransform_0604.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0604 hU
  have hcols := hrows.permuteColumns columnPerm_0604
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0604 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0604 = targetTop_0604 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0604 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 3 3 4 7)) 9 := by
  have htop : targetTop_0604 =
      topOfPattern (R := ℤ) (angle6 0 2 3 3 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0604

/-- Explicit target top block for canonical pattern `(0, 2, 3, 3, 5, 5)`. -/
def targetTop_0605 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0605 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 1;
     0, 1, 0]

def columnPerm_0605 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0605 : BottomDetBound targetTop_0605 9 := by
  have hU : rowTransform_0605.det.natAbs = 1 := by
    have hdet : rowTransform_0605.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0605 hU
  have hcols := hrows.permuteColumns columnPerm_0605
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0605 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0605 = targetTop_0605 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0605 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 3 3 5 5)) 9 := by
  have htop : targetTop_0605 =
      topOfPattern (R := ℤ) (angle6 0 2 3 3 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0605

/-- Explicit target top block for canonical pattern `(0, 2, 3, 3, 5, 6)`. -/
def targetTop_0606 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 0;
     0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0606 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_0606 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 5, 4]
  invFun := ![0, 1, 2, 3, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0606 : BottomDetBound targetTop_0606 9 := by
  have hU : rowTransform_0606.det.natAbs = 1 := by
    have hdet : rowTransform_0606.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R022.Aggregate.bottomBound.transformTopRows rowTransform_0606 hU
  have hcols := hrows.permuteColumns columnPerm_0606
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0606 MainTheory.Generated.BinaryBetaSixKernel.Representative.R022.Base.explicitTop)
          columnPerm_0606 = targetTop_0606 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0606 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 3 3 5 6)) 9 := by
  have htop : targetTop_0606 =
      topOfPattern (R := ℤ) (angle6 0 2 3 3 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0606

/-- Explicit target top block for canonical pattern `(0, 2, 3, 3, 5, 7)`. -/
def targetTop_0607 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0607 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 1, 0;
     0, 0, 1]

def columnPerm_0607 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 4, 5]
  invFun := ![0, 2, 3, 1, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0607 : BottomDetBound targetTop_0607 9 := by
  have hU : rowTransform_0607.det.natAbs = 1 := by
    have hdet : rowTransform_0607.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate.bottomBound.transformTopRows rowTransform_0607 hU
  have hcols := hrows.permuteColumns columnPerm_0607
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0607 MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Base.explicitTop)
          columnPerm_0607 = targetTop_0607 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0607 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 3 3 5 7)) 9 := by
  have htop : targetTop_0607 =
      topOfPattern (R := ℤ) (angle6 0 2 3 3 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0607

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard037
