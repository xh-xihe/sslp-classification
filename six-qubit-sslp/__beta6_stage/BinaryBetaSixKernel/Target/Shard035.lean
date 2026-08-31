-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R015.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard035

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit rank-deficient target for canonical pattern `(0, 2, 2, 2, 7, 7)`. -/
def targetTop_0560 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0560 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0560 :
    TopRowRelation targetTop_0560 relationCoefficients_0560 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0560, relationCoefficients_0560, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0560 : BottomDetBound targetTop_0560 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0560

theorem canonicalBound_0560 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 2 7 7)) 9 := by
  have htop : targetTop_0560 =
      topOfPattern (R := ℤ) (angle6 0 2 2 2 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0560

/-- Explicit rank-deficient target for canonical pattern `(0, 2, 2, 3, 3, 3)`. -/
def targetTop_0561 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0561 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0561 :
    TopRowRelation targetTop_0561 relationCoefficients_0561 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0561, relationCoefficients_0561, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0561 : BottomDetBound targetTop_0561 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0561

theorem canonicalBound_0561 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 3 3 3)) 9 := by
  have htop : targetTop_0561 =
      topOfPattern (R := ℤ) (angle6 0 2 2 3 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0561

/-- Explicit target top block for canonical pattern `(0, 2, 2, 3, 3, 4)`. -/
def targetTop_0562 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 0;
     0, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0562 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 0;
     0, 0, 1]

def columnPerm_0562 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0562 : BottomDetBound targetTop_0562 9 := by
  have hU : rowTransform_0562.det.natAbs = 1 := by
    have hdet : rowTransform_0562.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0562 hU
  have hcols := hrows.permuteColumns columnPerm_0562
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0562 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0562 = targetTop_0562 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0562 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 3 3 4)) 9 := by
  have htop : targetTop_0562 =
      topOfPattern (R := ℤ) (angle6 0 2 2 3 3 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0562

/-- Explicit target top block for canonical pattern `(0, 2, 2, 3, 3, 5)`. -/
def targetTop_0563 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0563 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 1, 0;
     0, 0, 1]

def columnPerm_0563 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0563 : BottomDetBound targetTop_0563 9 := by
  have hU : rowTransform_0563.det.natAbs = 1 := by
    have hdet : rowTransform_0563.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0563 hU
  have hcols := hrows.permuteColumns columnPerm_0563
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0563 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0563 = targetTop_0563 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0563 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 3 3 5)) 9 := by
  have htop : targetTop_0563 =
      topOfPattern (R := ℤ) (angle6 0 2 2 3 3 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0563

/-- Explicit target top block for canonical pattern `(0, 2, 2, 3, 3, 6)`. -/
def targetTop_0564 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 0;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0564 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 1;
     0, 0, 1]

def columnPerm_0564 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0564 : BottomDetBound targetTop_0564 9 := by
  have hU : rowTransform_0564.det.natAbs = 1 := by
    have hdet : rowTransform_0564.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0564 hU
  have hcols := hrows.permuteColumns columnPerm_0564
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0564 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0564 = targetTop_0564 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0564 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 3 3 6)) 9 := by
  have htop : targetTop_0564 =
      topOfPattern (R := ℤ) (angle6 0 2 2 3 3 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0564

/-- Explicit target top block for canonical pattern `(0, 2, 2, 3, 3, 7)`. -/
def targetTop_0565 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0565 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 1, 1;
     0, 0, 1]

def columnPerm_0565 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0565 : BottomDetBound targetTop_0565 9 := by
  have hU : rowTransform_0565.det.natAbs = 1 := by
    have hdet : rowTransform_0565.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0565 hU
  have hcols := hrows.permuteColumns columnPerm_0565
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0565 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0565 = targetTop_0565 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0565 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 3 3 7)) 9 := by
  have htop : targetTop_0565 =
      topOfPattern (R := ℤ) (angle6 0 2 2 3 3 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0565

/-- Explicit target top block for canonical pattern `(0, 2, 2, 3, 4, 4)`. -/
def targetTop_0566 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 0;
     0, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0566 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 1;
     0, 1, 0]

def columnPerm_0566 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0566 : BottomDetBound targetTop_0566 9 := by
  have hU : rowTransform_0566.det.natAbs = 1 := by
    have hdet : rowTransform_0566.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0566 hU
  have hcols := hrows.permuteColumns columnPerm_0566
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0566 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0566 = targetTop_0566 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0566 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 3 4 4)) 9 := by
  have htop : targetTop_0566 =
      topOfPattern (R := ℤ) (angle6 0 2 2 3 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0566

/-- Explicit target top block for canonical pattern `(0, 2, 2, 3, 4, 5)`. -/
def targetTop_0567 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 1;
     0, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0567 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, (-1);
     0, 0, 1]

def columnPerm_0567 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0567 : BottomDetBound targetTop_0567 9 := by
  have hU : rowTransform_0567.det.natAbs = 1 := by
    have hdet : rowTransform_0567.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Aggregate.bottomBound.transformTopRows rowTransform_0567 hU
  have hcols := hrows.permuteColumns columnPerm_0567
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0567 MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Base.explicitTop)
          columnPerm_0567 = targetTop_0567 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0567 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 3 4 5)) 9 := by
  have htop : targetTop_0567 =
      topOfPattern (R := ℤ) (angle6 0 2 2 3 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0567

/-- Explicit target top block for canonical pattern `(0, 2, 2, 3, 4, 6)`. -/
def targetTop_0568 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 0;
     0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0568 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 1;
     0, 1, 0]

def columnPerm_0568 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0568 : BottomDetBound targetTop_0568 9 := by
  have hU : rowTransform_0568.det.natAbs = 1 := by
    have hdet : rowTransform_0568.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0568 hU
  have hcols := hrows.permuteColumns columnPerm_0568
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0568 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0568 = targetTop_0568 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0568 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 3 4 6)) 9 := by
  have htop : targetTop_0568 =
      topOfPattern (R := ℤ) (angle6 0 2 2 3 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0568

/-- Explicit target top block for canonical pattern `(0, 2, 2, 3, 4, 7)`. -/
def targetTop_0569 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 1;
     0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0569 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 0;
     0, 0, 1]

def columnPerm_0569 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0569 : BottomDetBound targetTop_0569 9 := by
  have hU : rowTransform_0569.det.natAbs = 1 := by
    have hdet : rowTransform_0569.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate.bottomBound.transformTopRows rowTransform_0569 hU
  have hcols := hrows.permuteColumns columnPerm_0569
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0569 MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Base.explicitTop)
          columnPerm_0569 = targetTop_0569 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0569 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 3 4 7)) 9 := by
  have htop : targetTop_0569 =
      topOfPattern (R := ℤ) (angle6 0 2 2 3 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0569

/-- Explicit target top block for canonical pattern `(0, 2, 2, 3, 5, 5)`. -/
def targetTop_0570 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0570 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 1;
     0, 1, 0]

def columnPerm_0570 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0570 : BottomDetBound targetTop_0570 9 := by
  have hU : rowTransform_0570.det.natAbs = 1 := by
    have hdet : rowTransform_0570.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0570 hU
  have hcols := hrows.permuteColumns columnPerm_0570
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0570 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0570 = targetTop_0570 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0570 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 3 5 5)) 9 := by
  have htop : targetTop_0570 =
      topOfPattern (R := ℤ) (angle6 0 2 2 3 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0570

/-- Explicit target top block for canonical pattern `(0, 2, 2, 3, 5, 6)`. -/
def targetTop_0571 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 0;
     0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0571 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_0571 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 5, 4]
  invFun := ![0, 1, 2, 3, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0571 : BottomDetBound targetTop_0571 9 := by
  have hU : rowTransform_0571.det.natAbs = 1 := by
    have hdet : rowTransform_0571.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R015.Aggregate.bottomBound.transformTopRows rowTransform_0571 hU
  have hcols := hrows.permuteColumns columnPerm_0571
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0571 MainTheory.Generated.BinaryBetaSixKernel.Representative.R015.Base.explicitTop)
          columnPerm_0571 = targetTop_0571 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0571 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 3 5 6)) 9 := by
  have htop : targetTop_0571 =
      topOfPattern (R := ℤ) (angle6 0 2 2 3 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0571

/-- Explicit target top block for canonical pattern `(0, 2, 2, 3, 5, 7)`. -/
def targetTop_0572 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0572 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 1;
     0, 1, 0]

def columnPerm_0572 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0572 : BottomDetBound targetTop_0572 9 := by
  have hU : rowTransform_0572.det.natAbs = 1 := by
    have hdet : rowTransform_0572.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0572 hU
  have hcols := hrows.permuteColumns columnPerm_0572
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0572 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0572 = targetTop_0572 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0572 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 3 5 7)) 9 := by
  have htop : targetTop_0572 =
      topOfPattern (R := ℤ) (angle6 0 2 2 3 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0572

/-- Explicit target top block for canonical pattern `(0, 2, 2, 3, 6, 6)`. -/
def targetTop_0573 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 0;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0573 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, 1;
     0, 1, 0]

def columnPerm_0573 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0573 : BottomDetBound targetTop_0573 9 := by
  have hU : rowTransform_0573.det.natAbs = 1 := by
    have hdet : rowTransform_0573.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0573 hU
  have hcols := hrows.permuteColumns columnPerm_0573
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0573 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0573 = targetTop_0573 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0573 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 3 6 6)) 9 := by
  have htop : targetTop_0573 =
      topOfPattern (R := ℤ) (angle6 0 2 2 3 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0573

/-- Explicit target top block for canonical pattern `(0, 2, 2, 3, 6, 7)`. -/
def targetTop_0574 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0574 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 0;
     0, 0, 1]

def columnPerm_0574 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0574 : BottomDetBound targetTop_0574 9 := by
  have hU : rowTransform_0574.det.natAbs = 1 := by
    have hdet : rowTransform_0574.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Aggregate.bottomBound.transformTopRows rowTransform_0574 hU
  have hcols := hrows.permuteColumns columnPerm_0574
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0574 MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Base.explicitTop)
          columnPerm_0574 = targetTop_0574 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0574 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 3 6 7)) 9 := by
  have htop : targetTop_0574 =
      topOfPattern (R := ℤ) (angle6 0 2 2 3 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0574

/-- Explicit target top block for canonical pattern `(0, 2, 2, 3, 7, 7)`. -/
def targetTop_0575 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0575 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 1, 1;
     0, 1, 0]

def columnPerm_0575 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0575 : BottomDetBound targetTop_0575 9 := by
  have hU : rowTransform_0575.det.natAbs = 1 := by
    have hdet : rowTransform_0575.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0575 hU
  have hcols := hrows.permuteColumns columnPerm_0575
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0575 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0575 = targetTop_0575 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0575 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 3 7 7)) 9 := by
  have htop : targetTop_0575 =
      topOfPattern (R := ℤ) (angle6 0 2 2 3 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0575

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard035
