-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R017.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R019.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R021.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R023.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard038

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(0, 2, 3, 3, 6, 6)`. -/
def targetTop_0608 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 0;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0608 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, 1;
     0, 1, 0]

def columnPerm_0608 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0608 : BottomDetBound targetTop_0608 9 := by
  have hU : rowTransform_0608.det.natAbs = 1 := by
    have hdet : rowTransform_0608.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0608 hU
  have hcols := hrows.permuteColumns columnPerm_0608
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0608 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0608 = targetTop_0608 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0608 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 3 3 6 6)) 9 := by
  have htop : targetTop_0608 =
      topOfPattern (R := ℤ) (angle6 0 2 3 3 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0608

/-- Explicit target top block for canonical pattern `(0, 2, 3, 3, 6, 7)`. -/
def targetTop_0609 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0609 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, 0;
     0, 0, 1]

def columnPerm_0609 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 5, 4]
  invFun := ![0, 2, 3, 1, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0609 : BottomDetBound targetTop_0609 9 := by
  have hU : rowTransform_0609.det.natAbs = 1 := by
    have hdet : rowTransform_0609.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Aggregate.bottomBound.transformTopRows rowTransform_0609 hU
  have hcols := hrows.permuteColumns columnPerm_0609
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0609 MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Base.explicitTop)
          columnPerm_0609 = targetTop_0609 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0609 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 3 3 6 7)) 9 := by
  have htop : targetTop_0609 =
      topOfPattern (R := ℤ) (angle6 0 2 3 3 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0609

/-- Explicit target top block for canonical pattern `(0, 2, 3, 3, 7, 7)`. -/
def targetTop_0610 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0610 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 1, 1;
     0, 1, 0]

def columnPerm_0610 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0610 : BottomDetBound targetTop_0610 9 := by
  have hU : rowTransform_0610.det.natAbs = 1 := by
    have hdet : rowTransform_0610.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0610 hU
  have hcols := hrows.permuteColumns columnPerm_0610
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0610 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0610 = targetTop_0610 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0610 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 3 3 7 7)) 9 := by
  have htop : targetTop_0610 =
      topOfPattern (R := ℤ) (angle6 0 2 3 3 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0610

/-- Explicit target top block for canonical pattern `(0, 2, 3, 4, 4, 4)`. -/
def targetTop_0611 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 0;
     0, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0611 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 1;
     1, 0, 0]

def columnPerm_0611 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0611 : BottomDetBound targetTop_0611 9 := by
  have hU : rowTransform_0611.det.natAbs = 1 := by
    have hdet : rowTransform_0611.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0611 hU
  have hcols := hrows.permuteColumns columnPerm_0611
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0611 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0611 = targetTop_0611 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0611 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 3 4 4 4)) 9 := by
  have htop : targetTop_0611 =
      topOfPattern (R := ℤ) (angle6 0 2 3 4 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0611

/-- Explicit target top block for canonical pattern `(0, 2, 3, 4, 4, 5)`. -/
def targetTop_0612 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 1;
     0, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0612 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 0]

def columnPerm_0612 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 5, 1, 2, 4]
  invFun := ![0, 3, 4, 1, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0612 : BottomDetBound targetTop_0612 9 := by
  have hU : rowTransform_0612.det.natAbs = 1 := by
    have hdet : rowTransform_0612.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Aggregate.bottomBound.transformTopRows rowTransform_0612 hU
  have hcols := hrows.permuteColumns columnPerm_0612
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0612 MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Base.explicitTop)
          columnPerm_0612 = targetTop_0612 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0612 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 3 4 4 5)) 9 := by
  have htop : targetTop_0612 =
      topOfPattern (R := ℤ) (angle6 0 2 3 4 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0612

/-- Explicit target top block for canonical pattern `(0, 2, 3, 4, 4, 6)`. -/
def targetTop_0613 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 0;
     0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0613 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 1;
     1, 0, 0]

def columnPerm_0613 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 5, 1, 2, 4]
  invFun := ![0, 3, 4, 1, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0613 : BottomDetBound targetTop_0613 9 := by
  have hU : rowTransform_0613.det.natAbs = 1 := by
    have hdet : rowTransform_0613.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0613 hU
  have hcols := hrows.permuteColumns columnPerm_0613
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0613 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0613 = targetTop_0613 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0613 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 3 4 4 6)) 9 := by
  have htop : targetTop_0613 =
      topOfPattern (R := ℤ) (angle6 0 2 3 4 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0613

/-- Explicit target top block for canonical pattern `(0, 2, 3, 4, 4, 7)`. -/
def targetTop_0614 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 1;
     0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0614 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 1, 1;
     1, 0, 0]

def columnPerm_0614 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 3, 1, 2, 4]
  invFun := ![0, 3, 4, 2, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0614 : BottomDetBound targetTop_0614 9 := by
  have hU : rowTransform_0614.det.natAbs = 1 := by
    have hdet : rowTransform_0614.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0614 hU
  have hcols := hrows.permuteColumns columnPerm_0614
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0614 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0614 = targetTop_0614 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0614 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 3 4 4 7)) 9 := by
  have htop : targetTop_0614 =
      topOfPattern (R := ℤ) (angle6 0 2 3 4 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0614

/-- Explicit target top block for canonical pattern `(0, 2, 3, 4, 5, 5)`. -/
def targetTop_0615 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 1, 1;
     0, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0615 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, (-1);
     0, 1, 0;
     1, 0, 0]

def columnPerm_0615 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 3, 4, 1, 2]
  invFun := ![0, 4, 5, 2, 3, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0615 : BottomDetBound targetTop_0615 9 := by
  have hU : rowTransform_0615.det.natAbs = 1 := by
    have hdet : rowTransform_0615.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Aggregate.bottomBound.transformTopRows rowTransform_0615 hU
  have hcols := hrows.permuteColumns columnPerm_0615
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0615 MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Base.explicitTop)
          columnPerm_0615 = targetTop_0615 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0615 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 3 4 5 5)) 9 := by
  have htop : targetTop_0615 =
      topOfPattern (R := ℤ) (angle6 0 2 3 4 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0615

/-- Explicit target top block for canonical pattern `(0, 2, 3, 4, 5, 6)`. -/
def targetTop_0616 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 1, 0;
     0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0616 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_0616 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 5, 3]
  invFun := ![0, 1, 3, 5, 2, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0616 : BottomDetBound targetTop_0616 9 := by
  have hU : rowTransform_0616.det.natAbs = 1 := by
    have hdet : rowTransform_0616.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R019.Aggregate.bottomBound.transformTopRows rowTransform_0616 hU
  have hcols := hrows.permuteColumns columnPerm_0616
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0616 MainTheory.Generated.BinaryBetaSixKernel.Representative.R019.Base.explicitTop)
          columnPerm_0616 = targetTop_0616 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0616 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 3 4 5 6)) 9 := by
  have htop : targetTop_0616 =
      topOfPattern (R := ℤ) (angle6 0 2 3 4 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0616

/-- Explicit target top block for canonical pattern `(0, 2, 3, 4, 5, 7)`. -/
def targetTop_0617 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 1, 1;
     0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0617 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, (-1);
     0, 0, 1]

def columnPerm_0617 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0617 : BottomDetBound targetTop_0617 9 := by
  have hU : rowTransform_0617.det.natAbs = 1 := by
    have hdet : rowTransform_0617.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R021.Aggregate.bottomBound.transformTopRows rowTransform_0617 hU
  have hcols := hrows.permuteColumns columnPerm_0617
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0617 MainTheory.Generated.BinaryBetaSixKernel.Representative.R021.Base.explicitTop)
          columnPerm_0617 = targetTop_0617 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0617 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 3 4 5 7)) 9 := by
  have htop : targetTop_0617 =
      topOfPattern (R := ℤ) (angle6 0 2 3 4 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0617

/-- Explicit target top block for canonical pattern `(0, 2, 3, 4, 6, 6)`. -/
def targetTop_0618 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 0;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0618 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 1;
     0, 1, 0]

def columnPerm_0618 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0618 : BottomDetBound targetTop_0618 9 := by
  have hU : rowTransform_0618.det.natAbs = 1 := by
    have hdet : rowTransform_0618.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Aggregate.bottomBound.transformTopRows rowTransform_0618 hU
  have hcols := hrows.permuteColumns columnPerm_0618
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0618 MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Base.explicitTop)
          columnPerm_0618 = targetTop_0618 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0618 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 3 4 6 6)) 9 := by
  have htop : targetTop_0618 =
      topOfPattern (R := ℤ) (angle6 0 2 3 4 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0618

/-- Explicit target top block for canonical pattern `(0, 2, 3, 4, 6, 7)`. -/
def targetTop_0619 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 1;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0619 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 1;
     1, 0, 0]

def columnPerm_0619 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 4, 1, 3, 5]
  invFun := ![0, 3, 1, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0619 : BottomDetBound targetTop_0619 9 := by
  have hU : rowTransform_0619.det.natAbs = 1 := by
    have hdet : rowTransform_0619.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R017.Aggregate.bottomBound.transformTopRows rowTransform_0619 hU
  have hcols := hrows.permuteColumns columnPerm_0619
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0619 MainTheory.Generated.BinaryBetaSixKernel.Representative.R017.Base.explicitTop)
          columnPerm_0619 = targetTop_0619 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0619 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 3 4 6 7)) 9 := by
  have htop : targetTop_0619 =
      topOfPattern (R := ℤ) (angle6 0 2 3 4 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0619

/-- Explicit target top block for canonical pattern `(0, 2, 3, 4, 7, 7)`. -/
def targetTop_0620 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 1, 1;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0620 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 0, 1;
     0, 1, 0]

def columnPerm_0620 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0620 : BottomDetBound targetTop_0620 9 := by
  have hU : rowTransform_0620.det.natAbs = 1 := by
    have hdet : rowTransform_0620.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Aggregate.bottomBound.transformTopRows rowTransform_0620 hU
  have hcols := hrows.permuteColumns columnPerm_0620
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0620 MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Base.explicitTop)
          columnPerm_0620 = targetTop_0620 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0620 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 3 4 7 7)) 9 := by
  have htop : targetTop_0620 =
      topOfPattern (R := ℤ) (angle6 0 2 3 4 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0620

/-- Explicit target top block for canonical pattern `(0, 2, 3, 5, 5, 5)`. -/
def targetTop_0621 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0621 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 1;
     1, 0, 0]

def columnPerm_0621 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0621 : BottomDetBound targetTop_0621 9 := by
  have hU : rowTransform_0621.det.natAbs = 1 := by
    have hdet : rowTransform_0621.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0621 hU
  have hcols := hrows.permuteColumns columnPerm_0621
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0621 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0621 = targetTop_0621 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0621 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 3 5 5 5)) 9 := by
  have htop : targetTop_0621 =
      topOfPattern (R := ℤ) (angle6 0 2 3 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0621

/-- Explicit target top block for canonical pattern `(0, 2, 3, 5, 5, 6)`. -/
def targetTop_0622 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 0;
     0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0622 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_0622 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 4, 5, 3]
  invFun := ![0, 1, 2, 5, 3, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0622 : BottomDetBound targetTop_0622 9 := by
  have hU : rowTransform_0622.det.natAbs = 1 := by
    have hdet : rowTransform_0622.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R023.Aggregate.bottomBound.transformTopRows rowTransform_0622 hU
  have hcols := hrows.permuteColumns columnPerm_0622
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0622 MainTheory.Generated.BinaryBetaSixKernel.Representative.R023.Base.explicitTop)
          columnPerm_0622 = targetTop_0622 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0622 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 3 5 5 6)) 9 := by
  have htop : targetTop_0622 =
      topOfPattern (R := ℤ) (angle6 0 2 3 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0622

/-- Explicit target top block for canonical pattern `(0, 2, 3, 5, 5, 7)`. -/
def targetTop_0623 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0623 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 1;
     1, 0, 0]

def columnPerm_0623 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 5, 1, 2, 4]
  invFun := ![0, 3, 4, 1, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0623 : BottomDetBound targetTop_0623 9 := by
  have hU : rowTransform_0623.det.natAbs = 1 := by
    have hdet : rowTransform_0623.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0623 hU
  have hcols := hrows.permuteColumns columnPerm_0623
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0623 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0623 = targetTop_0623 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0623 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 3 5 5 7)) 9 := by
  have htop : targetTop_0623 =
      topOfPattern (R := ℤ) (angle6 0 2 3 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0623

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard038
