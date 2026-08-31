-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R039.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R044.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R047.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R048.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R049.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R050.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard065

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(1, 2, 2, 4, 4, 6)`. -/
def targetTop_1040 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 0;
     0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1040 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1040 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1040 : BottomDetBound targetTop_1040 9 := by
  have hU : rowTransform_1040.det.natAbs = 1 := by
    have hdet : rowTransform_1040.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate.bottomBound.transformTopRows rowTransform_1040 hU
  have hcols := hrows.permuteColumns columnPerm_1040
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1040 MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Base.explicitTop)
          columnPerm_1040 = targetTop_1040 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1040 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 4 4 6)) 9 := by
  have htop : targetTop_1040 =
      topOfPattern (R := ℤ) (angle6 1 2 2 4 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1040

/-- Explicit target top block for canonical pattern `(1, 2, 2, 4, 4, 7)`. -/
def targetTop_1041 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 1;
     0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1041 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1041 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1041 : BottomDetBound targetTop_1041 9 := by
  have hU : rowTransform_1041.det.natAbs = 1 := by
    have hdet : rowTransform_1041.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R039.Aggregate.bottomBound.transformTopRows rowTransform_1041 hU
  have hcols := hrows.permuteColumns columnPerm_1041
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1041 MainTheory.Generated.BinaryBetaSixKernel.Representative.R039.Base.explicitTop)
          columnPerm_1041 = targetTop_1041 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1041 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 4 4 7)) 9 := by
  have htop : targetTop_1041 =
      topOfPattern (R := ℤ) (angle6 1 2 2 4 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1041

/-- Explicit target top block for canonical pattern `(1, 2, 2, 4, 5, 5)`. -/
def targetTop_1042 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 1, 1;
     0, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1042 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1042 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1042 : BottomDetBound targetTop_1042 9 := by
  have hU : rowTransform_1042.det.natAbs = 1 := by
    have hdet : rowTransform_1042.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate.bottomBound.transformTopRows rowTransform_1042 hU
  have hcols := hrows.permuteColumns columnPerm_1042
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1042 MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Base.explicitTop)
          columnPerm_1042 = targetTop_1042 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1042 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 4 5 5)) 9 := by
  have htop : targetTop_1042 =
      topOfPattern (R := ℤ) (angle6 1 2 2 4 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1042

/-- Explicit target top block for canonical pattern `(1, 2, 2, 4, 5, 6)`. -/
def targetTop_1043 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 1, 0;
     0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1043 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1043 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 5, 3]
  invFun := ![1, 2, 3, 5, 0, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1043 : BottomDetBound targetTop_1043 9 := by
  have hU : rowTransform_1043.det.natAbs = 1 := by
    have hdet : rowTransform_1043.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Aggregate.bottomBound.transformTopRows rowTransform_1043 hU
  have hcols := hrows.permuteColumns columnPerm_1043
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1043 MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Base.explicitTop)
          columnPerm_1043 = targetTop_1043 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1043 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 4 5 6)) 9 := by
  have htop : targetTop_1043 =
      topOfPattern (R := ℤ) (angle6 1 2 2 4 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1043

/-- Explicit target top block for canonical pattern `(1, 2, 2, 4, 5, 7)`. -/
def targetTop_1044 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 1, 1;
     0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1044 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1044 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1044 : BottomDetBound targetTop_1044 9 := by
  have hU : rowTransform_1044.det.natAbs = 1 := by
    have hdet : rowTransform_1044.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R047.Aggregate.bottomBound.transformTopRows rowTransform_1044 hU
  have hcols := hrows.permuteColumns columnPerm_1044
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1044 MainTheory.Generated.BinaryBetaSixKernel.Representative.R047.Base.explicitTop)
          columnPerm_1044 = targetTop_1044 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1044 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 4 5 7)) 9 := by
  have htop : targetTop_1044 =
      topOfPattern (R := ℤ) (angle6 1 2 2 4 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1044

/-- Explicit target top block for canonical pattern `(1, 2, 2, 4, 6, 6)`. -/
def targetTop_1045 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 0;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1045 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1045 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1045 : BottomDetBound targetTop_1045 9 := by
  have hU : rowTransform_1045.det.natAbs = 1 := by
    have hdet : rowTransform_1045.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_1045 hU
  have hcols := hrows.permuteColumns columnPerm_1045
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1045 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_1045 = targetTop_1045 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1045 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 4 6 6)) 9 := by
  have htop : targetTop_1045 =
      topOfPattern (R := ℤ) (angle6 1 2 2 4 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1045

/-- Explicit target top block for canonical pattern `(1, 2, 2, 4, 6, 7)`. -/
def targetTop_1046 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 1;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1046 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1046 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1046 : BottomDetBound targetTop_1046 9 := by
  have hU : rowTransform_1046.det.natAbs = 1 := by
    have hdet : rowTransform_1046.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R044.Aggregate.bottomBound.transformTopRows rowTransform_1046 hU
  have hcols := hrows.permuteColumns columnPerm_1046
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1046 MainTheory.Generated.BinaryBetaSixKernel.Representative.R044.Base.explicitTop)
          columnPerm_1046 = targetTop_1046 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1046 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 4 6 7)) 9 := by
  have htop : targetTop_1046 =
      topOfPattern (R := ℤ) (angle6 1 2 2 4 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1046

/-- Explicit target top block for canonical pattern `(1, 2, 2, 4, 7, 7)`. -/
def targetTop_1047 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 1, 1;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1047 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1047 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1047 : BottomDetBound targetTop_1047 9 := by
  have hU : rowTransform_1047.det.natAbs = 1 := by
    have hdet : rowTransform_1047.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R048.Aggregate.bottomBound.transformTopRows rowTransform_1047 hU
  have hcols := hrows.permuteColumns columnPerm_1047
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1047 MainTheory.Generated.BinaryBetaSixKernel.Representative.R048.Base.explicitTop)
          columnPerm_1047 = targetTop_1047 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1047 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 4 7 7)) 9 := by
  have htop : targetTop_1047 =
      topOfPattern (R := ℤ) (angle6 1 2 2 4 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1047

/-- Explicit target top block for canonical pattern `(1, 2, 2, 5, 5, 5)`. -/
def targetTop_1048 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 1, 1;
     0, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1048 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 0;
     1, 0, 0]

def columnPerm_1048 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1048 : BottomDetBound targetTop_1048 9 := by
  have hU : rowTransform_1048.det.natAbs = 1 := by
    have hdet : rowTransform_1048.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1048 hU
  have hcols := hrows.permuteColumns columnPerm_1048
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1048 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1048 = targetTop_1048 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1048 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 5 5 5)) 9 := by
  have htop : targetTop_1048 =
      topOfPattern (R := ℤ) (angle6 1 2 2 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1048

/-- Explicit target top block for canonical pattern `(1, 2, 2, 5, 5, 6)`. -/
def targetTop_1049 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 1, 0;
     0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1049 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1049 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 4, 5, 3]
  invFun := ![1, 2, 0, 5, 3, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1049 : BottomDetBound targetTop_1049 9 := by
  have hU : rowTransform_1049.det.natAbs = 1 := by
    have hdet : rowTransform_1049.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R049.Aggregate.bottomBound.transformTopRows rowTransform_1049 hU
  have hcols := hrows.permuteColumns columnPerm_1049
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1049 MainTheory.Generated.BinaryBetaSixKernel.Representative.R049.Base.explicitTop)
          columnPerm_1049 = targetTop_1049 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1049 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 5 5 6)) 9 := by
  have htop : targetTop_1049 =
      topOfPattern (R := ℤ) (angle6 1 2 2 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1049

/-- Explicit target top block for canonical pattern `(1, 2, 2, 5, 5, 7)`. -/
def targetTop_1050 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 1, 1;
     0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1050 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1050 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1050 : BottomDetBound targetTop_1050 9 := by
  have hU : rowTransform_1050.det.natAbs = 1 := by
    have hdet : rowTransform_1050.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate.bottomBound.transformTopRows rowTransform_1050 hU
  have hcols := hrows.permuteColumns columnPerm_1050
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1050 MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Base.explicitTop)
          columnPerm_1050 = targetTop_1050 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1050 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 5 5 7)) 9 := by
  have htop : targetTop_1050 =
      topOfPattern (R := ℤ) (angle6 1 2 2 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1050

/-- Explicit target top block for canonical pattern `(1, 2, 2, 5, 6, 6)`. -/
def targetTop_1051 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 0, 0;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1051 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, (-1);
     0, 1, 0]

def columnPerm_1051 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 5, 2, 3]
  invFun := ![1, 2, 4, 5, 0, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1051 : BottomDetBound targetTop_1051 9 := by
  have hU : rowTransform_1051.det.natAbs = 1 := by
    have hdet : rowTransform_1051.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate.bottomBound.transformTopRows rowTransform_1051 hU
  have hcols := hrows.permuteColumns columnPerm_1051
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1051 MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Base.explicitTop)
          columnPerm_1051 = targetTop_1051 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1051 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 5 6 6)) 9 := by
  have htop : targetTop_1051 =
      topOfPattern (R := ℤ) (angle6 1 2 2 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1051

/-- Explicit target top block for canonical pattern `(1, 2, 2, 5, 6, 7)`. -/
def targetTop_1052 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 0, 1;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1052 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1052 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 4, 3, 5]
  invFun := ![1, 2, 0, 4, 3, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1052 : BottomDetBound targetTop_1052 9 := by
  have hU : rowTransform_1052.det.natAbs = 1 := by
    have hdet : rowTransform_1052.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R050.Aggregate.bottomBound.transformTopRows rowTransform_1052 hU
  have hcols := hrows.permuteColumns columnPerm_1052
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1052 MainTheory.Generated.BinaryBetaSixKernel.Representative.R050.Base.explicitTop)
          columnPerm_1052 = targetTop_1052 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1052 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 5 6 7)) 9 := by
  have htop : targetTop_1052 =
      topOfPattern (R := ℤ) (angle6 1 2 2 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1052

/-- Explicit target top block for canonical pattern `(1, 2, 2, 5, 7, 7)`. -/
def targetTop_1053 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 1, 1;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1053 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1053 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1053 : BottomDetBound targetTop_1053 9 := by
  have hU : rowTransform_1053.det.natAbs = 1 := by
    have hdet : rowTransform_1053.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_1053 hU
  have hcols := hrows.permuteColumns columnPerm_1053
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1053 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_1053 = targetTop_1053 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1053 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 5 7 7)) 9 := by
  have htop : targetTop_1053 =
      topOfPattern (R := ℤ) (angle6 1 2 2 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1053

/-- Explicit target top block for canonical pattern `(1, 2, 2, 6, 6, 6)`. -/
def targetTop_1054 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1054 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, 0;
     1, 0, 0]

def columnPerm_1054 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1054 : BottomDetBound targetTop_1054 9 := by
  have hU : rowTransform_1054.det.natAbs = 1 := by
    have hdet : rowTransform_1054.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1054 hU
  have hcols := hrows.permuteColumns columnPerm_1054
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1054 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1054 = targetTop_1054 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1054 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 6 6 6)) 9 := by
  have htop : targetTop_1054 =
      topOfPattern (R := ℤ) (angle6 1 2 2 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1054

/-- Explicit target top block for canonical pattern `(1, 2, 2, 6, 6, 7)`. -/
def targetTop_1055 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1055 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, 0;
     1, 0, 0]

def columnPerm_1055 : Equiv.Perm (Fin 6) where
  toFun := ![4, 2, 3, 0, 1, 5]
  invFun := ![3, 4, 1, 2, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1055 : BottomDetBound targetTop_1055 9 := by
  have hU : rowTransform_1055.det.natAbs = 1 := by
    have hdet : rowTransform_1055.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_1055 hU
  have hcols := hrows.permuteColumns columnPerm_1055
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1055 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_1055 = targetTop_1055 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1055 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 6 6 7)) 9 := by
  have htop : targetTop_1055 =
      topOfPattern (R := ℤ) (angle6 1 2 2 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1055

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard065
