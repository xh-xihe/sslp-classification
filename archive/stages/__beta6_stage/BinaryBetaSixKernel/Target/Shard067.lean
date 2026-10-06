-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R047.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R058.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R059.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R060.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R061.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R062.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard067

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(1, 2, 3, 3, 7, 7)`. -/
def targetTop_1072 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1072 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 1;
     1, 0, 0]

def columnPerm_1072 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 4, 5, 0, 1]
  invFun := ![4, 5, 0, 1, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1072 : BottomDetBound targetTop_1072 9 := by
  have hU : rowTransform_1072.det.natAbs = 1 := by
    have hdet : rowTransform_1072.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate.bottomBound.transformTopRows rowTransform_1072 hU
  have hcols := hrows.permuteColumns columnPerm_1072
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1072 MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Base.explicitTop)
          columnPerm_1072 = targetTop_1072 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1072 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 3 7 7)) 9 := by
  have htop : targetTop_1072 =
      topOfPattern (R := ℤ) (angle6 1 2 3 3 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1072

/-- Explicit target top block for canonical pattern `(1, 2, 3, 4, 4, 4)`. -/
def targetTop_1073 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 0, 0, 0;
     0, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1073 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1073 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1073 : BottomDetBound targetTop_1073 9 := by
  have hU : rowTransform_1073.det.natAbs = 1 := by
    have hdet : rowTransform_1073.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate.bottomBound.transformTopRows rowTransform_1073 hU
  have hcols := hrows.permuteColumns columnPerm_1073
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1073 MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Base.explicitTop)
          columnPerm_1073 = targetTop_1073 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1073 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 4 4 4)) 9 := by
  have htop : targetTop_1073 =
      topOfPattern (R := ℤ) (angle6 1 2 3 4 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1073

/-- Explicit target top block for canonical pattern `(1, 2, 3, 4, 4, 5)`. -/
def targetTop_1074 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 0, 0, 1;
     0, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1074 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1074 : Equiv.Perm (Fin 6) where
  toFun := ![2, 4, 5, 0, 1, 3]
  invFun := ![3, 4, 0, 5, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1074 : BottomDetBound targetTop_1074 9 := by
  have hU : rowTransform_1074.det.natAbs = 1 := by
    have hdet : rowTransform_1074.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Aggregate.bottomBound.transformTopRows rowTransform_1074 hU
  have hcols := hrows.permuteColumns columnPerm_1074
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1074 MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Base.explicitTop)
          columnPerm_1074 = targetTop_1074 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1074 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 4 4 5)) 9 := by
  have htop : targetTop_1074 =
      topOfPattern (R := ℤ) (angle6 1 2 3 4 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1074

/-- Explicit target top block for canonical pattern `(1, 2, 3, 4, 4, 6)`. -/
def targetTop_1075 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 0, 0, 0;
     0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1075 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 0]

def columnPerm_1075 : Equiv.Perm (Fin 6) where
  toFun := ![4, 2, 5, 0, 1, 3]
  invFun := ![3, 4, 1, 5, 0, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1075 : BottomDetBound targetTop_1075 9 := by
  have hU : rowTransform_1075.det.natAbs = 1 := by
    have hdet : rowTransform_1075.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Aggregate.bottomBound.transformTopRows rowTransform_1075 hU
  have hcols := hrows.permuteColumns columnPerm_1075
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1075 MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Base.explicitTop)
          columnPerm_1075 = targetTop_1075 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1075 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 4 4 6)) 9 := by
  have htop : targetTop_1075 =
      topOfPattern (R := ℤ) (angle6 1 2 3 4 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1075

/-- Explicit target top block for canonical pattern `(1, 2, 3, 4, 4, 7)`. -/
def targetTop_1076 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 0, 0, 1;
     0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1076 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1076 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 4, 0, 1, 5]
  invFun := ![3, 4, 0, 1, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1076 : BottomDetBound targetTop_1076 9 := by
  have hU : rowTransform_1076.det.natAbs = 1 := by
    have hdet : rowTransform_1076.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R047.Aggregate.bottomBound.transformTopRows rowTransform_1076 hU
  have hcols := hrows.permuteColumns columnPerm_1076
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1076 MainTheory.Generated.BinaryBetaSixKernel.Representative.R047.Base.explicitTop)
          columnPerm_1076 = targetTop_1076 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1076 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 4 4 7)) 9 := by
  have htop : targetTop_1076 =
      topOfPattern (R := ℤ) (angle6 1 2 3 4 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1076

/-- Explicit target top block for canonical pattern `(1, 2, 3, 4, 5, 5)`. -/
def targetTop_1077 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 0, 1, 1;
     0, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1077 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_1077 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1077 : BottomDetBound targetTop_1077 9 := by
  have hU : rowTransform_1077.det.natAbs = 1 := by
    have hdet : rowTransform_1077.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Aggregate.bottomBound.transformTopRows rowTransform_1077 hU
  have hcols := hrows.permuteColumns columnPerm_1077
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1077 MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Base.explicitTop)
          columnPerm_1077 = targetTop_1077 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1077 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 4 5 5)) 9 := by
  have htop : targetTop_1077 =
      topOfPattern (R := ℤ) (angle6 1 2 3 4 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1077

/-- Explicit target top block for canonical pattern `(1, 2, 3, 4, 5, 6)`. -/
def targetTop_1078 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 0, 1, 0;
     0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1078 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_1078 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1078 : BottomDetBound targetTop_1078 9 := by
  have hU : rowTransform_1078.det.natAbs = 1 := by
    have hdet : rowTransform_1078.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R058.Aggregate.bottomBound.transformTopRows rowTransform_1078 hU
  have hcols := hrows.permuteColumns columnPerm_1078
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1078 MainTheory.Generated.BinaryBetaSixKernel.Representative.R058.Base.explicitTop)
          columnPerm_1078 = targetTop_1078 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1078 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 4 5 6)) 9 := by
  have htop : targetTop_1078 =
      topOfPattern (R := ℤ) (angle6 1 2 3 4 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1078

/-- Explicit target top block for canonical pattern `(1, 2, 3, 4, 5, 7)`. -/
def targetTop_1079 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 0, 1, 1;
     0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1079 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_1079 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1079 : BottomDetBound targetTop_1079 9 := by
  have hU : rowTransform_1079.det.natAbs = 1 := by
    have hdet : rowTransform_1079.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R059.Aggregate.bottomBound.transformTopRows rowTransform_1079 hU
  have hcols := hrows.permuteColumns columnPerm_1079
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1079 MainTheory.Generated.BinaryBetaSixKernel.Representative.R059.Base.explicitTop)
          columnPerm_1079 = targetTop_1079 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1079 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 4 5 7)) 9 := by
  have htop : targetTop_1079 =
      topOfPattern (R := ℤ) (angle6 1 2 3 4 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1079

/-- Explicit target top block for canonical pattern `(1, 2, 3, 4, 6, 6)`. -/
def targetTop_1080 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 0, 0, 0;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1080 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1080 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 5, 1, 2, 3]
  invFun := ![1, 3, 4, 5, 0, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1080 : BottomDetBound targetTop_1080 9 := by
  have hU : rowTransform_1080.det.natAbs = 1 := by
    have hdet : rowTransform_1080.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Aggregate.bottomBound.transformTopRows rowTransform_1080 hU
  have hcols := hrows.permuteColumns columnPerm_1080
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1080 MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Base.explicitTop)
          columnPerm_1080 = targetTop_1080 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1080 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 4 6 6)) 9 := by
  have htop : targetTop_1080 =
      topOfPattern (R := ℤ) (angle6 1 2 3 4 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1080

/-- Explicit target top block for canonical pattern `(1, 2, 3, 4, 6, 7)`. -/
def targetTop_1081 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 0, 0, 1;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1081 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1081 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1081 : BottomDetBound targetTop_1081 9 := by
  have hU : rowTransform_1081.det.natAbs = 1 := by
    have hdet : rowTransform_1081.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R059.Aggregate.bottomBound.transformTopRows rowTransform_1081 hU
  have hcols := hrows.permuteColumns columnPerm_1081
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1081 MainTheory.Generated.BinaryBetaSixKernel.Representative.R059.Base.explicitTop)
          columnPerm_1081 = targetTop_1081 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1081 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 4 6 7)) 9 := by
  have htop : targetTop_1081 =
      topOfPattern (R := ℤ) (angle6 1 2 3 4 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1081

/-- Explicit target top block for canonical pattern `(1, 2, 3, 4, 7, 7)`. -/
def targetTop_1082 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 0, 1, 1;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1082 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_1082 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1082 : BottomDetBound targetTop_1082 9 := by
  have hU : rowTransform_1082.det.natAbs = 1 := by
    have hdet : rowTransform_1082.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R060.Aggregate.bottomBound.transformTopRows rowTransform_1082 hU
  have hcols := hrows.permuteColumns columnPerm_1082
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1082 MainTheory.Generated.BinaryBetaSixKernel.Representative.R060.Base.explicitTop)
          columnPerm_1082 = targetTop_1082 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1082 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 4 7 7)) 9 := by
  have htop : targetTop_1082 =
      topOfPattern (R := ℤ) (angle6 1 2 3 4 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1082

/-- Explicit target top block for canonical pattern `(1, 2, 3, 5, 5, 5)`. -/
def targetTop_1083 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 1, 1;
     0, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1083 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1083 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1083 : BottomDetBound targetTop_1083 9 := by
  have hU : rowTransform_1083.det.natAbs = 1 := by
    have hdet : rowTransform_1083.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate.bottomBound.transformTopRows rowTransform_1083 hU
  have hcols := hrows.permuteColumns columnPerm_1083
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1083 MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Base.explicitTop)
          columnPerm_1083 = targetTop_1083 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1083 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 5 5 5)) 9 := by
  have htop : targetTop_1083 =
      topOfPattern (R := ℤ) (angle6 1 2 3 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1083

/-- Explicit target top block for canonical pattern `(1, 2, 3, 5, 5, 6)`. -/
def targetTop_1084 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 1, 0;
     0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1084 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_1084 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1084 : BottomDetBound targetTop_1084 9 := by
  have hU : rowTransform_1084.det.natAbs = 1 := by
    have hdet : rowTransform_1084.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R061.Aggregate.bottomBound.transformTopRows rowTransform_1084 hU
  have hcols := hrows.permuteColumns columnPerm_1084
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1084 MainTheory.Generated.BinaryBetaSixKernel.Representative.R061.Base.explicitTop)
          columnPerm_1084 = targetTop_1084 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1084 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 5 5 6)) 9 := by
  have htop : targetTop_1084 =
      topOfPattern (R := ℤ) (angle6 1 2 3 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1084

/-- Explicit target top block for canonical pattern `(1, 2, 3, 5, 5, 7)`. -/
def targetTop_1085 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 1, 1;
     0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1085 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 0;
     1, 0, 0]

def columnPerm_1085 : Equiv.Perm (Fin 6) where
  toFun := ![4, 2, 5, 0, 1, 3]
  invFun := ![3, 4, 1, 5, 0, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1085 : BottomDetBound targetTop_1085 9 := by
  have hU : rowTransform_1085.det.natAbs = 1 := by
    have hdet : rowTransform_1085.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Aggregate.bottomBound.transformTopRows rowTransform_1085 hU
  have hcols := hrows.permuteColumns columnPerm_1085
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1085 MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Base.explicitTop)
          columnPerm_1085 = targetTop_1085 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1085 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 5 5 7)) 9 := by
  have htop : targetTop_1085 =
      topOfPattern (R := ℤ) (angle6 1 2 3 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1085

/-- Explicit target top block for canonical pattern `(1, 2, 3, 5, 6, 6)`. -/
def targetTop_1086 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 0, 0;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1086 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1086 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 5, 3, 4]
  invFun := ![1, 0, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1086 : BottomDetBound targetTop_1086 9 := by
  have hU : rowTransform_1086.det.natAbs = 1 := by
    have hdet : rowTransform_1086.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R061.Aggregate.bottomBound.transformTopRows rowTransform_1086 hU
  have hcols := hrows.permuteColumns columnPerm_1086
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1086 MainTheory.Generated.BinaryBetaSixKernel.Representative.R061.Base.explicitTop)
          columnPerm_1086 = targetTop_1086 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1086 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 5 6 6)) 9 := by
  have htop : targetTop_1086 =
      topOfPattern (R := ℤ) (angle6 1 2 3 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1086

/-- Explicit target top block for canonical pattern `(1, 2, 3, 5, 6, 7)`. -/
def targetTop_1087 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 0, 1;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1087 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_1087 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1087 : BottomDetBound targetTop_1087 9 := by
  have hU : rowTransform_1087.det.natAbs = 1 := by
    have hdet : rowTransform_1087.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R062.Aggregate.bottomBound.transformTopRows rowTransform_1087 hU
  have hcols := hrows.permuteColumns columnPerm_1087
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1087 MainTheory.Generated.BinaryBetaSixKernel.Representative.R062.Base.explicitTop)
          columnPerm_1087 = targetTop_1087 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1087 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 5 6 7)) 9 := by
  have htop : targetTop_1087 =
      topOfPattern (R := ℤ) (angle6 1 2 3 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1087

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard067
