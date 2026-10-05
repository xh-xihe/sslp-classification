-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R050.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R056.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R059.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R060.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R063.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard069

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(1, 2, 4, 5, 5, 6)`. -/
def targetTop_1104 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 1, 0;
     0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1104 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1104 : Equiv.Perm (Fin 6) where
  toFun := ![1, 4, 0, 2, 3, 5]
  invFun := ![2, 0, 3, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1104 : BottomDetBound targetTop_1104 9 := by
  have hU : rowTransform_1104.det.natAbs = 1 := by
    have hdet : rowTransform_1104.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Aggregate.bottomBound.transformTopRows rowTransform_1104 hU
  have hcols := hrows.permuteColumns columnPerm_1104
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1104 MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Base.explicitTop)
          columnPerm_1104 = targetTop_1104 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1104 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 4 5 5 6)) 9 := by
  have htop : targetTop_1104 =
      topOfPattern (R := ℤ) (angle6 1 2 4 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1104

/-- Explicit target top block for canonical pattern `(1, 2, 4, 5, 5, 7)`. -/
def targetTop_1105 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 1, 1;
     0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1105 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_1105 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 3, 5]
  invFun := ![0, 2, 3, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1105 : BottomDetBound targetTop_1105 9 := by
  have hU : rowTransform_1105.det.natAbs = 1 := by
    have hdet : rowTransform_1105.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R056.Aggregate.bottomBound.transformTopRows rowTransform_1105 hU
  have hcols := hrows.permuteColumns columnPerm_1105
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1105 MainTheory.Generated.BinaryBetaSixKernel.Representative.R056.Base.explicitTop)
          columnPerm_1105 = targetTop_1105 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1105 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 4 5 5 7)) 9 := by
  have htop : targetTop_1105 =
      topOfPattern (R := ℤ) (angle6 1 2 4 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1105

/-- Explicit target top block for canonical pattern `(1, 2, 4, 5, 6, 6)`. -/
def targetTop_1106 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 0, 0;
     0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1106 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 0]

def columnPerm_1106 : Equiv.Perm (Fin 6) where
  toFun := ![4, 1, 0, 5, 2, 3]
  invFun := ![2, 1, 4, 5, 0, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1106 : BottomDetBound targetTop_1106 9 := by
  have hU : rowTransform_1106.det.natAbs = 1 := by
    have hdet : rowTransform_1106.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Aggregate.bottomBound.transformTopRows rowTransform_1106 hU
  have hcols := hrows.permuteColumns columnPerm_1106
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1106 MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Base.explicitTop)
          columnPerm_1106 = targetTop_1106 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1106 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 4 5 6 6)) 9 := by
  have htop : targetTop_1106 =
      topOfPattern (R := ℤ) (angle6 1 2 4 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1106

/-- Explicit target top block for canonical pattern `(1, 2, 4, 5, 6, 7)`. -/
def targetTop_1107 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 0, 1;
     0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1107 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1107 : Equiv.Perm (Fin 6) where
  toFun := ![1, 3, 0, 2, 4, 5]
  invFun := ![2, 0, 3, 1, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1107 : BottomDetBound targetTop_1107 9 := by
  have hU : rowTransform_1107.det.natAbs = 1 := by
    have hdet : rowTransform_1107.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R059.Aggregate.bottomBound.transformTopRows rowTransform_1107 hU
  have hcols := hrows.permuteColumns columnPerm_1107
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1107 MainTheory.Generated.BinaryBetaSixKernel.Representative.R059.Base.explicitTop)
          columnPerm_1107 = targetTop_1107 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1107 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 4 5 6 7)) 9 := by
  have htop : targetTop_1107 =
      topOfPattern (R := ℤ) (angle6 1 2 4 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1107

/-- Explicit target top block for canonical pattern `(1, 2, 4, 5, 7, 7)`. -/
def targetTop_1108 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 1, 1;
     0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1108 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_1108 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 4, 5]
  invFun := ![0, 2, 3, 1, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1108 : BottomDetBound targetTop_1108 9 := by
  have hU : rowTransform_1108.det.natAbs = 1 := by
    have hdet : rowTransform_1108.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R060.Aggregate.bottomBound.transformTopRows rowTransform_1108 hU
  have hcols := hrows.permuteColumns columnPerm_1108
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1108 MainTheory.Generated.BinaryBetaSixKernel.Representative.R060.Base.explicitTop)
          columnPerm_1108 = targetTop_1108 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1108 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 4 5 7 7)) 9 := by
  have htop : targetTop_1108 =
      topOfPattern (R := ℤ) (angle6 1 2 4 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1108

/-- Explicit target top block for canonical pattern `(1, 2, 4, 6, 6, 6)`. -/
def targetTop_1109 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 0;
     0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1109 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1109 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1109 : BottomDetBound targetTop_1109 9 := by
  have hU : rowTransform_1109.det.natAbs = 1 := by
    have hdet : rowTransform_1109.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Aggregate.bottomBound.transformTopRows rowTransform_1109 hU
  have hcols := hrows.permuteColumns columnPerm_1109
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1109 MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Base.explicitTop)
          columnPerm_1109 = targetTop_1109 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1109 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 4 6 6 6)) 9 := by
  have htop : targetTop_1109 =
      topOfPattern (R := ℤ) (angle6 1 2 4 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1109

/-- Explicit target top block for canonical pattern `(1, 2, 4, 6, 6, 7)`. -/
def targetTop_1110 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 1;
     0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1110 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1110 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1110 : BottomDetBound targetTop_1110 9 := by
  have hU : rowTransform_1110.det.natAbs = 1 := by
    have hdet : rowTransform_1110.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R056.Aggregate.bottomBound.transformTopRows rowTransform_1110 hU
  have hcols := hrows.permuteColumns columnPerm_1110
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1110 MainTheory.Generated.BinaryBetaSixKernel.Representative.R056.Base.explicitTop)
          columnPerm_1110 = targetTop_1110 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1110 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 4 6 6 7)) 9 := by
  have htop : targetTop_1110 =
      topOfPattern (R := ℤ) (angle6 1 2 4 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1110

/-- Explicit target top block for canonical pattern `(1, 2, 4, 6, 7, 7)`. -/
def targetTop_1111 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 1, 1;
     0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1111 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1111 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1111 : BottomDetBound targetTop_1111 9 := by
  have hU : rowTransform_1111.det.natAbs = 1 := by
    have hdet : rowTransform_1111.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R060.Aggregate.bottomBound.transformTopRows rowTransform_1111 hU
  have hcols := hrows.permuteColumns columnPerm_1111
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1111 MainTheory.Generated.BinaryBetaSixKernel.Representative.R060.Base.explicitTop)
          columnPerm_1111 = targetTop_1111 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1111 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 4 6 7 7)) 9 := by
  have htop : targetTop_1111 =
      topOfPattern (R := ℤ) (angle6 1 2 4 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1111

/-- Explicit target top block for canonical pattern `(1, 2, 4, 7, 7, 7)`. -/
def targetTop_1112 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 1, 1;
     0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1112 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_1112 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1112 : BottomDetBound targetTop_1112 9 := by
  have hU : rowTransform_1112.det.natAbs = 1 := by
    have hdet : rowTransform_1112.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R063.Aggregate.bottomBound.transformTopRows rowTransform_1112 hU
  have hcols := hrows.permuteColumns columnPerm_1112
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1112 MainTheory.Generated.BinaryBetaSixKernel.Representative.R063.Base.explicitTop)
          columnPerm_1112 = targetTop_1112 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1112 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 4 7 7 7)) 9 := by
  have htop : targetTop_1112 =
      topOfPattern (R := ℤ) (angle6 1 2 4 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1112

/-- Explicit target top block for canonical pattern `(1, 2, 5, 5, 5, 5)`. -/
def targetTop_1113 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 1, 1;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1113 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1113 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1113 : BottomDetBound targetTop_1113 9 := by
  have hU : rowTransform_1113.det.natAbs = 1 := by
    have hdet : rowTransform_1113.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1113 hU
  have hcols := hrows.permuteColumns columnPerm_1113
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1113 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1113 = targetTop_1113 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1113 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 5 5 5 5)) 9 := by
  have htop : targetTop_1113 =
      topOfPattern (R := ℤ) (angle6 1 2 5 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1113

/-- Explicit target top block for canonical pattern `(1, 2, 5, 5, 5, 6)`. -/
def targetTop_1114 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 1, 0;
     0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1114 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, (-1);
     0, 0, 1;
     1, 0, 0]

def columnPerm_1114 : Equiv.Perm (Fin 6) where
  toFun := ![3, 5, 0, 1, 2, 4]
  invFun := ![2, 3, 4, 0, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1114 : BottomDetBound targetTop_1114 9 := by
  have hU : rowTransform_1114.det.natAbs = 1 := by
    have hdet : rowTransform_1114.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate.bottomBound.transformTopRows rowTransform_1114 hU
  have hcols := hrows.permuteColumns columnPerm_1114
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1114 MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Base.explicitTop)
          columnPerm_1114 = targetTop_1114 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1114 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 5 5 5 6)) 9 := by
  have htop : targetTop_1114 =
      topOfPattern (R := ℤ) (angle6 1 2 5 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1114

/-- Explicit target top block for canonical pattern `(1, 2, 5, 5, 5, 7)`. -/
def targetTop_1115 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 1, 1;
     0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1115 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 0;
     1, 0, 0]

def columnPerm_1115 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 0, 1, 2, 4]
  invFun := ![2, 3, 4, 1, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1115 : BottomDetBound targetTop_1115 9 := by
  have hU : rowTransform_1115.det.natAbs = 1 := by
    have hdet : rowTransform_1115.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_1115 hU
  have hcols := hrows.permuteColumns columnPerm_1115
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1115 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_1115 = targetTop_1115 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1115 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 5 5 5 7)) 9 := by
  have htop : targetTop_1115 =
      topOfPattern (R := ℤ) (angle6 1 2 5 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1115

/-- Explicit target top block for canonical pattern `(1, 2, 5, 5, 6, 6)`. -/
def targetTop_1116 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 0, 0;
     0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1116 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     1, 1, (-1)]

def columnPerm_1116 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1116 : BottomDetBound targetTop_1116 9 := by
  have hU : rowTransform_1116.det.natAbs = 1 := by
    have hdet : rowTransform_1116.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate.bottomBound.transformTopRows rowTransform_1116 hU
  have hcols := hrows.permuteColumns columnPerm_1116
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1116 MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Base.explicitTop)
          columnPerm_1116 = targetTop_1116 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1116 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 5 5 6 6)) 9 := by
  have htop : targetTop_1116 =
      topOfPattern (R := ℤ) (angle6 1 2 5 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1116

/-- Explicit target top block for canonical pattern `(1, 2, 5, 5, 6, 7)`. -/
def targetTop_1117 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 0, 1;
     0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1117 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, (-1);
     0, 0, 1;
     1, 0, 0]

def columnPerm_1117 : Equiv.Perm (Fin 6) where
  toFun := ![2, 4, 0, 1, 3, 5]
  invFun := ![2, 3, 0, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1117 : BottomDetBound targetTop_1117 9 := by
  have hU : rowTransform_1117.det.natAbs = 1 := by
    have hdet : rowTransform_1117.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R050.Aggregate.bottomBound.transformTopRows rowTransform_1117 hU
  have hcols := hrows.permuteColumns columnPerm_1117
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1117 MainTheory.Generated.BinaryBetaSixKernel.Representative.R050.Base.explicitTop)
          columnPerm_1117 = targetTop_1117 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1117 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 5 5 6 7)) 9 := by
  have htop : targetTop_1117 =
      topOfPattern (R := ℤ) (angle6 1 2 5 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1117

/-- Explicit target top block for canonical pattern `(1, 2, 5, 5, 7, 7)`. -/
def targetTop_1118 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 1, 1;
     0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1118 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 0;
     1, 0, 0]

def columnPerm_1118 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 0, 1, 3, 4]
  invFun := ![2, 3, 1, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1118 : BottomDetBound targetTop_1118 9 := by
  have hU : rowTransform_1118.det.natAbs = 1 := by
    have hdet : rowTransform_1118.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_1118 hU
  have hcols := hrows.permuteColumns columnPerm_1118
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1118 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_1118 = targetTop_1118 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1118 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 5 5 7 7)) 9 := by
  have htop : targetTop_1118 =
      topOfPattern (R := ℤ) (angle6 1 2 5 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1118

/-- Explicit target top block for canonical pattern `(1, 2, 5, 6, 6, 6)`. -/
def targetTop_1119 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 0, 0, 0;
     0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1119 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, (-1);
     1, 0, 0]

def columnPerm_1119 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1119 : BottomDetBound targetTop_1119 9 := by
  have hU : rowTransform_1119.det.natAbs = 1 := by
    have hdet : rowTransform_1119.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate.bottomBound.transformTopRows rowTransform_1119 hU
  have hcols := hrows.permuteColumns columnPerm_1119
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1119 MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Base.explicitTop)
          columnPerm_1119 = targetTop_1119 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1119 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 5 6 6 6)) 9 := by
  have htop : targetTop_1119 =
      topOfPattern (R := ℤ) (angle6 1 2 5 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1119

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard069
