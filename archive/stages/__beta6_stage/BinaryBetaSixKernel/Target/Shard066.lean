-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R056.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R057.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard066

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(1, 2, 2, 6, 7, 7)`. -/
def targetTop_1056 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1056 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 1;
     0, 0, 1]

def columnPerm_1056 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1056 : BottomDetBound targetTop_1056 9 := by
  have hU : rowTransform_1056.det.natAbs = 1 := by
    have hdet : rowTransform_1056.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate.bottomBound.transformTopRows rowTransform_1056 hU
  have hcols := hrows.permuteColumns columnPerm_1056
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1056 MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Base.explicitTop)
          columnPerm_1056 = targetTop_1056 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1056 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 6 7 7)) 9 := by
  have htop : targetTop_1056 =
      topOfPattern (R := ℤ) (angle6 1 2 2 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1056

/-- Explicit target top block for canonical pattern `(1, 2, 2, 7, 7, 7)`. -/
def targetTop_1057 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1057 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 1, 0;
     1, 0, 0]

def columnPerm_1057 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1057 : BottomDetBound targetTop_1057 9 := by
  have hU : rowTransform_1057.det.natAbs = 1 := by
    have hdet : rowTransform_1057.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1057 hU
  have hcols := hrows.permuteColumns columnPerm_1057
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1057 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1057 = targetTop_1057 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1057 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 7 7 7)) 9 := by
  have htop : targetTop_1057 =
      topOfPattern (R := ℤ) (angle6 1 2 2 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1057

/-- Explicit rank-deficient target for canonical pattern `(1, 2, 3, 3, 3, 3)`. -/
def targetTop_1058 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1058 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_1058 :
    TopRowRelation targetTop_1058 relationCoefficients_1058 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1058, relationCoefficients_1058, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1058 : BottomDetBound targetTop_1058 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1058

theorem canonicalBound_1058 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 3 3 3)) 9 := by
  have htop : targetTop_1058 =
      topOfPattern (R := ℤ) (angle6 1 2 3 3 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1058

/-- Explicit target top block for canonical pattern `(1, 2, 3, 3, 3, 4)`. -/
def targetTop_1059 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 1, 0;
     0, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1059 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_1059 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1059 : BottomDetBound targetTop_1059 9 := by
  have hU : rowTransform_1059.det.natAbs = 1 := by
    have hdet : rowTransform_1059.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Aggregate.bottomBound.transformTopRows rowTransform_1059 hU
  have hcols := hrows.permuteColumns columnPerm_1059
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1059 MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Base.explicitTop)
          columnPerm_1059 = targetTop_1059 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1059 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 3 3 4)) 9 := by
  have htop : targetTop_1059 =
      topOfPattern (R := ℤ) (angle6 1 2 3 3 3 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1059

/-- Explicit target top block for canonical pattern `(1, 2, 3, 3, 3, 5)`. -/
def targetTop_1060 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1060 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 0;
     0, 0, 1]

def columnPerm_1060 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1060 : BottomDetBound targetTop_1060 9 := by
  have hU : rowTransform_1060.det.natAbs = 1 := by
    have hdet : rowTransform_1060.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Aggregate.bottomBound.transformTopRows rowTransform_1060 hU
  have hcols := hrows.permuteColumns columnPerm_1060
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1060 MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Base.explicitTop)
          columnPerm_1060 = targetTop_1060 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1060 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 3 3 5)) 9 := by
  have htop : targetTop_1060 =
      topOfPattern (R := ℤ) (angle6 1 2 3 3 3 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1060

/-- Explicit target top block for canonical pattern `(1, 2, 3, 3, 3, 6)`. -/
def targetTop_1061 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 1, 0;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1061 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     0, 0, 1]

def columnPerm_1061 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1061 : BottomDetBound targetTop_1061 9 := by
  have hU : rowTransform_1061.det.natAbs = 1 := by
    have hdet : rowTransform_1061.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Aggregate.bottomBound.transformTopRows rowTransform_1061 hU
  have hcols := hrows.permuteColumns columnPerm_1061
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1061 MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Base.explicitTop)
          columnPerm_1061 = targetTop_1061 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1061 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 3 3 6)) 9 := by
  have htop : targetTop_1061 =
      topOfPattern (R := ℤ) (angle6 1 2 3 3 3 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1061

/-- Explicit target top block for canonical pattern `(1, 2, 3, 3, 3, 7)`. -/
def targetTop_1062 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1062 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 1;
     0, 0, 1]

def columnPerm_1062 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1062 : BottomDetBound targetTop_1062 9 := by
  have hU : rowTransform_1062.det.natAbs = 1 := by
    have hdet : rowTransform_1062.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Aggregate.bottomBound.transformTopRows rowTransform_1062 hU
  have hcols := hrows.permuteColumns columnPerm_1062
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1062 MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Base.explicitTop)
          columnPerm_1062 = targetTop_1062 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1062 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 3 3 7)) 9 := by
  have htop : targetTop_1062 =
      topOfPattern (R := ℤ) (angle6 1 2 3 3 3 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1062

/-- Explicit target top block for canonical pattern `(1, 2, 3, 3, 4, 4)`. -/
def targetTop_1063 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 0, 0;
     0, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1063 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1063 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 4, 5, 0, 1]
  invFun := ![4, 5, 0, 1, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1063 : BottomDetBound targetTop_1063 9 := by
  have hU : rowTransform_1063.det.natAbs = 1 := by
    have hdet : rowTransform_1063.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate.bottomBound.transformTopRows rowTransform_1063 hU
  have hcols := hrows.permuteColumns columnPerm_1063
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1063 MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Base.explicitTop)
          columnPerm_1063 = targetTop_1063 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1063 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 3 4 4)) 9 := by
  have htop : targetTop_1063 =
      topOfPattern (R := ℤ) (angle6 1 2 3 3 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1063

/-- Explicit target top block for canonical pattern `(1, 2, 3, 3, 4, 5)`. -/
def targetTop_1064 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 0, 1;
     0, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1064 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_1064 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1064 : BottomDetBound targetTop_1064 9 := by
  have hU : rowTransform_1064.det.natAbs = 1 := by
    have hdet : rowTransform_1064.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Aggregate.bottomBound.transformTopRows rowTransform_1064 hU
  have hcols := hrows.permuteColumns columnPerm_1064
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1064 MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Base.explicitTop)
          columnPerm_1064 = targetTop_1064 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1064 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 3 4 5)) 9 := by
  have htop : targetTop_1064 =
      topOfPattern (R := ℤ) (angle6 1 2 3 3 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1064

/-- Explicit target top block for canonical pattern `(1, 2, 3, 3, 4, 6)`. -/
def targetTop_1065 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 0, 0;
     0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1065 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1065 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1065 : BottomDetBound targetTop_1065 9 := by
  have hU : rowTransform_1065.det.natAbs = 1 := by
    have hdet : rowTransform_1065.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Aggregate.bottomBound.transformTopRows rowTransform_1065 hU
  have hcols := hrows.permuteColumns columnPerm_1065
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1065 MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Base.explicitTop)
          columnPerm_1065 = targetTop_1065 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1065 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 3 4 6)) 9 := by
  have htop : targetTop_1065 =
      topOfPattern (R := ℤ) (angle6 1 2 3 3 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1065

/-- Explicit target top block for canonical pattern `(1, 2, 3, 3, 4, 7)`. -/
def targetTop_1066 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 0, 1;
     0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1066 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_1066 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1066 : BottomDetBound targetTop_1066 9 := by
  have hU : rowTransform_1066.det.natAbs = 1 := by
    have hdet : rowTransform_1066.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R056.Aggregate.bottomBound.transformTopRows rowTransform_1066 hU
  have hcols := hrows.permuteColumns columnPerm_1066
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1066 MainTheory.Generated.BinaryBetaSixKernel.Representative.R056.Base.explicitTop)
          columnPerm_1066 = targetTop_1066 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1066 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 3 4 7)) 9 := by
  have htop : targetTop_1066 =
      topOfPattern (R := ℤ) (angle6 1 2 3 3 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1066

/-- Explicit target top block for canonical pattern `(1, 2, 3, 3, 5, 5)`. -/
def targetTop_1067 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1067 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1067 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 4, 5, 0, 1]
  invFun := ![4, 5, 0, 1, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1067 : BottomDetBound targetTop_1067 9 := by
  have hU : rowTransform_1067.det.natAbs = 1 := by
    have hdet : rowTransform_1067.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate.bottomBound.transformTopRows rowTransform_1067 hU
  have hcols := hrows.permuteColumns columnPerm_1067
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1067 MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Base.explicitTop)
          columnPerm_1067 = targetTop_1067 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1067 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 3 5 5)) 9 := by
  have htop : targetTop_1067 =
      topOfPattern (R := ℤ) (angle6 1 2 3 3 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1067

/-- Explicit target top block for canonical pattern `(1, 2, 3, 3, 5, 6)`. -/
def targetTop_1068 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 1, 0;
     0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1068 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_1068 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1068 : BottomDetBound targetTop_1068 9 := by
  have hU : rowTransform_1068.det.natAbs = 1 := by
    have hdet : rowTransform_1068.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R057.Aggregate.bottomBound.transformTopRows rowTransform_1068 hU
  have hcols := hrows.permuteColumns columnPerm_1068
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1068 MainTheory.Generated.BinaryBetaSixKernel.Representative.R057.Base.explicitTop)
          columnPerm_1068 = targetTop_1068 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1068 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 3 5 6)) 9 := by
  have htop : targetTop_1068 =
      topOfPattern (R := ℤ) (angle6 1 2 3 3 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1068

/-- Explicit target top block for canonical pattern `(1, 2, 3, 3, 5, 7)`. -/
def targetTop_1069 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1069 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1069 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1069 : BottomDetBound targetTop_1069 9 := by
  have hU : rowTransform_1069.det.natAbs = 1 := by
    have hdet : rowTransform_1069.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Aggregate.bottomBound.transformTopRows rowTransform_1069 hU
  have hcols := hrows.permuteColumns columnPerm_1069
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1069 MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Base.explicitTop)
          columnPerm_1069 = targetTop_1069 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1069 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 3 5 7)) 9 := by
  have htop : targetTop_1069 =
      topOfPattern (R := ℤ) (angle6 1 2 3 3 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1069

/-- Explicit target top block for canonical pattern `(1, 2, 3, 3, 6, 6)`. -/
def targetTop_1070 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 0, 0;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1070 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 1;
     1, 0, 0]

def columnPerm_1070 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 4, 5, 0, 1]
  invFun := ![4, 5, 0, 1, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1070 : BottomDetBound targetTop_1070 9 := by
  have hU : rowTransform_1070.det.natAbs = 1 := by
    have hdet : rowTransform_1070.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate.bottomBound.transformTopRows rowTransform_1070 hU
  have hcols := hrows.permuteColumns columnPerm_1070
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1070 MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Base.explicitTop)
          columnPerm_1070 = targetTop_1070 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1070 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 3 6 6)) 9 := by
  have htop : targetTop_1070 =
      topOfPattern (R := ℤ) (angle6 1 2 3 3 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1070

/-- Explicit target top block for canonical pattern `(1, 2, 3, 3, 6, 7)`. -/
def targetTop_1071 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 0, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1071 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     0, 0, 1]

def columnPerm_1071 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1071 : BottomDetBound targetTop_1071 9 := by
  have hU : rowTransform_1071.det.natAbs = 1 := by
    have hdet : rowTransform_1071.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Aggregate.bottomBound.transformTopRows rowTransform_1071 hU
  have hcols := hrows.permuteColumns columnPerm_1071
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1071 MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Base.explicitTop)
          columnPerm_1071 = targetTop_1071 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1071 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 3 6 7)) 9 := by
  have htop : targetTop_1071 =
      topOfPattern (R := ℤ) (angle6 1 2 3 3 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1071

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard066
