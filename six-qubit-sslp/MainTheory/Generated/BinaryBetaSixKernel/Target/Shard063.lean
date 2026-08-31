-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R033.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard063

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit rank-deficient target for canonical pattern `(1, 2, 2, 2, 3, 3)`. -/
def targetTop_1008 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1008 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_1008 :
    TopRowRelation targetTop_1008 relationCoefficients_1008 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1008, relationCoefficients_1008, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1008 : BottomDetBound targetTop_1008 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1008

theorem canonicalBound_1008 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 2 3 3)) 9 := by
  have htop : targetTop_1008 =
      topOfPattern (R := ℤ) (angle6 1 2 2 2 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1008

/-- Explicit target top block for canonical pattern `(1, 2, 2, 2, 3, 4)`. -/
def targetTop_1009 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 1, 0;
     0, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1009 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1009 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1009 : BottomDetBound targetTop_1009 9 := by
  have hU : rowTransform_1009.det.natAbs = 1 := by
    have hdet : rowTransform_1009.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_1009 hU
  have hcols := hrows.permuteColumns columnPerm_1009
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1009 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_1009 = targetTop_1009 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1009 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 2 3 4)) 9 := by
  have htop : targetTop_1009 =
      topOfPattern (R := ℤ) (angle6 1 2 2 2 3 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1009

/-- Explicit target top block for canonical pattern `(1, 2, 2, 2, 3, 5)`. -/
def targetTop_1010 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1010 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1010 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1010 : BottomDetBound targetTop_1010 9 := by
  have hU : rowTransform_1010.det.natAbs = 1 := by
    have hdet : rowTransform_1010.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_1010 hU
  have hcols := hrows.permuteColumns columnPerm_1010
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1010 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_1010 = targetTop_1010 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1010 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 2 3 5)) 9 := by
  have htop : targetTop_1010 =
      topOfPattern (R := ℤ) (angle6 1 2 2 2 3 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1010

/-- Explicit target top block for canonical pattern `(1, 2, 2, 2, 3, 6)`. -/
def targetTop_1011 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 1, 0;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1011 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 1;
     0, 0, 1]

def columnPerm_1011 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1011 : BottomDetBound targetTop_1011 9 := by
  have hU : rowTransform_1011.det.natAbs = 1 := by
    have hdet : rowTransform_1011.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_1011 hU
  have hcols := hrows.permuteColumns columnPerm_1011
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1011 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_1011 = targetTop_1011 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1011 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 2 3 6)) 9 := by
  have htop : targetTop_1011 =
      topOfPattern (R := ℤ) (angle6 1 2 2 2 3 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1011

/-- Explicit target top block for canonical pattern `(1, 2, 2, 2, 3, 7)`. -/
def targetTop_1012 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1012 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 1;
     0, 0, 1]

def columnPerm_1012 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1012 : BottomDetBound targetTop_1012 9 := by
  have hU : rowTransform_1012.det.natAbs = 1 := by
    have hdet : rowTransform_1012.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_1012 hU
  have hcols := hrows.permuteColumns columnPerm_1012
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1012 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_1012 = targetTop_1012 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1012 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 2 3 7)) 9 := by
  have htop : targetTop_1012 =
      topOfPattern (R := ℤ) (angle6 1 2 2 2 3 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1012

/-- Explicit target top block for canonical pattern `(1, 2, 2, 2, 4, 4)`. -/
def targetTop_1013 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1013 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1013 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1013 : BottomDetBound targetTop_1013 9 := by
  have hU : rowTransform_1013.det.natAbs = 1 := by
    have hdet : rowTransform_1013.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1013 hU
  have hcols := hrows.permuteColumns columnPerm_1013
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1013 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1013 = targetTop_1013 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1013 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 2 4 4)) 9 := by
  have htop : targetTop_1013 =
      topOfPattern (R := ℤ) (angle6 1 2 2 2 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1013

/-- Explicit target top block for canonical pattern `(1, 2, 2, 2, 4, 5)`. -/
def targetTop_1014 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1014 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1014 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1014 : BottomDetBound targetTop_1014 9 := by
  have hU : rowTransform_1014.det.natAbs = 1 := by
    have hdet : rowTransform_1014.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate.bottomBound.transformTopRows rowTransform_1014 hU
  have hcols := hrows.permuteColumns columnPerm_1014
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1014 MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Base.explicitTop)
          columnPerm_1014 = targetTop_1014 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1014 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 2 4 5)) 9 := by
  have htop : targetTop_1014 =
      topOfPattern (R := ℤ) (angle6 1 2 2 2 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1014

/-- Explicit target top block for canonical pattern `(1, 2, 2, 2, 4, 6)`. -/
def targetTop_1015 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1015 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1015 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1015 : BottomDetBound targetTop_1015 9 := by
  have hU : rowTransform_1015.det.natAbs = 1 := by
    have hdet : rowTransform_1015.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_1015 hU
  have hcols := hrows.permuteColumns columnPerm_1015
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1015 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_1015 = targetTop_1015 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1015 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 2 4 6)) 9 := by
  have htop : targetTop_1015 =
      topOfPattern (R := ℤ) (angle6 1 2 2 2 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1015

/-- Explicit target top block for canonical pattern `(1, 2, 2, 2, 4, 7)`. -/
def targetTop_1016 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1016 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1016 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1016 : BottomDetBound targetTop_1016 9 := by
  have hU : rowTransform_1016.det.natAbs = 1 := by
    have hdet : rowTransform_1016.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R033.Aggregate.bottomBound.transformTopRows rowTransform_1016 hU
  have hcols := hrows.permuteColumns columnPerm_1016
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1016 MainTheory.Generated.BinaryBetaSixKernel.Representative.R033.Base.explicitTop)
          columnPerm_1016 = targetTop_1016 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1016 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 2 4 7)) 9 := by
  have htop : targetTop_1016 =
      topOfPattern (R := ℤ) (angle6 1 2 2 2 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1016

/-- Explicit target top block for canonical pattern `(1, 2, 2, 2, 5, 5)`. -/
def targetTop_1017 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1017 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1017 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1017 : BottomDetBound targetTop_1017 9 := by
  have hU : rowTransform_1017.det.natAbs = 1 := by
    have hdet : rowTransform_1017.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1017 hU
  have hcols := hrows.permuteColumns columnPerm_1017
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1017 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1017 = targetTop_1017 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1017 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 2 5 5)) 9 := by
  have htop : targetTop_1017 =
      topOfPattern (R := ℤ) (angle6 1 2 2 2 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1017

/-- Explicit target top block for canonical pattern `(1, 2, 2, 2, 5, 6)`. -/
def targetTop_1018 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 1, 0;
     0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1018 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1018 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 5, 4]
  invFun := ![1, 2, 3, 0, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1018 : BottomDetBound targetTop_1018 9 := by
  have hU : rowTransform_1018.det.natAbs = 1 := by
    have hdet : rowTransform_1018.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate.bottomBound.transformTopRows rowTransform_1018 hU
  have hcols := hrows.permuteColumns columnPerm_1018
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1018 MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Base.explicitTop)
          columnPerm_1018 = targetTop_1018 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1018 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 2 5 6)) 9 := by
  have htop : targetTop_1018 =
      topOfPattern (R := ℤ) (angle6 1 2 2 2 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1018

/-- Explicit target top block for canonical pattern `(1, 2, 2, 2, 5, 7)`. -/
def targetTop_1019 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1019 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1019 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1019 : BottomDetBound targetTop_1019 9 := by
  have hU : rowTransform_1019.det.natAbs = 1 := by
    have hdet : rowTransform_1019.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_1019 hU
  have hcols := hrows.permuteColumns columnPerm_1019
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1019 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_1019 = targetTop_1019 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1019 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 2 5 7)) 9 := by
  have htop : targetTop_1019 =
      topOfPattern (R := ℤ) (angle6 1 2 2 2 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1019

/-- Explicit target top block for canonical pattern `(1, 2, 2, 2, 6, 6)`. -/
def targetTop_1020 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1020 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, 0;
     0, 1, 0]

def columnPerm_1020 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1020 : BottomDetBound targetTop_1020 9 := by
  have hU : rowTransform_1020.det.natAbs = 1 := by
    have hdet : rowTransform_1020.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1020 hU
  have hcols := hrows.permuteColumns columnPerm_1020
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1020 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1020 = targetTop_1020 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1020 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 2 6 6)) 9 := by
  have htop : targetTop_1020 =
      topOfPattern (R := ℤ) (angle6 1 2 2 2 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1020

/-- Explicit target top block for canonical pattern `(1, 2, 2, 2, 6, 7)`. -/
def targetTop_1021 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1021 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 1;
     0, 0, 1]

def columnPerm_1021 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1021 : BottomDetBound targetTop_1021 9 := by
  have hU : rowTransform_1021.det.natAbs = 1 := by
    have hdet : rowTransform_1021.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate.bottomBound.transformTopRows rowTransform_1021 hU
  have hcols := hrows.permuteColumns columnPerm_1021
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1021 MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Base.explicitTop)
          columnPerm_1021 = targetTop_1021 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1021 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 2 6 7)) 9 := by
  have htop : targetTop_1021 =
      topOfPattern (R := ℤ) (angle6 1 2 2 2 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1021

/-- Explicit target top block for canonical pattern `(1, 2, 2, 2, 7, 7)`. -/
def targetTop_1022 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1022 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 1, 0;
     0, 1, 0]

def columnPerm_1022 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1022 : BottomDetBound targetTop_1022 9 := by
  have hU : rowTransform_1022.det.natAbs = 1 := by
    have hdet : rowTransform_1022.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1022 hU
  have hcols := hrows.permuteColumns columnPerm_1022
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1022 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1022 = targetTop_1022 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1022 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 2 7 7)) 9 := by
  have htop : targetTop_1022 =
      topOfPattern (R := ℤ) (angle6 1 2 2 2 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1022

/-- Explicit rank-deficient target for canonical pattern `(1, 2, 2, 3, 3, 3)`. -/
def targetTop_1023 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1023 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_1023 :
    TopRowRelation targetTop_1023 relationCoefficients_1023 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1023, relationCoefficients_1023, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1023 : BottomDetBound targetTop_1023 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1023

theorem canonicalBound_1023 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 3 3 3)) 9 := by
  have htop : targetTop_1023 =
      topOfPattern (R := ℤ) (angle6 1 2 2 3 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1023

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard063
