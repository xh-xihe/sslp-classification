-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard062

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(1, 1, 5, 5, 7, 7)`. -/
def targetTop_0992 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0992 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0992 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0992 : BottomDetBound targetTop_0992 9 := by
  have hU : rowTransform_0992.det.natAbs = 1 := by
    have hdet : rowTransform_0992.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate.bottomBound.transformTopRows rowTransform_0992 hU
  have hcols := hrows.permuteColumns columnPerm_0992
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0992 MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Base.explicitTop)
          columnPerm_0992 = targetTop_0992 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0992 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 5 5 7 7)) 9 := by
  have htop : targetTop_0992 =
      topOfPattern (R := ℤ) (angle6 1 1 5 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0992

/-- Explicit target top block for canonical pattern `(1, 1, 5, 6, 6, 6)`. -/
def targetTop_0993 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0993 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 0;
     1, 0, 1]

def columnPerm_0993 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0993 : BottomDetBound targetTop_0993 9 := by
  have hU : rowTransform_0993.det.natAbs = 1 := by
    have hdet : rowTransform_0993.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0993 hU
  have hcols := hrows.permuteColumns columnPerm_0993
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0993 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0993 = targetTop_0993 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0993 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 5 6 6 6)) 9 := by
  have htop : targetTop_0993 =
      topOfPattern (R := ℤ) (angle6 1 1 5 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0993

/-- Explicit target top block for canonical pattern `(1, 1, 5, 6, 6, 7)`. -/
def targetTop_0994 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0994 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 0;
     0, 1, 1]

def columnPerm_0994 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0994 : BottomDetBound targetTop_0994 9 := by
  have hU : rowTransform_0994.det.natAbs = 1 := by
    have hdet : rowTransform_0994.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate.bottomBound.transformTopRows rowTransform_0994 hU
  have hcols := hrows.permuteColumns columnPerm_0994
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0994 MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Base.explicitTop)
          columnPerm_0994 = targetTop_0994 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0994 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 5 6 6 7)) 9 := by
  have htop : targetTop_0994 =
      topOfPattern (R := ℤ) (angle6 1 1 5 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0994

/-- Explicit target top block for canonical pattern `(1, 1, 5, 6, 7, 7)`. -/
def targetTop_0995 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0995 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 0;
     0, 1, 1]

def columnPerm_0995 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0995 : BottomDetBound targetTop_0995 9 := by
  have hU : rowTransform_0995.det.natAbs = 1 := by
    have hdet : rowTransform_0995.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_0995 hU
  have hcols := hrows.permuteColumns columnPerm_0995
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0995 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_0995 = targetTop_0995 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0995 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 5 6 7 7)) 9 := by
  have htop : targetTop_0995 =
      topOfPattern (R := ℤ) (angle6 1 1 5 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0995

/-- Explicit target top block for canonical pattern `(1, 1, 5, 7, 7, 7)`. -/
def targetTop_0996 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0996 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     1, 0, 0;
     1, 0, 1]

def columnPerm_0996 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0996 : BottomDetBound targetTop_0996 9 := by
  have hU : rowTransform_0996.det.natAbs = 1 := by
    have hdet : rowTransform_0996.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0996 hU
  have hcols := hrows.permuteColumns columnPerm_0996
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0996 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0996 = targetTop_0996 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0996 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 5 7 7 7)) 9 := by
  have htop : targetTop_0996 =
      topOfPattern (R := ℤ) (angle6 1 1 5 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0996

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 6, 6, 6, 6)`. -/
def targetTop_0997 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0997 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0997 :
    TopRowRelation targetTop_0997 relationCoefficients_0997 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0997, relationCoefficients_0997, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0997 : BottomDetBound targetTop_0997 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0997

theorem canonicalBound_0997 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 6 6 6 6)) 9 := by
  have htop : targetTop_0997 =
      topOfPattern (R := ℤ) (angle6 1 1 6 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0997

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 6, 6, 6, 7)`. -/
def targetTop_0998 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0998 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0998 :
    TopRowRelation targetTop_0998 relationCoefficients_0998 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0998, relationCoefficients_0998, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0998 : BottomDetBound targetTop_0998 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0998

theorem canonicalBound_0998 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 6 6 6 7)) 9 := by
  have htop : targetTop_0998 =
      topOfPattern (R := ℤ) (angle6 1 1 6 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0998

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 6, 6, 7, 7)`. -/
def targetTop_0999 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0999 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0999 :
    TopRowRelation targetTop_0999 relationCoefficients_0999 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0999, relationCoefficients_0999, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0999 : BottomDetBound targetTop_0999 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0999

theorem canonicalBound_0999 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 6 6 7 7)) 9 := by
  have htop : targetTop_0999 =
      topOfPattern (R := ℤ) (angle6 1 1 6 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0999

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 6, 7, 7, 7)`. -/
def targetTop_1000 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1000 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_1000 :
    TopRowRelation targetTop_1000 relationCoefficients_1000 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1000, relationCoefficients_1000, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1000 : BottomDetBound targetTop_1000 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1000

theorem canonicalBound_1000 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 6 7 7 7)) 9 := by
  have htop : targetTop_1000 =
      topOfPattern (R := ℤ) (angle6 1 1 6 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1000

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 7, 7, 7, 7)`. -/
def targetTop_1001 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1001 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_1001 :
    TopRowRelation targetTop_1001 relationCoefficients_1001 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1001, relationCoefficients_1001, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1001 : BottomDetBound targetTop_1001 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1001

theorem canonicalBound_1001 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 7 7 7 7)) 9 := by
  have htop : targetTop_1001 =
      topOfPattern (R := ℤ) (angle6 1 1 7 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1001

/-- Explicit rank-deficient target for canonical pattern `(1, 2, 2, 2, 2, 2)`. -/
def targetTop_1002 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1002 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_1002 :
    TopRowRelation targetTop_1002 relationCoefficients_1002 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1002, relationCoefficients_1002, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1002 : BottomDetBound targetTop_1002 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1002

theorem canonicalBound_1002 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 2 2 2)) 9 := by
  have htop : targetTop_1002 =
      topOfPattern (R := ℤ) (angle6 1 2 2 2 2 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1002

/-- Explicit rank-deficient target for canonical pattern `(1, 2, 2, 2, 2, 3)`. -/
def targetTop_1003 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1003 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_1003 :
    TopRowRelation targetTop_1003 relationCoefficients_1003 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1003, relationCoefficients_1003, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1003 : BottomDetBound targetTop_1003 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1003

theorem canonicalBound_1003 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 2 2 3)) 9 := by
  have htop : targetTop_1003 =
      topOfPattern (R := ℤ) (angle6 1 2 2 2 2 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1003

/-- Explicit target top block for canonical pattern `(1, 2, 2, 2, 2, 4)`. -/
def targetTop_1004 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1004 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1004 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1004 : BottomDetBound targetTop_1004 9 := by
  have hU : rowTransform_1004.det.natAbs = 1 := by
    have hdet : rowTransform_1004.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1004 hU
  have hcols := hrows.permuteColumns columnPerm_1004
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1004 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1004 = targetTop_1004 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1004 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 2 2 4)) 9 := by
  have htop : targetTop_1004 =
      topOfPattern (R := ℤ) (angle6 1 2 2 2 2 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1004

/-- Explicit target top block for canonical pattern `(1, 2, 2, 2, 2, 5)`. -/
def targetTop_1005 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1005 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1005 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1005 : BottomDetBound targetTop_1005 9 := by
  have hU : rowTransform_1005.det.natAbs = 1 := by
    have hdet : rowTransform_1005.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1005 hU
  have hcols := hrows.permuteColumns columnPerm_1005
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1005 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1005 = targetTop_1005 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1005 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 2 2 5)) 9 := by
  have htop : targetTop_1005 =
      topOfPattern (R := ℤ) (angle6 1 2 2 2 2 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1005

/-- Explicit target top block for canonical pattern `(1, 2, 2, 2, 2, 6)`. -/
def targetTop_1006 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1006 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 1;
     0, 0, 1]

def columnPerm_1006 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1006 : BottomDetBound targetTop_1006 9 := by
  have hU : rowTransform_1006.det.natAbs = 1 := by
    have hdet : rowTransform_1006.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1006 hU
  have hcols := hrows.permuteColumns columnPerm_1006
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1006 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1006 = targetTop_1006 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1006 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 2 2 6)) 9 := by
  have htop : targetTop_1006 =
      topOfPattern (R := ℤ) (angle6 1 2 2 2 2 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1006

/-- Explicit target top block for canonical pattern `(1, 2, 2, 2, 2, 7)`. -/
def targetTop_1007 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1007 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 1;
     0, 0, 1]

def columnPerm_1007 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1007 : BottomDetBound targetTop_1007 9 := by
  have hU : rowTransform_1007.det.natAbs = 1 := by
    have hdet : rowTransform_1007.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1007 hU
  have hcols := hrows.permuteColumns columnPerm_1007
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1007 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1007 = targetTop_1007 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1007 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 2 2 7)) 9 := by
  have htop : targetTop_1007 =
      topOfPattern (R := ℤ) (angle6 1 2 2 2 2 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1007

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard062
