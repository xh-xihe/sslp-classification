-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R042.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R044.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R045.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard064

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(1, 2, 2, 3, 3, 4)`. -/
def targetTop_1024 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 1, 0;
     0, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1024 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1024 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1024 : BottomDetBound targetTop_1024 9 := by
  have hU : rowTransform_1024.det.natAbs = 1 := by
    have hdet : rowTransform_1024.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_1024 hU
  have hcols := hrows.permuteColumns columnPerm_1024
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1024 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_1024 = targetTop_1024 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1024 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 3 3 4)) 9 := by
  have htop : targetTop_1024 =
      topOfPattern (R := ℤ) (angle6 1 2 2 3 3 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1024

/-- Explicit target top block for canonical pattern `(1, 2, 2, 3, 3, 5)`. -/
def targetTop_1025 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1025 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1025 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1025 : BottomDetBound targetTop_1025 9 := by
  have hU : rowTransform_1025.det.natAbs = 1 := by
    have hdet : rowTransform_1025.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_1025 hU
  have hcols := hrows.permuteColumns columnPerm_1025
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1025 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_1025 = targetTop_1025 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1025 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 3 3 5)) 9 := by
  have htop : targetTop_1025 =
      topOfPattern (R := ℤ) (angle6 1 2 2 3 3 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1025

/-- Explicit target top block for canonical pattern `(1, 2, 2, 3, 3, 6)`. -/
def targetTop_1026 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 1, 0;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1026 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 1;
     0, 0, 1]

def columnPerm_1026 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1026 : BottomDetBound targetTop_1026 9 := by
  have hU : rowTransform_1026.det.natAbs = 1 := by
    have hdet : rowTransform_1026.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_1026 hU
  have hcols := hrows.permuteColumns columnPerm_1026
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1026 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_1026 = targetTop_1026 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1026 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 3 3 6)) 9 := by
  have htop : targetTop_1026 =
      topOfPattern (R := ℤ) (angle6 1 2 2 3 3 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1026

/-- Explicit target top block for canonical pattern `(1, 2, 2, 3, 3, 7)`. -/
def targetTop_1027 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1027 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 1;
     0, 0, 1]

def columnPerm_1027 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1027 : BottomDetBound targetTop_1027 9 := by
  have hU : rowTransform_1027.det.natAbs = 1 := by
    have hdet : rowTransform_1027.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_1027 hU
  have hcols := hrows.permuteColumns columnPerm_1027
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1027 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_1027 = targetTop_1027 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1027 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 3 3 7)) 9 := by
  have htop : targetTop_1027 =
      topOfPattern (R := ℤ) (angle6 1 2 2 3 3 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1027

/-- Explicit target top block for canonical pattern `(1, 2, 2, 3, 4, 4)`. -/
def targetTop_1028 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 0, 0;
     0, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1028 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1028 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 5, 2, 3]
  invFun := ![1, 2, 4, 5, 0, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1028 : BottomDetBound targetTop_1028 9 := by
  have hU : rowTransform_1028.det.natAbs = 1 := by
    have hdet : rowTransform_1028.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_1028 hU
  have hcols := hrows.permuteColumns columnPerm_1028
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1028 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_1028 = targetTop_1028 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1028 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 3 4 4)) 9 := by
  have htop : targetTop_1028 =
      topOfPattern (R := ℤ) (angle6 1 2 2 3 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1028

/-- Explicit target top block for canonical pattern `(1, 2, 2, 3, 4, 5)`. -/
def targetTop_1029 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 0, 1;
     0, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1029 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1029 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1029 : BottomDetBound targetTop_1029 9 := by
  have hU : rowTransform_1029.det.natAbs = 1 := by
    have hdet : rowTransform_1029.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Aggregate.bottomBound.transformTopRows rowTransform_1029 hU
  have hcols := hrows.permuteColumns columnPerm_1029
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1029 MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Base.explicitTop)
          columnPerm_1029 = targetTop_1029 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1029 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 3 4 5)) 9 := by
  have htop : targetTop_1029 =
      topOfPattern (R := ℤ) (angle6 1 2 2 3 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1029

/-- Explicit target top block for canonical pattern `(1, 2, 2, 3, 4, 6)`. -/
def targetTop_1030 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 0, 0;
     0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1030 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1030 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1030 : BottomDetBound targetTop_1030 9 := by
  have hU : rowTransform_1030.det.natAbs = 1 := by
    have hdet : rowTransform_1030.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R042.Aggregate.bottomBound.transformTopRows rowTransform_1030 hU
  have hcols := hrows.permuteColumns columnPerm_1030
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1030 MainTheory.Generated.BinaryBetaSixKernel.Representative.R042.Base.explicitTop)
          columnPerm_1030 = targetTop_1030 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1030 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 3 4 6)) 9 := by
  have htop : targetTop_1030 =
      topOfPattern (R := ℤ) (angle6 1 2 2 3 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1030

/-- Explicit target top block for canonical pattern `(1, 2, 2, 3, 4, 7)`. -/
def targetTop_1031 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 0, 1;
     0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1031 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1031 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1031 : BottomDetBound targetTop_1031 9 := by
  have hU : rowTransform_1031.det.natAbs = 1 := by
    have hdet : rowTransform_1031.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R044.Aggregate.bottomBound.transformTopRows rowTransform_1031 hU
  have hcols := hrows.permuteColumns columnPerm_1031
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1031 MainTheory.Generated.BinaryBetaSixKernel.Representative.R044.Base.explicitTop)
          columnPerm_1031 = targetTop_1031 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1031 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 3 4 7)) 9 := by
  have htop : targetTop_1031 =
      topOfPattern (R := ℤ) (angle6 1 2 2 3 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1031

/-- Explicit target top block for canonical pattern `(1, 2, 2, 3, 5, 5)`. -/
def targetTop_1032 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1032 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1032 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 5, 2, 3]
  invFun := ![1, 2, 4, 5, 0, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1032 : BottomDetBound targetTop_1032 9 := by
  have hU : rowTransform_1032.det.natAbs = 1 := by
    have hdet : rowTransform_1032.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_1032 hU
  have hcols := hrows.permuteColumns columnPerm_1032
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1032 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_1032 = targetTop_1032 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1032 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 3 5 5)) 9 := by
  have htop : targetTop_1032 =
      topOfPattern (R := ℤ) (angle6 1 2 2 3 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1032

/-- Explicit target top block for canonical pattern `(1, 2, 2, 3, 5, 6)`. -/
def targetTop_1033 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 1, 0;
     0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1033 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1033 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 5, 4]
  invFun := ![1, 2, 0, 3, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1033 : BottomDetBound targetTop_1033 9 := by
  have hU : rowTransform_1033.det.natAbs = 1 := by
    have hdet : rowTransform_1033.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R045.Aggregate.bottomBound.transformTopRows rowTransform_1033 hU
  have hcols := hrows.permuteColumns columnPerm_1033
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1033 MainTheory.Generated.BinaryBetaSixKernel.Representative.R045.Base.explicitTop)
          columnPerm_1033 = targetTop_1033 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1033 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 3 5 6)) 9 := by
  have htop : targetTop_1033 =
      topOfPattern (R := ℤ) (angle6 1 2 2 3 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1033

/-- Explicit target top block for canonical pattern `(1, 2, 2, 3, 5, 7)`. -/
def targetTop_1034 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1034 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1034 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1034 : BottomDetBound targetTop_1034 9 := by
  have hU : rowTransform_1034.det.natAbs = 1 := by
    have hdet : rowTransform_1034.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R042.Aggregate.bottomBound.transformTopRows rowTransform_1034 hU
  have hcols := hrows.permuteColumns columnPerm_1034
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1034 MainTheory.Generated.BinaryBetaSixKernel.Representative.R042.Base.explicitTop)
          columnPerm_1034 = targetTop_1034 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1034 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 3 5 7)) 9 := by
  have htop : targetTop_1034 =
      topOfPattern (R := ℤ) (angle6 1 2 2 3 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1034

/-- Explicit target top block for canonical pattern `(1, 2, 2, 3, 6, 6)`. -/
def targetTop_1035 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 0, 0;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1035 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, 0;
     0, 1, 0]

def columnPerm_1035 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 5, 2, 3]
  invFun := ![1, 2, 4, 5, 0, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1035 : BottomDetBound targetTop_1035 9 := by
  have hU : rowTransform_1035.det.natAbs = 1 := by
    have hdet : rowTransform_1035.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_1035 hU
  have hcols := hrows.permuteColumns columnPerm_1035
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1035 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_1035 = targetTop_1035 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1035 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 3 6 6)) 9 := by
  have htop : targetTop_1035 =
      topOfPattern (R := ℤ) (angle6 1 2 2 3 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1035

/-- Explicit target top block for canonical pattern `(1, 2, 2, 3, 6, 7)`. -/
def targetTop_1036 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 0, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1036 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 1;
     0, 0, 1]

def columnPerm_1036 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1036 : BottomDetBound targetTop_1036 9 := by
  have hU : rowTransform_1036.det.natAbs = 1 := by
    have hdet : rowTransform_1036.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Aggregate.bottomBound.transformTopRows rowTransform_1036 hU
  have hcols := hrows.permuteColumns columnPerm_1036
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1036 MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Base.explicitTop)
          columnPerm_1036 = targetTop_1036 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1036 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 3 6 7)) 9 := by
  have htop : targetTop_1036 =
      topOfPattern (R := ℤ) (angle6 1 2 2 3 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1036

/-- Explicit target top block for canonical pattern `(1, 2, 2, 3, 7, 7)`. -/
def targetTop_1037 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1037 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 1, 0;
     0, 1, 0]

def columnPerm_1037 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 5, 2, 3]
  invFun := ![1, 2, 4, 5, 0, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1037 : BottomDetBound targetTop_1037 9 := by
  have hU : rowTransform_1037.det.natAbs = 1 := by
    have hdet : rowTransform_1037.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_1037 hU
  have hcols := hrows.permuteColumns columnPerm_1037
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1037 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_1037 = targetTop_1037 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1037 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 3 7 7)) 9 := by
  have htop : targetTop_1037 =
      topOfPattern (R := ℤ) (angle6 1 2 2 3 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1037

/-- Explicit target top block for canonical pattern `(1, 2, 2, 4, 4, 4)`. -/
def targetTop_1038 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 0;
     0, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1038 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 0]

def columnPerm_1038 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1038 : BottomDetBound targetTop_1038 9 := by
  have hU : rowTransform_1038.det.natAbs = 1 := by
    have hdet : rowTransform_1038.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1038 hU
  have hcols := hrows.permuteColumns columnPerm_1038
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1038 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1038 = targetTop_1038 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1038 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 4 4 4)) 9 := by
  have htop : targetTop_1038 =
      topOfPattern (R := ℤ) (angle6 1 2 2 4 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1038

/-- Explicit target top block for canonical pattern `(1, 2, 2, 4, 4, 5)`. -/
def targetTop_1039 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 1;
     0, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1039 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 0]

def columnPerm_1039 : Equiv.Perm (Fin 6) where
  toFun := ![4, 2, 3, 0, 1, 5]
  invFun := ![3, 4, 1, 2, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1039 : BottomDetBound targetTop_1039 9 := by
  have hU : rowTransform_1039.det.natAbs = 1 := by
    have hdet : rowTransform_1039.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_1039 hU
  have hcols := hrows.permuteColumns columnPerm_1039
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1039 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_1039 = targetTop_1039 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1039 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 4 4 5)) 9 := by
  have htop : targetTop_1039 =
      topOfPattern (R := ℤ) (angle6 1 2 2 4 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1039

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard064
