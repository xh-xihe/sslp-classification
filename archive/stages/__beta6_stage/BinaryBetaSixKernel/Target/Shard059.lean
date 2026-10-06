-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R045.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R049.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R050.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R051.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard059

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(1, 1, 3, 3, 6, 6)`. -/
def targetTop_0944 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 0;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0944 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0944 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0944 : BottomDetBound targetTop_0944 9 := by
  have hU : rowTransform_0944.det.natAbs = 1 := by
    have hdet : rowTransform_0944.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate.bottomBound.transformTopRows rowTransform_0944 hU
  have hcols := hrows.permuteColumns columnPerm_0944
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0944 MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Base.explicitTop)
          columnPerm_0944 = targetTop_0944 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0944 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 3 6 6)) 9 := by
  have htop : targetTop_0944 =
      topOfPattern (R := ℤ) (angle6 1 1 3 3 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0944

/-- Explicit target top block for canonical pattern `(1, 1, 3, 3, 6, 7)`. -/
def targetTop_0945 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0945 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0945 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0945 : BottomDetBound targetTop_0945 9 := by
  have hU : rowTransform_0945.det.natAbs = 1 := by
    have hdet : rowTransform_0945.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_0945 hU
  have hcols := hrows.permuteColumns columnPerm_0945
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0945 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_0945 = targetTop_0945 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0945 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 3 6 7)) 9 := by
  have htop : targetTop_0945 =
      topOfPattern (R := ℤ) (angle6 1 1 3 3 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0945

/-- Explicit target top block for canonical pattern `(1, 1, 3, 3, 7, 7)`. -/
def targetTop_0946 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0946 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0946 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0946 : BottomDetBound targetTop_0946 9 := by
  have hU : rowTransform_0946.det.natAbs = 1 := by
    have hdet : rowTransform_0946.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate.bottomBound.transformTopRows rowTransform_0946 hU
  have hcols := hrows.permuteColumns columnPerm_0946
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0946 MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Base.explicitTop)
          columnPerm_0946 = targetTop_0946 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0946 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 3 7 7)) 9 := by
  have htop : targetTop_0946 =
      topOfPattern (R := ℤ) (angle6 1 1 3 3 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0946

/-- Explicit target top block for canonical pattern `(1, 1, 3, 4, 4, 4)`. -/
def targetTop_0947 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0947 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 0, 1;
     1, 0, 0]

def columnPerm_0947 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0947 : BottomDetBound targetTop_0947 9 := by
  have hU : rowTransform_0947.det.natAbs = 1 := by
    have hdet : rowTransform_0947.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0947 hU
  have hcols := hrows.permuteColumns columnPerm_0947
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0947 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0947 = targetTop_0947 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0947 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 4 4 4)) 9 := by
  have htop : targetTop_0947 =
      topOfPattern (R := ℤ) (angle6 1 1 3 4 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0947

/-- Explicit target top block for canonical pattern `(1, 1, 3, 4, 4, 5)`. -/
def targetTop_0948 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 1;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0948 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 0, 1;
     0, 1, 0]

def columnPerm_0948 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0948 : BottomDetBound targetTop_0948 9 := by
  have hU : rowTransform_0948.det.natAbs = 1 := by
    have hdet : rowTransform_0948.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate.bottomBound.transformTopRows rowTransform_0948 hU
  have hcols := hrows.permuteColumns columnPerm_0948
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0948 MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Base.explicitTop)
          columnPerm_0948 = targetTop_0948 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0948 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 4 4 5)) 9 := by
  have htop : targetTop_0948 =
      topOfPattern (R := ℤ) (angle6 1 1 3 4 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0948

/-- Explicit target top block for canonical pattern `(1, 1, 3, 4, 4, 6)`. -/
def targetTop_0949 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 0;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0949 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_0949 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0949 : BottomDetBound targetTop_0949 9 := by
  have hU : rowTransform_0949.det.natAbs = 1 := by
    have hdet : rowTransform_0949.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate.bottomBound.transformTopRows rowTransform_0949 hU
  have hcols := hrows.permuteColumns columnPerm_0949
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0949 MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Base.explicitTop)
          columnPerm_0949 = targetTop_0949 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0949 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 4 4 6)) 9 := by
  have htop : targetTop_0949 =
      topOfPattern (R := ℤ) (angle6 1 1 3 4 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0949

/-- Explicit target top block for canonical pattern `(1, 1, 3, 4, 4, 7)`. -/
def targetTop_0950 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 1;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0950 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 0, 1;
     1, 0, 0]

def columnPerm_0950 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 4, 0, 1, 5]
  invFun := ![3, 4, 0, 1, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0950 : BottomDetBound targetTop_0950 9 := by
  have hU : rowTransform_0950.det.natAbs = 1 := by
    have hdet : rowTransform_0950.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_0950 hU
  have hcols := hrows.permuteColumns columnPerm_0950
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0950 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_0950 = targetTop_0950 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0950 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 4 4 7)) 9 := by
  have htop : targetTop_0950 =
      topOfPattern (R := ℤ) (angle6 1 1 3 4 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0950

/-- Explicit target top block for canonical pattern `(1, 1, 3, 4, 5, 5)`. -/
def targetTop_0951 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 1, 1;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0951 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 0, 1;
     0, 1, 0]

def columnPerm_0951 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0951 : BottomDetBound targetTop_0951 9 := by
  have hU : rowTransform_0951.det.natAbs = 1 := by
    have hdet : rowTransform_0951.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_0951 hU
  have hcols := hrows.permuteColumns columnPerm_0951
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0951 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_0951 = targetTop_0951 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0951 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 4 5 5)) 9 := by
  have htop : targetTop_0951 =
      topOfPattern (R := ℤ) (angle6 1 1 3 4 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0951

/-- Explicit target top block for canonical pattern `(1, 1, 3, 4, 5, 6)`. -/
def targetTop_0952 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 1, 0;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0952 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_0952 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0952 : BottomDetBound targetTop_0952 9 := by
  have hU : rowTransform_0952.det.natAbs = 1 := by
    have hdet : rowTransform_0952.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R045.Aggregate.bottomBound.transformTopRows rowTransform_0952 hU
  have hcols := hrows.permuteColumns columnPerm_0952
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0952 MainTheory.Generated.BinaryBetaSixKernel.Representative.R045.Base.explicitTop)
          columnPerm_0952 = targetTop_0952 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0952 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 4 5 6)) 9 := by
  have htop : targetTop_0952 =
      topOfPattern (R := ℤ) (angle6 1 1 3 4 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0952

/-- Explicit target top block for canonical pattern `(1, 1, 3, 4, 5, 7)`. -/
def targetTop_0953 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 1, 1;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0953 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 0, 1;
     0, 1, 0]

def columnPerm_0953 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0953 : BottomDetBound targetTop_0953 9 := by
  have hU : rowTransform_0953.det.natAbs = 1 := by
    have hdet : rowTransform_0953.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Aggregate.bottomBound.transformTopRows rowTransform_0953 hU
  have hcols := hrows.permuteColumns columnPerm_0953
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0953 MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Base.explicitTop)
          columnPerm_0953 = targetTop_0953 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0953 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 4 5 7)) 9 := by
  have htop : targetTop_0953 =
      topOfPattern (R := ℤ) (angle6 1 1 3 4 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0953

/-- Explicit target top block for canonical pattern `(1, 1, 3, 4, 6, 6)`. -/
def targetTop_0954 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 0;
     0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0954 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, (-1);
     0, 1, 0;
     0, 0, 1]

def columnPerm_0954 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0954 : BottomDetBound targetTop_0954 9 := by
  have hU : rowTransform_0954.det.natAbs = 1 := by
    have hdet : rowTransform_0954.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R049.Aggregate.bottomBound.transformTopRows rowTransform_0954 hU
  have hcols := hrows.permuteColumns columnPerm_0954
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0954 MainTheory.Generated.BinaryBetaSixKernel.Representative.R049.Base.explicitTop)
          columnPerm_0954 = targetTop_0954 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0954 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 4 6 6)) 9 := by
  have htop : targetTop_0954 =
      topOfPattern (R := ℤ) (angle6 1 1 3 4 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0954

/-- Explicit target top block for canonical pattern `(1, 1, 3, 4, 6, 7)`. -/
def targetTop_0955 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 1;
     0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0955 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, (-1);
     0, 1, 0;
     0, 0, 1]

def columnPerm_0955 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0955 : BottomDetBound targetTop_0955 9 := by
  have hU : rowTransform_0955.det.natAbs = 1 := by
    have hdet : rowTransform_0955.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R050.Aggregate.bottomBound.transformTopRows rowTransform_0955 hU
  have hcols := hrows.permuteColumns columnPerm_0955
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0955 MainTheory.Generated.BinaryBetaSixKernel.Representative.R050.Base.explicitTop)
          columnPerm_0955 = targetTop_0955 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0955 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 4 6 7)) 9 := by
  have htop : targetTop_0955 =
      topOfPattern (R := ℤ) (angle6 1 1 3 4 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0955

/-- Explicit target top block for canonical pattern `(1, 1, 3, 4, 7, 7)`. -/
def targetTop_0956 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 1, 1;
     0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0956 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0956 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0956 : BottomDetBound targetTop_0956 9 := by
  have hU : rowTransform_0956.det.natAbs = 1 := by
    have hdet : rowTransform_0956.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate.bottomBound.transformTopRows rowTransform_0956 hU
  have hcols := hrows.permuteColumns columnPerm_0956
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0956 MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Base.explicitTop)
          columnPerm_0956 = targetTop_0956 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0956 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 4 7 7)) 9 := by
  have htop : targetTop_0956 =
      topOfPattern (R := ℤ) (angle6 1 1 3 4 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0956

/-- Explicit target top block for canonical pattern `(1, 1, 3, 5, 5, 5)`. -/
def targetTop_0957 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0957 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 0, 1;
     1, 0, 0]

def columnPerm_0957 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0957 : BottomDetBound targetTop_0957 9 := by
  have hU : rowTransform_0957.det.natAbs = 1 := by
    have hdet : rowTransform_0957.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0957 hU
  have hcols := hrows.permuteColumns columnPerm_0957
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0957 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0957 = targetTop_0957 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0957 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 5 5 5)) 9 := by
  have htop : targetTop_0957 =
      topOfPattern (R := ℤ) (angle6 1 1 3 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0957

/-- Explicit target top block for canonical pattern `(1, 1, 3, 5, 5, 6)`. -/
def targetTop_0958 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 0;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0958 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_0958 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0958 : BottomDetBound targetTop_0958 9 := by
  have hU : rowTransform_0958.det.natAbs = 1 := by
    have hdet : rowTransform_0958.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R051.Aggregate.bottomBound.transformTopRows rowTransform_0958 hU
  have hcols := hrows.permuteColumns columnPerm_0958
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0958 MainTheory.Generated.BinaryBetaSixKernel.Representative.R051.Base.explicitTop)
          columnPerm_0958 = targetTop_0958 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0958 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 5 5 6)) 9 := by
  have htop : targetTop_0958 =
      topOfPattern (R := ℤ) (angle6 1 1 3 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0958

/-- Explicit target top block for canonical pattern `(1, 1, 3, 5, 5, 7)`. -/
def targetTop_0959 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0959 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_0959 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0959 : BottomDetBound targetTop_0959 9 := by
  have hU : rowTransform_0959.det.natAbs = 1 := by
    have hdet : rowTransform_0959.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate.bottomBound.transformTopRows rowTransform_0959 hU
  have hcols := hrows.permuteColumns columnPerm_0959
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0959 MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Base.explicitTop)
          columnPerm_0959 = targetTop_0959 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0959 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 5 5 7)) 9 := by
  have htop : targetTop_0959 =
      topOfPattern (R := ℤ) (angle6 1 1 3 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0959

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard059
