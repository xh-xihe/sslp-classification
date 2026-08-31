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

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard057

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(1, 1, 2, 4, 4, 4)`. -/
def targetTop_0912 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0912 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_0912 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0912 : BottomDetBound targetTop_0912 9 := by
  have hU : rowTransform_0912.det.natAbs = 1 := by
    have hdet : rowTransform_0912.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0912 hU
  have hcols := hrows.permuteColumns columnPerm_0912
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0912 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0912 = targetTop_0912 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0912 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 4 4 4)) 9 := by
  have htop : targetTop_0912 =
      topOfPattern (R := ℤ) (angle6 1 1 2 4 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0912

/-- Explicit target top block for canonical pattern `(1, 1, 2, 4, 4, 5)`. -/
def targetTop_0913 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 1;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0913 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_0913 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0913 : BottomDetBound targetTop_0913 9 := by
  have hU : rowTransform_0913.det.natAbs = 1 := by
    have hdet : rowTransform_0913.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate.bottomBound.transformTopRows rowTransform_0913 hU
  have hcols := hrows.permuteColumns columnPerm_0913
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0913 MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Base.explicitTop)
          columnPerm_0913 = targetTop_0913 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0913 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 4 4 5)) 9 := by
  have htop : targetTop_0913 =
      topOfPattern (R := ℤ) (angle6 1 1 2 4 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0913

/-- Explicit target top block for canonical pattern `(1, 1, 2, 4, 4, 6)`. -/
def targetTop_0914 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0914 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_0914 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 4, 0, 1, 5]
  invFun := ![3, 4, 0, 1, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0914 : BottomDetBound targetTop_0914 9 := by
  have hU : rowTransform_0914.det.natAbs = 1 := by
    have hdet : rowTransform_0914.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_0914 hU
  have hcols := hrows.permuteColumns columnPerm_0914
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0914 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_0914 = targetTop_0914 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0914 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 4 4 6)) 9 := by
  have htop : targetTop_0914 =
      topOfPattern (R := ℤ) (angle6 1 1 2 4 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0914

/-- Explicit target top block for canonical pattern `(1, 1, 2, 4, 4, 7)`. -/
def targetTop_0915 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 1;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0915 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_0915 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0915 : BottomDetBound targetTop_0915 9 := by
  have hU : rowTransform_0915.det.natAbs = 1 := by
    have hdet : rowTransform_0915.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R039.Aggregate.bottomBound.transformTopRows rowTransform_0915 hU
  have hcols := hrows.permuteColumns columnPerm_0915
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0915 MainTheory.Generated.BinaryBetaSixKernel.Representative.R039.Base.explicitTop)
          columnPerm_0915 = targetTop_0915 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0915 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 4 4 7)) 9 := by
  have htop : targetTop_0915 =
      topOfPattern (R := ℤ) (angle6 1 1 2 4 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0915

/-- Explicit target top block for canonical pattern `(1, 1, 2, 4, 5, 5)`. -/
def targetTop_0916 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 1, 1;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0916 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_0916 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0916 : BottomDetBound targetTop_0916 9 := by
  have hU : rowTransform_0916.det.natAbs = 1 := by
    have hdet : rowTransform_0916.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_0916 hU
  have hcols := hrows.permuteColumns columnPerm_0916
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0916 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_0916 = targetTop_0916 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0916 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 4 5 5)) 9 := by
  have htop : targetTop_0916 =
      topOfPattern (R := ℤ) (angle6 1 1 2 4 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0916

/-- Explicit target top block for canonical pattern `(1, 1, 2, 4, 5, 6)`. -/
def targetTop_0917 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 1, 0;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0917 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_0917 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0917 : BottomDetBound targetTop_0917 9 := by
  have hU : rowTransform_0917.det.natAbs = 1 := by
    have hdet : rowTransform_0917.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Aggregate.bottomBound.transformTopRows rowTransform_0917 hU
  have hcols := hrows.permuteColumns columnPerm_0917
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0917 MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Base.explicitTop)
          columnPerm_0917 = targetTop_0917 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0917 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 4 5 6)) 9 := by
  have htop : targetTop_0917 =
      topOfPattern (R := ℤ) (angle6 1 1 2 4 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0917

/-- Explicit target top block for canonical pattern `(1, 1, 2, 4, 5, 7)`. -/
def targetTop_0918 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 1, 1;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0918 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_0918 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0918 : BottomDetBound targetTop_0918 9 := by
  have hU : rowTransform_0918.det.natAbs = 1 := by
    have hdet : rowTransform_0918.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R044.Aggregate.bottomBound.transformTopRows rowTransform_0918 hU
  have hcols := hrows.permuteColumns columnPerm_0918
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0918 MainTheory.Generated.BinaryBetaSixKernel.Representative.R044.Base.explicitTop)
          columnPerm_0918 = targetTop_0918 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0918 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 4 5 7)) 9 := by
  have htop : targetTop_0918 =
      topOfPattern (R := ℤ) (angle6 1 1 2 4 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0918

/-- Explicit target top block for canonical pattern `(1, 1, 2, 4, 6, 6)`. -/
def targetTop_0919 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 0;
     0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0919 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0919 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0919 : BottomDetBound targetTop_0919 9 := by
  have hU : rowTransform_0919.det.natAbs = 1 := by
    have hdet : rowTransform_0919.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate.bottomBound.transformTopRows rowTransform_0919 hU
  have hcols := hrows.permuteColumns columnPerm_0919
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0919 MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Base.explicitTop)
          columnPerm_0919 = targetTop_0919 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0919 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 4 6 6)) 9 := by
  have htop : targetTop_0919 =
      topOfPattern (R := ℤ) (angle6 1 1 2 4 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0919

/-- Explicit target top block for canonical pattern `(1, 1, 2, 4, 6, 7)`. -/
def targetTop_0920 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 1;
     0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0920 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0920 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0920 : BottomDetBound targetTop_0920 9 := by
  have hU : rowTransform_0920.det.natAbs = 1 := by
    have hdet : rowTransform_0920.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R047.Aggregate.bottomBound.transformTopRows rowTransform_0920 hU
  have hcols := hrows.permuteColumns columnPerm_0920
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0920 MainTheory.Generated.BinaryBetaSixKernel.Representative.R047.Base.explicitTop)
          columnPerm_0920 = targetTop_0920 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0920 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 4 6 7)) 9 := by
  have htop : targetTop_0920 =
      topOfPattern (R := ℤ) (angle6 1 1 2 4 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0920

/-- Explicit target top block for canonical pattern `(1, 1, 2, 4, 7, 7)`. -/
def targetTop_0921 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 1, 1;
     0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0921 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0921 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0921 : BottomDetBound targetTop_0921 9 := by
  have hU : rowTransform_0921.det.natAbs = 1 := by
    have hdet : rowTransform_0921.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R048.Aggregate.bottomBound.transformTopRows rowTransform_0921 hU
  have hcols := hrows.permuteColumns columnPerm_0921
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0921 MainTheory.Generated.BinaryBetaSixKernel.Representative.R048.Base.explicitTop)
          columnPerm_0921 = targetTop_0921 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0921 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 4 7 7)) 9 := by
  have htop : targetTop_0921 =
      topOfPattern (R := ℤ) (angle6 1 1 2 4 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0921

/-- Explicit target top block for canonical pattern `(1, 1, 2, 5, 5, 5)`. -/
def targetTop_0922 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 1, 1;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0922 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_0922 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0922 : BottomDetBound targetTop_0922 9 := by
  have hU : rowTransform_0922.det.natAbs = 1 := by
    have hdet : rowTransform_0922.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0922 hU
  have hcols := hrows.permuteColumns columnPerm_0922
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0922 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0922 = targetTop_0922 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0922 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 5 5 5)) 9 := by
  have htop : targetTop_0922 =
      topOfPattern (R := ℤ) (angle6 1 1 2 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0922

/-- Explicit target top block for canonical pattern `(1, 1, 2, 5, 5, 6)`. -/
def targetTop_0923 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 1, 0;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0923 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, (-1);
     0, 0, 1;
     0, 1, 0]

def columnPerm_0923 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0923 : BottomDetBound targetTop_0923 9 := by
  have hU : rowTransform_0923.det.natAbs = 1 := by
    have hdet : rowTransform_0923.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate.bottomBound.transformTopRows rowTransform_0923 hU
  have hcols := hrows.permuteColumns columnPerm_0923
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0923 MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Base.explicitTop)
          columnPerm_0923 = targetTop_0923 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0923 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 5 5 6)) 9 := by
  have htop : targetTop_0923 =
      topOfPattern (R := ℤ) (angle6 1 1 2 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0923

/-- Explicit target top block for canonical pattern `(1, 1, 2, 5, 5, 7)`. -/
def targetTop_0924 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 1, 1;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0924 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_0924 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 4, 0, 1, 5]
  invFun := ![3, 4, 0, 1, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0924 : BottomDetBound targetTop_0924 9 := by
  have hU : rowTransform_0924.det.natAbs = 1 := by
    have hdet : rowTransform_0924.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_0924 hU
  have hcols := hrows.permuteColumns columnPerm_0924
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0924 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_0924 = targetTop_0924 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0924 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 5 5 7)) 9 := by
  have htop : targetTop_0924 =
      topOfPattern (R := ℤ) (angle6 1 1 2 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0924

/-- Explicit target top block for canonical pattern `(1, 1, 2, 5, 6, 6)`. -/
def targetTop_0925 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 0, 0;
     0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0925 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0925 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0925 : BottomDetBound targetTop_0925 9 := by
  have hU : rowTransform_0925.det.natAbs = 1 := by
    have hdet : rowTransform_0925.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R049.Aggregate.bottomBound.transformTopRows rowTransform_0925 hU
  have hcols := hrows.permuteColumns columnPerm_0925
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0925 MainTheory.Generated.BinaryBetaSixKernel.Representative.R049.Base.explicitTop)
          columnPerm_0925 = targetTop_0925 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0925 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 5 6 6)) 9 := by
  have htop : targetTop_0925 =
      topOfPattern (R := ℤ) (angle6 1 1 2 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0925

/-- Explicit target top block for canonical pattern `(1, 1, 2, 5, 6, 7)`. -/
def targetTop_0926 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 0, 1;
     0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0926 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0926 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0926 : BottomDetBound targetTop_0926 9 := by
  have hU : rowTransform_0926.det.natAbs = 1 := by
    have hdet : rowTransform_0926.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R050.Aggregate.bottomBound.transformTopRows rowTransform_0926 hU
  have hcols := hrows.permuteColumns columnPerm_0926
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0926 MainTheory.Generated.BinaryBetaSixKernel.Representative.R050.Base.explicitTop)
          columnPerm_0926 = targetTop_0926 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0926 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 5 6 7)) 9 := by
  have htop : targetTop_0926 =
      topOfPattern (R := ℤ) (angle6 1 1 2 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0926

/-- Explicit target top block for canonical pattern `(1, 1, 2, 5, 7, 7)`. -/
def targetTop_0927 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 1, 1;
     0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0927 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0927 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0927 : BottomDetBound targetTop_0927 9 := by
  have hU : rowTransform_0927.det.natAbs = 1 := by
    have hdet : rowTransform_0927.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate.bottomBound.transformTopRows rowTransform_0927 hU
  have hcols := hrows.permuteColumns columnPerm_0927
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0927 MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Base.explicitTop)
          columnPerm_0927 = targetTop_0927 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0927 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 5 7 7)) 9 := by
  have htop : targetTop_0927 =
      topOfPattern (R := ℤ) (angle6 1 1 2 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0927

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard057
