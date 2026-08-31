-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R042.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R044.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R045.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard056

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(1, 1, 2, 2, 7, 7)`. -/
def targetTop_0896 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0896 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0896 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0896 : BottomDetBound targetTop_0896 9 := by
  have hU : rowTransform_0896.det.natAbs = 1 := by
    have hdet : rowTransform_0896.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate.bottomBound.transformTopRows rowTransform_0896 hU
  have hcols := hrows.permuteColumns columnPerm_0896
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0896 MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Base.explicitTop)
          columnPerm_0896 = targetTop_0896 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0896 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 2 7 7)) 9 := by
  have htop : targetTop_0896 =
      topOfPattern (R := ℤ) (angle6 1 1 2 2 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0896

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 2, 3, 3, 3)`. -/
def targetTop_0897 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0897 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0897 :
    TopRowRelation targetTop_0897 relationCoefficients_0897 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0897, relationCoefficients_0897, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0897 : BottomDetBound targetTop_0897 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0897

theorem canonicalBound_0897 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 3 3 3)) 9 := by
  have htop : targetTop_0897 =
      topOfPattern (R := ℤ) (angle6 1 1 2 3 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0897

/-- Explicit target top block for canonical pattern `(1, 1, 2, 3, 3, 4)`. -/
def targetTop_0898 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 1, 0;
     0, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0898 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0898 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0898 : BottomDetBound targetTop_0898 9 := by
  have hU : rowTransform_0898.det.natAbs = 1 := by
    have hdet : rowTransform_0898.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_0898 hU
  have hcols := hrows.permuteColumns columnPerm_0898
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0898 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_0898 = targetTop_0898 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0898 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 3 3 4)) 9 := by
  have htop : targetTop_0898 =
      topOfPattern (R := ℤ) (angle6 1 1 2 3 3 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0898

/-- Explicit target top block for canonical pattern `(1, 1, 2, 3, 3, 5)`. -/
def targetTop_0899 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0899 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0899 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0899 : BottomDetBound targetTop_0899 9 := by
  have hU : rowTransform_0899.det.natAbs = 1 := by
    have hdet : rowTransform_0899.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_0899 hU
  have hcols := hrows.permuteColumns columnPerm_0899
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0899 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_0899 = targetTop_0899 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0899 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 3 3 5)) 9 := by
  have htop : targetTop_0899 =
      topOfPattern (R := ℤ) (angle6 1 1 2 3 3 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0899

/-- Explicit target top block for canonical pattern `(1, 1, 2, 3, 3, 6)`. -/
def targetTop_0900 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 1, 0;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0900 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0900 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0900 : BottomDetBound targetTop_0900 9 := by
  have hU : rowTransform_0900.det.natAbs = 1 := by
    have hdet : rowTransform_0900.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_0900 hU
  have hcols := hrows.permuteColumns columnPerm_0900
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0900 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_0900 = targetTop_0900 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0900 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 3 3 6)) 9 := by
  have htop : targetTop_0900 =
      topOfPattern (R := ℤ) (angle6 1 1 2 3 3 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0900

/-- Explicit target top block for canonical pattern `(1, 1, 2, 3, 3, 7)`. -/
def targetTop_0901 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0901 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0901 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0901 : BottomDetBound targetTop_0901 9 := by
  have hU : rowTransform_0901.det.natAbs = 1 := by
    have hdet : rowTransform_0901.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_0901 hU
  have hcols := hrows.permuteColumns columnPerm_0901
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0901 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_0901 = targetTop_0901 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0901 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 3 3 7)) 9 := by
  have htop : targetTop_0901 =
      topOfPattern (R := ℤ) (angle6 1 1 2 3 3 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0901

/-- Explicit target top block for canonical pattern `(1, 1, 2, 3, 4, 4)`. -/
def targetTop_0902 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 0, 0;
     0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0902 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_0902 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0902 : BottomDetBound targetTop_0902 9 := by
  have hU : rowTransform_0902.det.natAbs = 1 := by
    have hdet : rowTransform_0902.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_0902 hU
  have hcols := hrows.permuteColumns columnPerm_0902
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0902 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_0902 = targetTop_0902 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0902 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 3 4 4)) 9 := by
  have htop : targetTop_0902 =
      topOfPattern (R := ℤ) (angle6 1 1 2 3 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0902

/-- Explicit target top block for canonical pattern `(1, 1, 2, 3, 4, 5)`. -/
def targetTop_0903 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 0, 1;
     0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0903 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0903 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0903 : BottomDetBound targetTop_0903 9 := by
  have hU : rowTransform_0903.det.natAbs = 1 := by
    have hdet : rowTransform_0903.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R042.Aggregate.bottomBound.transformTopRows rowTransform_0903 hU
  have hcols := hrows.permuteColumns columnPerm_0903
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0903 MainTheory.Generated.BinaryBetaSixKernel.Representative.R042.Base.explicitTop)
          columnPerm_0903 = targetTop_0903 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0903 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 3 4 5)) 9 := by
  have htop : targetTop_0903 =
      topOfPattern (R := ℤ) (angle6 1 1 2 3 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0903

/-- Explicit target top block for canonical pattern `(1, 1, 2, 3, 4, 6)`. -/
def targetTop_0904 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 0, 0;
     0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0904 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0904 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0904 : BottomDetBound targetTop_0904 9 := by
  have hU : rowTransform_0904.det.natAbs = 1 := by
    have hdet : rowTransform_0904.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Aggregate.bottomBound.transformTopRows rowTransform_0904 hU
  have hcols := hrows.permuteColumns columnPerm_0904
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0904 MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Base.explicitTop)
          columnPerm_0904 = targetTop_0904 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0904 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 3 4 6)) 9 := by
  have htop : targetTop_0904 =
      topOfPattern (R := ℤ) (angle6 1 1 2 3 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0904

/-- Explicit target top block for canonical pattern `(1, 1, 2, 3, 4, 7)`. -/
def targetTop_0905 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 0, 1;
     0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0905 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0905 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0905 : BottomDetBound targetTop_0905 9 := by
  have hU : rowTransform_0905.det.natAbs = 1 := by
    have hdet : rowTransform_0905.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R044.Aggregate.bottomBound.transformTopRows rowTransform_0905 hU
  have hcols := hrows.permuteColumns columnPerm_0905
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0905 MainTheory.Generated.BinaryBetaSixKernel.Representative.R044.Base.explicitTop)
          columnPerm_0905 = targetTop_0905 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0905 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 3 4 7)) 9 := by
  have htop : targetTop_0905 =
      topOfPattern (R := ℤ) (angle6 1 1 2 3 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0905

/-- Explicit target top block for canonical pattern `(1, 1, 2, 3, 5, 5)`. -/
def targetTop_0906 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0906 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_0906 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0906 : BottomDetBound targetTop_0906 9 := by
  have hU : rowTransform_0906.det.natAbs = 1 := by
    have hdet : rowTransform_0906.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_0906 hU
  have hcols := hrows.permuteColumns columnPerm_0906
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0906 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_0906 = targetTop_0906 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0906 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 3 5 5)) 9 := by
  have htop : targetTop_0906 =
      topOfPattern (R := ℤ) (angle6 1 1 2 3 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0906

/-- Explicit target top block for canonical pattern `(1, 1, 2, 3, 5, 6)`. -/
def targetTop_0907 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 1, 0;
     0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0907 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0907 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0907 : BottomDetBound targetTop_0907 9 := by
  have hU : rowTransform_0907.det.natAbs = 1 := by
    have hdet : rowTransform_0907.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R045.Aggregate.bottomBound.transformTopRows rowTransform_0907 hU
  have hcols := hrows.permuteColumns columnPerm_0907
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0907 MainTheory.Generated.BinaryBetaSixKernel.Representative.R045.Base.explicitTop)
          columnPerm_0907 = targetTop_0907 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0907 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 3 5 6)) 9 := by
  have htop : targetTop_0907 =
      topOfPattern (R := ℤ) (angle6 1 1 2 3 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0907

/-- Explicit target top block for canonical pattern `(1, 1, 2, 3, 5, 7)`. -/
def targetTop_0908 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0908 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0908 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0908 : BottomDetBound targetTop_0908 9 := by
  have hU : rowTransform_0908.det.natAbs = 1 := by
    have hdet : rowTransform_0908.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Aggregate.bottomBound.transformTopRows rowTransform_0908 hU
  have hcols := hrows.permuteColumns columnPerm_0908
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0908 MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Base.explicitTop)
          columnPerm_0908 = targetTop_0908 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0908 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 3 5 7)) 9 := by
  have htop : targetTop_0908 =
      topOfPattern (R := ℤ) (angle6 1 1 2 3 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0908

/-- Explicit target top block for canonical pattern `(1, 1, 2, 3, 6, 6)`. -/
def targetTop_0909 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 0, 0;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0909 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     0, 1, 0]

def columnPerm_0909 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0909 : BottomDetBound targetTop_0909 9 := by
  have hU : rowTransform_0909.det.natAbs = 1 := by
    have hdet : rowTransform_0909.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_0909 hU
  have hcols := hrows.permuteColumns columnPerm_0909
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0909 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_0909 = targetTop_0909 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0909 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 3 6 6)) 9 := by
  have htop : targetTop_0909 =
      topOfPattern (R := ℤ) (angle6 1 1 2 3 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0909

/-- Explicit target top block for canonical pattern `(1, 1, 2, 3, 6, 7)`. -/
def targetTop_0910 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 0, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0910 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0910 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0910 : BottomDetBound targetTop_0910 9 := by
  have hU : rowTransform_0910.det.natAbs = 1 := by
    have hdet : rowTransform_0910.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R042.Aggregate.bottomBound.transformTopRows rowTransform_0910 hU
  have hcols := hrows.permuteColumns columnPerm_0910
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0910 MainTheory.Generated.BinaryBetaSixKernel.Representative.R042.Base.explicitTop)
          columnPerm_0910 = targetTop_0910 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0910 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 3 6 7)) 9 := by
  have htop : targetTop_0910 =
      topOfPattern (R := ℤ) (angle6 1 1 2 3 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0910

/-- Explicit target top block for canonical pattern `(1, 1, 2, 3, 7, 7)`. -/
def targetTop_0911 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0911 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 1;
     0, 1, 0]

def columnPerm_0911 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0911 : BottomDetBound targetTop_0911 9 := by
  have hU : rowTransform_0911.det.natAbs = 1 := by
    have hdet : rowTransform_0911.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_0911 hU
  have hcols := hrows.permuteColumns columnPerm_0911
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0911 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_0911 = targetTop_0911 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0911 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 3 7 7)) 9 := by
  have htop : targetTop_0911 =
      topOfPattern (R := ℤ) (angle6 1 1 2 3 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0911

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard056
