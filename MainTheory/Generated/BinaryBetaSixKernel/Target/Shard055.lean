-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R039.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard055

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(1, 1, 2, 2, 2, 6)`. -/
def targetTop_0880 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0880 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 1;
     0, 0, 1]

def columnPerm_0880 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0880 : BottomDetBound targetTop_0880 9 := by
  have hU : rowTransform_0880.det.natAbs = 1 := by
    have hdet : rowTransform_0880.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0880 hU
  have hcols := hrows.permuteColumns columnPerm_0880
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0880 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0880 = targetTop_0880 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0880 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 2 2 6)) 9 := by
  have htop : targetTop_0880 =
      topOfPattern (R := ℤ) (angle6 1 1 2 2 2 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0880

/-- Explicit target top block for canonical pattern `(1, 1, 2, 2, 2, 7)`. -/
def targetTop_0881 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0881 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 1;
     0, 0, 1]

def columnPerm_0881 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0881 : BottomDetBound targetTop_0881 9 := by
  have hU : rowTransform_0881.det.natAbs = 1 := by
    have hdet : rowTransform_0881.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0881 hU
  have hcols := hrows.permuteColumns columnPerm_0881
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0881 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0881 = targetTop_0881 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0881 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 2 2 7)) 9 := by
  have htop : targetTop_0881 =
      topOfPattern (R := ℤ) (angle6 1 1 2 2 2 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0881

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 2, 2, 3, 3)`. -/
def targetTop_0882 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0882 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0882 :
    TopRowRelation targetTop_0882 relationCoefficients_0882 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0882, relationCoefficients_0882, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0882 : BottomDetBound targetTop_0882 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0882

theorem canonicalBound_0882 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 2 3 3)) 9 := by
  have htop : targetTop_0882 =
      topOfPattern (R := ℤ) (angle6 1 1 2 2 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0882

/-- Explicit target top block for canonical pattern `(1, 1, 2, 2, 3, 4)`. -/
def targetTop_0883 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 1, 0;
     0, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0883 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0883 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0883 : BottomDetBound targetTop_0883 9 := by
  have hU : rowTransform_0883.det.natAbs = 1 := by
    have hdet : rowTransform_0883.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate.bottomBound.transformTopRows rowTransform_0883 hU
  have hcols := hrows.permuteColumns columnPerm_0883
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0883 MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Base.explicitTop)
          columnPerm_0883 = targetTop_0883 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0883 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 2 3 4)) 9 := by
  have htop : targetTop_0883 =
      topOfPattern (R := ℤ) (angle6 1 1 2 2 3 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0883

/-- Explicit target top block for canonical pattern `(1, 1, 2, 2, 3, 5)`. -/
def targetTop_0884 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0884 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0884 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0884 : BottomDetBound targetTop_0884 9 := by
  have hU : rowTransform_0884.det.natAbs = 1 := by
    have hdet : rowTransform_0884.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate.bottomBound.transformTopRows rowTransform_0884 hU
  have hcols := hrows.permuteColumns columnPerm_0884
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0884 MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Base.explicitTop)
          columnPerm_0884 = targetTop_0884 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0884 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 2 3 5)) 9 := by
  have htop : targetTop_0884 =
      topOfPattern (R := ℤ) (angle6 1 1 2 2 3 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0884

/-- Explicit target top block for canonical pattern `(1, 1, 2, 2, 3, 6)`. -/
def targetTop_0885 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 1, 0;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0885 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0885 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0885 : BottomDetBound targetTop_0885 9 := by
  have hU : rowTransform_0885.det.natAbs = 1 := by
    have hdet : rowTransform_0885.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate.bottomBound.transformTopRows rowTransform_0885 hU
  have hcols := hrows.permuteColumns columnPerm_0885
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0885 MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Base.explicitTop)
          columnPerm_0885 = targetTop_0885 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0885 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 2 3 6)) 9 := by
  have htop : targetTop_0885 =
      topOfPattern (R := ℤ) (angle6 1 1 2 2 3 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0885

/-- Explicit target top block for canonical pattern `(1, 1, 2, 2, 3, 7)`. -/
def targetTop_0886 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0886 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0886 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0886 : BottomDetBound targetTop_0886 9 := by
  have hU : rowTransform_0886.det.natAbs = 1 := by
    have hdet : rowTransform_0886.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate.bottomBound.transformTopRows rowTransform_0886 hU
  have hcols := hrows.permuteColumns columnPerm_0886
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0886 MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Base.explicitTop)
          columnPerm_0886 = targetTop_0886 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0886 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 2 3 7)) 9 := by
  have htop : targetTop_0886 =
      topOfPattern (R := ℤ) (angle6 1 1 2 2 3 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0886

/-- Explicit target top block for canonical pattern `(1, 1, 2, 2, 4, 4)`. -/
def targetTop_0887 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0887 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0887 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0887 : BottomDetBound targetTop_0887 9 := by
  have hU : rowTransform_0887.det.natAbs = 1 := by
    have hdet : rowTransform_0887.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate.bottomBound.transformTopRows rowTransform_0887 hU
  have hcols := hrows.permuteColumns columnPerm_0887
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0887 MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Base.explicitTop)
          columnPerm_0887 = targetTop_0887 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0887 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 2 4 4)) 9 := by
  have htop : targetTop_0887 =
      topOfPattern (R := ℤ) (angle6 1 1 2 2 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0887

/-- Explicit target top block for canonical pattern `(1, 1, 2, 2, 4, 5)`. -/
def targetTop_0888 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0888 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0888 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0888 : BottomDetBound targetTop_0888 9 := by
  have hU : rowTransform_0888.det.natAbs = 1 := by
    have hdet : rowTransform_0888.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_0888 hU
  have hcols := hrows.permuteColumns columnPerm_0888
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0888 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_0888 = targetTop_0888 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0888 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 2 4 5)) 9 := by
  have htop : targetTop_0888 =
      topOfPattern (R := ℤ) (angle6 1 1 2 2 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0888

/-- Explicit target top block for canonical pattern `(1, 1, 2, 2, 4, 6)`. -/
def targetTop_0889 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0889 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_0889 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 0, 1, 4, 5]
  invFun := ![2, 3, 0, 1, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0889 : BottomDetBound targetTop_0889 9 := by
  have hU : rowTransform_0889.det.natAbs = 1 := by
    have hdet : rowTransform_0889.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_0889 hU
  have hcols := hrows.permuteColumns columnPerm_0889
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0889 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_0889 = targetTop_0889 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0889 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 2 4 6)) 9 := by
  have htop : targetTop_0889 =
      topOfPattern (R := ℤ) (angle6 1 1 2 2 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0889

/-- Explicit target top block for canonical pattern `(1, 1, 2, 2, 4, 7)`. -/
def targetTop_0890 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0890 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0890 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0890 : BottomDetBound targetTop_0890 9 := by
  have hU : rowTransform_0890.det.natAbs = 1 := by
    have hdet : rowTransform_0890.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R039.Aggregate.bottomBound.transformTopRows rowTransform_0890 hU
  have hcols := hrows.permuteColumns columnPerm_0890
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0890 MainTheory.Generated.BinaryBetaSixKernel.Representative.R039.Base.explicitTop)
          columnPerm_0890 = targetTop_0890 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0890 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 2 4 7)) 9 := by
  have htop : targetTop_0890 =
      topOfPattern (R := ℤ) (angle6 1 1 2 2 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0890

/-- Explicit target top block for canonical pattern `(1, 1, 2, 2, 5, 5)`. -/
def targetTop_0891 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0891 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0891 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0891 : BottomDetBound targetTop_0891 9 := by
  have hU : rowTransform_0891.det.natAbs = 1 := by
    have hdet : rowTransform_0891.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate.bottomBound.transformTopRows rowTransform_0891 hU
  have hcols := hrows.permuteColumns columnPerm_0891
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0891 MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Base.explicitTop)
          columnPerm_0891 = targetTop_0891 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0891 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 2 5 5)) 9 := by
  have htop : targetTop_0891 =
      topOfPattern (R := ℤ) (angle6 1 1 2 2 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0891

/-- Explicit target top block for canonical pattern `(1, 1, 2, 2, 5, 6)`. -/
def targetTop_0892 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 1, 0;
     0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0892 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0892 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0892 : BottomDetBound targetTop_0892 9 := by
  have hU : rowTransform_0892.det.natAbs = 1 := by
    have hdet : rowTransform_0892.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate.bottomBound.transformTopRows rowTransform_0892 hU
  have hcols := hrows.permuteColumns columnPerm_0892
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0892 MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Base.explicitTop)
          columnPerm_0892 = targetTop_0892 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0892 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 2 5 6)) 9 := by
  have htop : targetTop_0892 =
      topOfPattern (R := ℤ) (angle6 1 1 2 2 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0892

/-- Explicit target top block for canonical pattern `(1, 1, 2, 2, 5, 7)`. -/
def targetTop_0893 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0893 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 0;
     0, 0, 1]

def columnPerm_0893 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 0, 1, 4, 5]
  invFun := ![2, 3, 0, 1, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0893 : BottomDetBound targetTop_0893 9 := by
  have hU : rowTransform_0893.det.natAbs = 1 := by
    have hdet : rowTransform_0893.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_0893 hU
  have hcols := hrows.permuteColumns columnPerm_0893
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0893 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_0893 = targetTop_0893 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0893 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 2 5 7)) 9 := by
  have htop : targetTop_0893 =
      topOfPattern (R := ℤ) (angle6 1 1 2 2 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0893

/-- Explicit target top block for canonical pattern `(1, 1, 2, 2, 6, 6)`. -/
def targetTop_0894 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0894 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0894 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0894 : BottomDetBound targetTop_0894 9 := by
  have hU : rowTransform_0894.det.natAbs = 1 := by
    have hdet : rowTransform_0894.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate.bottomBound.transformTopRows rowTransform_0894 hU
  have hcols := hrows.permuteColumns columnPerm_0894
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0894 MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Base.explicitTop)
          columnPerm_0894 = targetTop_0894 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0894 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 2 6 6)) 9 := by
  have htop : targetTop_0894 =
      topOfPattern (R := ℤ) (angle6 1 1 2 2 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0894

/-- Explicit target top block for canonical pattern `(1, 1, 2, 2, 6, 7)`. -/
def targetTop_0895 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0895 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0895 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0895 : BottomDetBound targetTop_0895 9 := by
  have hU : rowTransform_0895.det.natAbs = 1 := by
    have hdet : rowTransform_0895.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_0895 hU
  have hcols := hrows.permuteColumns columnPerm_0895
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0895 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_0895 = targetTop_0895 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0895 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 2 6 7)) 9 := by
  have htop : targetTop_0895 =
      topOfPattern (R := ℤ) (angle6 1 1 2 2 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0895

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard055
