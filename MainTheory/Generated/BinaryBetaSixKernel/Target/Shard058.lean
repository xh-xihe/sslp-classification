-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R051.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard058

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(1, 1, 2, 6, 6, 6)`. -/
def targetTop_0928 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0928 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 1;
     1, 0, 0]

def columnPerm_0928 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0928 : BottomDetBound targetTop_0928 9 := by
  have hU : rowTransform_0928.det.natAbs = 1 := by
    have hdet : rowTransform_0928.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0928 hU
  have hcols := hrows.permuteColumns columnPerm_0928
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0928 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0928 = targetTop_0928 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0928 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 6 6 6)) 9 := by
  have htop : targetTop_0928 =
      topOfPattern (R := ℤ) (angle6 1 1 2 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0928

/-- Explicit target top block for canonical pattern `(1, 1, 2, 6, 6, 7)`. -/
def targetTop_0929 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0929 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     0, 1, 0]

def columnPerm_0929 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0929 : BottomDetBound targetTop_0929 9 := by
  have hU : rowTransform_0929.det.natAbs = 1 := by
    have hdet : rowTransform_0929.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate.bottomBound.transformTopRows rowTransform_0929 hU
  have hcols := hrows.permuteColumns columnPerm_0929
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0929 MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Base.explicitTop)
          columnPerm_0929 = targetTop_0929 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0929 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 6 6 7)) 9 := by
  have htop : targetTop_0929 =
      topOfPattern (R := ℤ) (angle6 1 1 2 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0929

/-- Explicit target top block for canonical pattern `(1, 1, 2, 6, 7, 7)`. -/
def targetTop_0930 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0930 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     0, 1, 0]

def columnPerm_0930 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0930 : BottomDetBound targetTop_0930 9 := by
  have hU : rowTransform_0930.det.natAbs = 1 := by
    have hdet : rowTransform_0930.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_0930 hU
  have hcols := hrows.permuteColumns columnPerm_0930
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0930 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_0930 = targetTop_0930 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0930 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 6 7 7)) 9 := by
  have htop : targetTop_0930 =
      topOfPattern (R := ℤ) (angle6 1 1 2 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0930

/-- Explicit target top block for canonical pattern `(1, 1, 2, 7, 7, 7)`. -/
def targetTop_0931 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0931 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 1;
     1, 0, 0]

def columnPerm_0931 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0931 : BottomDetBound targetTop_0931 9 := by
  have hU : rowTransform_0931.det.natAbs = 1 := by
    have hdet : rowTransform_0931.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0931 hU
  have hcols := hrows.permuteColumns columnPerm_0931
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0931 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0931 = targetTop_0931 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0931 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 7 7 7)) 9 := by
  have htop : targetTop_0931 =
      topOfPattern (R := ℤ) (angle6 1 1 2 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0931

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 3, 3, 3, 3)`. -/
def targetTop_0932 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0932 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0932 :
    TopRowRelation targetTop_0932 relationCoefficients_0932 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0932, relationCoefficients_0932, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0932 : BottomDetBound targetTop_0932 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0932

theorem canonicalBound_0932 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 3 3 3)) 9 := by
  have htop : targetTop_0932 =
      topOfPattern (R := ℤ) (angle6 1 1 3 3 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0932

/-- Explicit target top block for canonical pattern `(1, 1, 3, 3, 3, 4)`. -/
def targetTop_0933 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 0;
     0, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0933 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_0933 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0933 : BottomDetBound targetTop_0933 9 := by
  have hU : rowTransform_0933.det.natAbs = 1 := by
    have hdet : rowTransform_0933.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0933 hU
  have hcols := hrows.permuteColumns columnPerm_0933
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0933 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0933 = targetTop_0933 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0933 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 3 3 4)) 9 := by
  have htop : targetTop_0933 =
      topOfPattern (R := ℤ) (angle6 1 1 3 3 3 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0933

/-- Explicit target top block for canonical pattern `(1, 1, 3, 3, 3, 5)`. -/
def targetTop_0934 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0934 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     1, 0, 0;
     0, 0, 1]

def columnPerm_0934 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0934 : BottomDetBound targetTop_0934 9 := by
  have hU : rowTransform_0934.det.natAbs = 1 := by
    have hdet : rowTransform_0934.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0934 hU
  have hcols := hrows.permuteColumns columnPerm_0934
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0934 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0934 = targetTop_0934 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0934 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 3 3 5)) 9 := by
  have htop : targetTop_0934 =
      topOfPattern (R := ℤ) (angle6 1 1 3 3 3 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0934

/-- Explicit target top block for canonical pattern `(1, 1, 3, 3, 3, 6)`. -/
def targetTop_0935 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 0;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0935 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 1;
     0, 0, 1]

def columnPerm_0935 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0935 : BottomDetBound targetTop_0935 9 := by
  have hU : rowTransform_0935.det.natAbs = 1 := by
    have hdet : rowTransform_0935.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0935 hU
  have hcols := hrows.permuteColumns columnPerm_0935
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0935 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0935 = targetTop_0935 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0935 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 3 3 6)) 9 := by
  have htop : targetTop_0935 =
      topOfPattern (R := ℤ) (angle6 1 1 3 3 3 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0935

/-- Explicit target top block for canonical pattern `(1, 1, 3, 3, 3, 7)`. -/
def targetTop_0936 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0936 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     1, 0, 1;
     0, 0, 1]

def columnPerm_0936 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0936 : BottomDetBound targetTop_0936 9 := by
  have hU : rowTransform_0936.det.natAbs = 1 := by
    have hdet : rowTransform_0936.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0936 hU
  have hcols := hrows.permuteColumns columnPerm_0936
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0936 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0936 = targetTop_0936 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0936 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 3 3 7)) 9 := by
  have htop : targetTop_0936 =
      topOfPattern (R := ℤ) (angle6 1 1 3 3 3 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0936

/-- Explicit target top block for canonical pattern `(1, 1, 3, 3, 4, 4)`. -/
def targetTop_0937 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 0;
     0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0937 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0937 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0937 : BottomDetBound targetTop_0937 9 := by
  have hU : rowTransform_0937.det.natAbs = 1 := by
    have hdet : rowTransform_0937.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate.bottomBound.transformTopRows rowTransform_0937 hU
  have hcols := hrows.permuteColumns columnPerm_0937
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0937 MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Base.explicitTop)
          columnPerm_0937 = targetTop_0937 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0937 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 3 4 4)) 9 := by
  have htop : targetTop_0937 =
      topOfPattern (R := ℤ) (angle6 1 1 3 3 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0937

/-- Explicit target top block for canonical pattern `(1, 1, 3, 3, 4, 5)`. -/
def targetTop_0938 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 1;
     0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0938 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0938 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0938 : BottomDetBound targetTop_0938 9 := by
  have hU : rowTransform_0938.det.natAbs = 1 := by
    have hdet : rowTransform_0938.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_0938 hU
  have hcols := hrows.permuteColumns columnPerm_0938
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0938 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_0938 = targetTop_0938 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0938 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 3 4 5)) 9 := by
  have htop : targetTop_0938 =
      topOfPattern (R := ℤ) (angle6 1 1 3 3 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0938

/-- Explicit target top block for canonical pattern `(1, 1, 3, 3, 4, 6)`. -/
def targetTop_0939 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 0;
     0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0939 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, (-1);
     0, 1, 0;
     0, 0, 1]

def columnPerm_0939 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0939 : BottomDetBound targetTop_0939 9 := by
  have hU : rowTransform_0939.det.natAbs = 1 := by
    have hdet : rowTransform_0939.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate.bottomBound.transformTopRows rowTransform_0939 hU
  have hcols := hrows.permuteColumns columnPerm_0939
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0939 MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Base.explicitTop)
          columnPerm_0939 = targetTop_0939 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0939 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 3 4 6)) 9 := by
  have htop : targetTop_0939 =
      topOfPattern (R := ℤ) (angle6 1 1 3 3 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0939

/-- Explicit target top block for canonical pattern `(1, 1, 3, 3, 4, 7)`. -/
def targetTop_0940 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 1;
     0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0940 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_0940 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 0, 1, 4, 5]
  invFun := ![2, 3, 0, 1, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0940 : BottomDetBound targetTop_0940 9 := by
  have hU : rowTransform_0940.det.natAbs = 1 := by
    have hdet : rowTransform_0940.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_0940 hU
  have hcols := hrows.permuteColumns columnPerm_0940
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0940 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_0940 = targetTop_0940 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0940 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 3 4 7)) 9 := by
  have htop : targetTop_0940 =
      topOfPattern (R := ℤ) (angle6 1 1 3 3 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0940

/-- Explicit target top block for canonical pattern `(1, 1, 3, 3, 5, 5)`. -/
def targetTop_0941 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0941 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0941 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0941 : BottomDetBound targetTop_0941 9 := by
  have hU : rowTransform_0941.det.natAbs = 1 := by
    have hdet : rowTransform_0941.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate.bottomBound.transformTopRows rowTransform_0941 hU
  have hcols := hrows.permuteColumns columnPerm_0941
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0941 MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Base.explicitTop)
          columnPerm_0941 = targetTop_0941 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0941 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 3 5 5)) 9 := by
  have htop : targetTop_0941 =
      topOfPattern (R := ℤ) (angle6 1 1 3 3 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0941

/-- Explicit target top block for canonical pattern `(1, 1, 3, 3, 5, 6)`. -/
def targetTop_0942 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 0;
     0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0942 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0942 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0942 : BottomDetBound targetTop_0942 9 := by
  have hU : rowTransform_0942.det.natAbs = 1 := by
    have hdet : rowTransform_0942.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R051.Aggregate.bottomBound.transformTopRows rowTransform_0942 hU
  have hcols := hrows.permuteColumns columnPerm_0942
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0942 MainTheory.Generated.BinaryBetaSixKernel.Representative.R051.Base.explicitTop)
          columnPerm_0942 = targetTop_0942 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0942 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 3 5 6)) 9 := by
  have htop : targetTop_0942 =
      topOfPattern (R := ℤ) (angle6 1 1 3 3 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0942

/-- Explicit target top block for canonical pattern `(1, 1, 3, 3, 5, 7)`. -/
def targetTop_0943 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0943 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0943 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0943 : BottomDetBound targetTop_0943 9 := by
  have hU : rowTransform_0943.det.natAbs = 1 := by
    have hdet : rowTransform_0943.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate.bottomBound.transformTopRows rowTransform_0943 hU
  have hcols := hrows.permuteColumns columnPerm_0943
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0943 MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Base.explicitTop)
          columnPerm_0943 = targetTop_0943 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0943 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 3 5 7)) 9 := by
  have htop : targetTop_0943 =
      topOfPattern (R := ℤ) (angle6 1 1 3 3 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0943

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard058
