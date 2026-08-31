-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R042.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard061

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(1, 1, 4, 4, 7, 7)`. -/
def targetTop_0976 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0976 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0976 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0976 : BottomDetBound targetTop_0976 9 := by
  have hU : rowTransform_0976.det.natAbs = 1 := by
    have hdet : rowTransform_0976.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate.bottomBound.transformTopRows rowTransform_0976 hU
  have hcols := hrows.permuteColumns columnPerm_0976
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0976 MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Base.explicitTop)
          columnPerm_0976 = targetTop_0976 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0976 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 4 4 7 7)) 9 := by
  have htop : targetTop_0976 =
      topOfPattern (R := ℤ) (angle6 1 1 4 4 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0976

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 4, 5, 5, 5)`. -/
def targetTop_0977 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0977 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0977 :
    TopRowRelation targetTop_0977 relationCoefficients_0977 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0977, relationCoefficients_0977, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0977 : BottomDetBound targetTop_0977 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0977

theorem canonicalBound_0977 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 4 5 5 5)) 9 := by
  have htop : targetTop_0977 =
      topOfPattern (R := ℤ) (angle6 1 1 4 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0977

/-- Explicit target top block for canonical pattern `(1, 1, 4, 5, 5, 6)`. -/
def targetTop_0978 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0978 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0978 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0978 : BottomDetBound targetTop_0978 9 := by
  have hU : rowTransform_0978.det.natAbs = 1 := by
    have hdet : rowTransform_0978.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_0978 hU
  have hcols := hrows.permuteColumns columnPerm_0978
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0978 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_0978 = targetTop_0978 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0978 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 4 5 5 6)) 9 := by
  have htop : targetTop_0978 =
      topOfPattern (R := ℤ) (angle6 1 1 4 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0978

/-- Explicit target top block for canonical pattern `(1, 1, 4, 5, 5, 7)`. -/
def targetTop_0979 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0979 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0979 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0979 : BottomDetBound targetTop_0979 9 := by
  have hU : rowTransform_0979.det.natAbs = 1 := by
    have hdet : rowTransform_0979.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_0979 hU
  have hcols := hrows.permuteColumns columnPerm_0979
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0979 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_0979 = targetTop_0979 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0979 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 4 5 5 7)) 9 := by
  have htop : targetTop_0979 =
      topOfPattern (R := ℤ) (angle6 1 1 4 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0979

/-- Explicit target top block for canonical pattern `(1, 1, 4, 5, 6, 6)`. -/
def targetTop_0980 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0980 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 1, 1]

def columnPerm_0980 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0980 : BottomDetBound targetTop_0980 9 := by
  have hU : rowTransform_0980.det.natAbs = 1 := by
    have hdet : rowTransform_0980.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_0980 hU
  have hcols := hrows.permuteColumns columnPerm_0980
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0980 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_0980 = targetTop_0980 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0980 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 4 5 6 6)) 9 := by
  have htop : targetTop_0980 =
      topOfPattern (R := ℤ) (angle6 1 1 4 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0980

/-- Explicit target top block for canonical pattern `(1, 1, 4, 5, 6, 7)`. -/
def targetTop_0981 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0981 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0981 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0981 : BottomDetBound targetTop_0981 9 := by
  have hU : rowTransform_0981.det.natAbs = 1 := by
    have hdet : rowTransform_0981.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R042.Aggregate.bottomBound.transformTopRows rowTransform_0981 hU
  have hcols := hrows.permuteColumns columnPerm_0981
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0981 MainTheory.Generated.BinaryBetaSixKernel.Representative.R042.Base.explicitTop)
          columnPerm_0981 = targetTop_0981 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0981 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 4 5 6 7)) 9 := by
  have htop : targetTop_0981 =
      topOfPattern (R := ℤ) (angle6 1 1 4 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0981

/-- Explicit target top block for canonical pattern `(1, 1, 4, 5, 7, 7)`. -/
def targetTop_0982 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0982 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 0;
     0, 1, 1]

def columnPerm_0982 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0982 : BottomDetBound targetTop_0982 9 := by
  have hU : rowTransform_0982.det.natAbs = 1 := by
    have hdet : rowTransform_0982.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_0982 hU
  have hcols := hrows.permuteColumns columnPerm_0982
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0982 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_0982 = targetTop_0982 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0982 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 4 5 7 7)) 9 := by
  have htop : targetTop_0982 =
      topOfPattern (R := ℤ) (angle6 1 1 4 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0982

/-- Explicit target top block for canonical pattern `(1, 1, 4, 6, 6, 6)`. -/
def targetTop_0983 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 0;
     0, 0, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0983 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     1, 0, 1]

def columnPerm_0983 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0983 : BottomDetBound targetTop_0983 9 := by
  have hU : rowTransform_0983.det.natAbs = 1 := by
    have hdet : rowTransform_0983.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0983 hU
  have hcols := hrows.permuteColumns columnPerm_0983
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0983 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0983 = targetTop_0983 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0983 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 4 6 6 6)) 9 := by
  have htop : targetTop_0983 =
      topOfPattern (R := ℤ) (angle6 1 1 4 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0983

/-- Explicit target top block for canonical pattern `(1, 1, 4, 6, 6, 7)`. -/
def targetTop_0984 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0984 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 1, 1]

def columnPerm_0984 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0984 : BottomDetBound targetTop_0984 9 := by
  have hU : rowTransform_0984.det.natAbs = 1 := by
    have hdet : rowTransform_0984.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate.bottomBound.transformTopRows rowTransform_0984 hU
  have hcols := hrows.permuteColumns columnPerm_0984
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0984 MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Base.explicitTop)
          columnPerm_0984 = targetTop_0984 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0984 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 4 6 6 7)) 9 := by
  have htop : targetTop_0984 =
      topOfPattern (R := ℤ) (angle6 1 1 4 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0984

/-- Explicit target top block for canonical pattern `(1, 1, 4, 6, 7, 7)`. -/
def targetTop_0985 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0985 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 1, 1]

def columnPerm_0985 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0985 : BottomDetBound targetTop_0985 9 := by
  have hU : rowTransform_0985.det.natAbs = 1 := by
    have hdet : rowTransform_0985.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_0985 hU
  have hcols := hrows.permuteColumns columnPerm_0985
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0985 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_0985 = targetTop_0985 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0985 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 4 6 7 7)) 9 := by
  have htop : targetTop_0985 =
      topOfPattern (R := ℤ) (angle6 1 1 4 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0985

/-- Explicit target top block for canonical pattern `(1, 1, 4, 7, 7, 7)`. -/
def targetTop_0986 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0986 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 0;
     1, 0, 1]

def columnPerm_0986 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0986 : BottomDetBound targetTop_0986 9 := by
  have hU : rowTransform_0986.det.natAbs = 1 := by
    have hdet : rowTransform_0986.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0986 hU
  have hcols := hrows.permuteColumns columnPerm_0986
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0986 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0986 = targetTop_0986 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0986 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 4 7 7 7)) 9 := by
  have htop : targetTop_0986 =
      topOfPattern (R := ℤ) (angle6 1 1 4 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0986

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 5, 5, 5, 5)`. -/
def targetTop_0987 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0987 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0987 :
    TopRowRelation targetTop_0987 relationCoefficients_0987 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0987, relationCoefficients_0987, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0987 : BottomDetBound targetTop_0987 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0987

theorem canonicalBound_0987 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 5 5 5 5)) 9 := by
  have htop : targetTop_0987 =
      topOfPattern (R := ℤ) (angle6 1 1 5 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0987

/-- Explicit target top block for canonical pattern `(1, 1, 5, 5, 5, 6)`. -/
def targetTop_0988 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0988 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 0, 1;
     1, 0, 1]

def columnPerm_0988 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0988 : BottomDetBound targetTop_0988 9 := by
  have hU : rowTransform_0988.det.natAbs = 1 := by
    have hdet : rowTransform_0988.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0988 hU
  have hcols := hrows.permuteColumns columnPerm_0988
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0988 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0988 = targetTop_0988 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0988 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 5 5 5 6)) 9 := by
  have htop : targetTop_0988 =
      topOfPattern (R := ℤ) (angle6 1 1 5 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0988

/-- Explicit target top block for canonical pattern `(1, 1, 5, 5, 5, 7)`. -/
def targetTop_0989 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0989 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 0, 1;
     1, 0, 1]

def columnPerm_0989 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0989 : BottomDetBound targetTop_0989 9 := by
  have hU : rowTransform_0989.det.natAbs = 1 := by
    have hdet : rowTransform_0989.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0989 hU
  have hcols := hrows.permuteColumns columnPerm_0989
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0989 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0989 = targetTop_0989 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0989 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 5 5 5 7)) 9 := by
  have htop : targetTop_0989 =
      topOfPattern (R := ℤ) (angle6 1 1 5 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0989

/-- Explicit target top block for canonical pattern `(1, 1, 5, 5, 6, 6)`. -/
def targetTop_0990 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0990 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0990 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0990 : BottomDetBound targetTop_0990 9 := by
  have hU : rowTransform_0990.det.natAbs = 1 := by
    have hdet : rowTransform_0990.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate.bottomBound.transformTopRows rowTransform_0990 hU
  have hcols := hrows.permuteColumns columnPerm_0990
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0990 MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Base.explicitTop)
          columnPerm_0990 = targetTop_0990 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0990 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 5 5 6 6)) 9 := by
  have htop : targetTop_0990 =
      topOfPattern (R := ℤ) (angle6 1 1 5 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0990

/-- Explicit target top block for canonical pattern `(1, 1, 5, 5, 6, 7)`. -/
def targetTop_0991 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0991 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0991 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0991 : BottomDetBound targetTop_0991 9 := by
  have hU : rowTransform_0991.det.natAbs = 1 := by
    have hdet : rowTransform_0991.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_0991 hU
  have hcols := hrows.permuteColumns columnPerm_0991
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0991 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_0991 = targetTop_0991 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0991 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 5 5 6 7)) 9 := by
  have htop : targetTop_0991 =
      topOfPattern (R := ℤ) (angle6 1 1 5 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0991

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard061
