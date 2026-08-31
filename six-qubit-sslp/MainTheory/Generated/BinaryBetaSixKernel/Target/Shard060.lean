-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R049.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R052.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R053.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard060

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(1, 1, 3, 5, 6, 6)`. -/
def targetTop_0960 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 0;
     0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0960 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0960 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0960 : BottomDetBound targetTop_0960 9 := by
  have hU : rowTransform_0960.det.natAbs = 1 := by
    have hdet : rowTransform_0960.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R052.Aggregate.bottomBound.transformTopRows rowTransform_0960 hU
  have hcols := hrows.permuteColumns columnPerm_0960
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0960 MainTheory.Generated.BinaryBetaSixKernel.Representative.R052.Base.explicitTop)
          columnPerm_0960 = targetTop_0960 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0960 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 5 6 6)) 9 := by
  have htop : targetTop_0960 =
      topOfPattern (R := ℤ) (angle6 1 1 3 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0960

/-- Explicit target top block for canonical pattern `(1, 1, 3, 5, 6, 7)`. -/
def targetTop_0961 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 1;
     0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0961 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0961 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0961 : BottomDetBound targetTop_0961 9 := by
  have hU : rowTransform_0961.det.natAbs = 1 := by
    have hdet : rowTransform_0961.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R053.Aggregate.bottomBound.transformTopRows rowTransform_0961 hU
  have hcols := hrows.permuteColumns columnPerm_0961
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0961 MainTheory.Generated.BinaryBetaSixKernel.Representative.R053.Base.explicitTop)
          columnPerm_0961 = targetTop_0961 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0961 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 5 6 7)) 9 := by
  have htop : targetTop_0961 =
      topOfPattern (R := ℤ) (angle6 1 1 3 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0961

/-- Explicit target top block for canonical pattern `(1, 1, 3, 5, 7, 7)`. -/
def targetTop_0962 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0962 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0962 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0962 : BottomDetBound targetTop_0962 9 := by
  have hU : rowTransform_0962.det.natAbs = 1 := by
    have hdet : rowTransform_0962.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R049.Aggregate.bottomBound.transformTopRows rowTransform_0962 hU
  have hcols := hrows.permuteColumns columnPerm_0962
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0962 MainTheory.Generated.BinaryBetaSixKernel.Representative.R049.Base.explicitTop)
          columnPerm_0962 = targetTop_0962 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0962 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 5 7 7)) 9 := by
  have htop : targetTop_0962 =
      topOfPattern (R := ℤ) (angle6 1 1 3 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0962

/-- Explicit target top block for canonical pattern `(1, 1, 3, 6, 6, 6)`. -/
def targetTop_0963 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 0;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0963 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 1;
     1, 0, 0]

def columnPerm_0963 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0963 : BottomDetBound targetTop_0963 9 := by
  have hU : rowTransform_0963.det.natAbs = 1 := by
    have hdet : rowTransform_0963.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0963 hU
  have hcols := hrows.permuteColumns columnPerm_0963
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0963 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0963 = targetTop_0963 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0963 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 6 6 6)) 9 := by
  have htop : targetTop_0963 =
      topOfPattern (R := ℤ) (angle6 1 1 3 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0963

/-- Explicit target top block for canonical pattern `(1, 1, 3, 6, 6, 7)`. -/
def targetTop_0964 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0964 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 1;
     0, 1, 0]

def columnPerm_0964 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0964 : BottomDetBound targetTop_0964 9 := by
  have hU : rowTransform_0964.det.natAbs = 1 := by
    have hdet : rowTransform_0964.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate.bottomBound.transformTopRows rowTransform_0964 hU
  have hcols := hrows.permuteColumns columnPerm_0964
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0964 MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Base.explicitTop)
          columnPerm_0964 = targetTop_0964 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0964 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 6 6 7)) 9 := by
  have htop : targetTop_0964 =
      topOfPattern (R := ℤ) (angle6 1 1 3 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0964

/-- Explicit target top block for canonical pattern `(1, 1, 3, 6, 7, 7)`. -/
def targetTop_0965 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0965 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 1;
     0, 1, 0]

def columnPerm_0965 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0965 : BottomDetBound targetTop_0965 9 := by
  have hU : rowTransform_0965.det.natAbs = 1 := by
    have hdet : rowTransform_0965.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_0965 hU
  have hcols := hrows.permuteColumns columnPerm_0965
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0965 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_0965 = targetTop_0965 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0965 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 6 7 7)) 9 := by
  have htop : targetTop_0965 =
      topOfPattern (R := ℤ) (angle6 1 1 3 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0965

/-- Explicit target top block for canonical pattern `(1, 1, 3, 7, 7, 7)`. -/
def targetTop_0966 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0966 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     1, 0, 1;
     1, 0, 0]

def columnPerm_0966 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0966 : BottomDetBound targetTop_0966 9 := by
  have hU : rowTransform_0966.det.natAbs = 1 := by
    have hdet : rowTransform_0966.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0966 hU
  have hcols := hrows.permuteColumns columnPerm_0966
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0966 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0966 = targetTop_0966 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0966 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 7 7 7)) 9 := by
  have htop : targetTop_0966 =
      topOfPattern (R := ℤ) (angle6 1 1 3 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0966

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 4, 4, 4, 4)`. -/
def targetTop_0967 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0967 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0967 :
    TopRowRelation targetTop_0967 relationCoefficients_0967 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0967, relationCoefficients_0967, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0967 : BottomDetBound targetTop_0967 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0967

theorem canonicalBound_0967 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 4 4 4 4)) 9 := by
  have htop : targetTop_0967 =
      topOfPattern (R := ℤ) (angle6 1 1 4 4 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0967

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 4, 4, 4, 5)`. -/
def targetTop_0968 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0968 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0968 :
    TopRowRelation targetTop_0968 relationCoefficients_0968 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0968, relationCoefficients_0968, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0968 : BottomDetBound targetTop_0968 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0968

theorem canonicalBound_0968 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 4 4 4 5)) 9 := by
  have htop : targetTop_0968 =
      topOfPattern (R := ℤ) (angle6 1 1 4 4 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0968

/-- Explicit target top block for canonical pattern `(1, 1, 4, 4, 4, 6)`. -/
def targetTop_0969 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0969 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 1]

def columnPerm_0969 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0969 : BottomDetBound targetTop_0969 9 := by
  have hU : rowTransform_0969.det.natAbs = 1 := by
    have hdet : rowTransform_0969.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0969 hU
  have hcols := hrows.permuteColumns columnPerm_0969
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0969 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0969 = targetTop_0969 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0969 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 4 4 4 6)) 9 := by
  have htop : targetTop_0969 =
      topOfPattern (R := ℤ) (angle6 1 1 4 4 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0969

/-- Explicit target top block for canonical pattern `(1, 1, 4, 4, 4, 7)`. -/
def targetTop_0970 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0970 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 0, 1;
     1, 0, 1]

def columnPerm_0970 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0970 : BottomDetBound targetTop_0970 9 := by
  have hU : rowTransform_0970.det.natAbs = 1 := by
    have hdet : rowTransform_0970.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0970 hU
  have hcols := hrows.permuteColumns columnPerm_0970
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0970 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0970 = targetTop_0970 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0970 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 4 4 4 7)) 9 := by
  have htop : targetTop_0970 =
      topOfPattern (R := ℤ) (angle6 1 1 4 4 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0970

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 4, 4, 5, 5)`. -/
def targetTop_0971 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0971 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0971 :
    TopRowRelation targetTop_0971 relationCoefficients_0971 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0971, relationCoefficients_0971, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0971 : BottomDetBound targetTop_0971 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0971

theorem canonicalBound_0971 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 4 4 5 5)) 9 := by
  have htop : targetTop_0971 =
      topOfPattern (R := ℤ) (angle6 1 1 4 4 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0971

/-- Explicit target top block for canonical pattern `(1, 1, 4, 4, 5, 6)`. -/
def targetTop_0972 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0972 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0972 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0972 : BottomDetBound targetTop_0972 9 := by
  have hU : rowTransform_0972.det.natAbs = 1 := by
    have hdet : rowTransform_0972.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate.bottomBound.transformTopRows rowTransform_0972 hU
  have hcols := hrows.permuteColumns columnPerm_0972
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0972 MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Base.explicitTop)
          columnPerm_0972 = targetTop_0972 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0972 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 4 4 5 6)) 9 := by
  have htop : targetTop_0972 =
      topOfPattern (R := ℤ) (angle6 1 1 4 4 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0972

/-- Explicit target top block for canonical pattern `(1, 1, 4, 4, 5, 7)`. -/
def targetTop_0973 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0973 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0973 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0973 : BottomDetBound targetTop_0973 9 := by
  have hU : rowTransform_0973.det.natAbs = 1 := by
    have hdet : rowTransform_0973.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate.bottomBound.transformTopRows rowTransform_0973 hU
  have hcols := hrows.permuteColumns columnPerm_0973
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0973 MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Base.explicitTop)
          columnPerm_0973 = targetTop_0973 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0973 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 4 4 5 7)) 9 := by
  have htop : targetTop_0973 =
      topOfPattern (R := ℤ) (angle6 1 1 4 4 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0973

/-- Explicit target top block for canonical pattern `(1, 1, 4, 4, 6, 6)`. -/
def targetTop_0974 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0974 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0974 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0974 : BottomDetBound targetTop_0974 9 := by
  have hU : rowTransform_0974.det.natAbs = 1 := by
    have hdet : rowTransform_0974.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate.bottomBound.transformTopRows rowTransform_0974 hU
  have hcols := hrows.permuteColumns columnPerm_0974
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0974 MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Base.explicitTop)
          columnPerm_0974 = targetTop_0974 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0974 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 4 4 6 6)) 9 := by
  have htop : targetTop_0974 =
      topOfPattern (R := ℤ) (angle6 1 1 4 4 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0974

/-- Explicit target top block for canonical pattern `(1, 1, 4, 4, 6, 7)`. -/
def targetTop_0975 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0975 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0975 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0975 : BottomDetBound targetTop_0975 9 := by
  have hU : rowTransform_0975.det.natAbs = 1 := by
    have hdet : rowTransform_0975.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_0975 hU
  have hcols := hrows.permuteColumns columnPerm_0975
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0975 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_0975 = targetTop_0975 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0975 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 4 4 6 7)) 9 := by
  have htop : targetTop_0975 =
      topOfPattern (R := ℤ) (angle6 1 1 4 4 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0975

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard060
