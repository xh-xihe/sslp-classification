-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard013

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 2, 2, 2, 6)`. -/
def targetTop_0208 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0208 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0208 :
    TopRowRelation targetTop_0208 relationCoefficients_0208 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0208, relationCoefficients_0208, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0208 : BottomDetBound targetTop_0208 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0208

theorem canonicalBound_0208 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 2 2 6)) 9 := by
  have htop : targetTop_0208 =
      topOfPattern (R := ℤ) (angle6 0 0 2 2 2 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0208

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 2, 2, 2, 7)`. -/
def targetTop_0209 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0209 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0209 :
    TopRowRelation targetTop_0209 relationCoefficients_0209 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0209, relationCoefficients_0209, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0209 : BottomDetBound targetTop_0209 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0209

theorem canonicalBound_0209 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 2 2 7)) 9 := by
  have htop : targetTop_0209 =
      topOfPattern (R := ℤ) (angle6 0 0 2 2 2 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0209

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 2, 2, 3, 3)`. -/
def targetTop_0210 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0210 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0210 :
    TopRowRelation targetTop_0210 relationCoefficients_0210 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0210, relationCoefficients_0210, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0210 : BottomDetBound targetTop_0210 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0210

theorem canonicalBound_0210 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 2 3 3)) 9 := by
  have htop : targetTop_0210 =
      topOfPattern (R := ℤ) (angle6 0 0 2 2 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0210

/-- Explicit target top block for canonical pattern `(0, 0, 2, 2, 3, 4)`. -/
def targetTop_0211 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 0;
     0, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0211 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 0;
     0, 0, 1]

def columnPerm_0211 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0211 : BottomDetBound targetTop_0211 9 := by
  have hU : rowTransform_0211.det.natAbs = 1 := by
    have hdet : rowTransform_0211.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0211 hU
  have hcols := hrows.permuteColumns columnPerm_0211
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0211 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0211 = targetTop_0211 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0211 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 2 3 4)) 9 := by
  have htop : targetTop_0211 =
      topOfPattern (R := ℤ) (angle6 0 0 2 2 3 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0211

/-- Explicit target top block for canonical pattern `(0, 0, 2, 2, 3, 5)`. -/
def targetTop_0212 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0212 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 1, 0;
     0, 0, 1]

def columnPerm_0212 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0212 : BottomDetBound targetTop_0212 9 := by
  have hU : rowTransform_0212.det.natAbs = 1 := by
    have hdet : rowTransform_0212.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0212 hU
  have hcols := hrows.permuteColumns columnPerm_0212
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0212 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0212 = targetTop_0212 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0212 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 2 3 5)) 9 := by
  have htop : targetTop_0212 =
      topOfPattern (R := ℤ) (angle6 0 0 2 2 3 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0212

/-- Explicit target top block for canonical pattern `(0, 0, 2, 2, 3, 6)`. -/
def targetTop_0213 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 0;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0213 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 1;
     0, 0, 1]

def columnPerm_0213 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0213 : BottomDetBound targetTop_0213 9 := by
  have hU : rowTransform_0213.det.natAbs = 1 := by
    have hdet : rowTransform_0213.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0213 hU
  have hcols := hrows.permuteColumns columnPerm_0213
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0213 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0213 = targetTop_0213 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0213 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 2 3 6)) 9 := by
  have htop : targetTop_0213 =
      topOfPattern (R := ℤ) (angle6 0 0 2 2 3 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0213

/-- Explicit target top block for canonical pattern `(0, 0, 2, 2, 3, 7)`. -/
def targetTop_0214 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0214 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 1, 1;
     0, 0, 1]

def columnPerm_0214 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0214 : BottomDetBound targetTop_0214 9 := by
  have hU : rowTransform_0214.det.natAbs = 1 := by
    have hdet : rowTransform_0214.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0214 hU
  have hcols := hrows.permuteColumns columnPerm_0214
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0214 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0214 = targetTop_0214 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0214 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 2 3 7)) 9 := by
  have htop : targetTop_0214 =
      topOfPattern (R := ℤ) (angle6 0 0 2 2 3 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0214

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 2, 2, 4, 4)`. -/
def targetTop_0215 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0215 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0215 :
    TopRowRelation targetTop_0215 relationCoefficients_0215 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0215, relationCoefficients_0215, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0215 : BottomDetBound targetTop_0215 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0215

theorem canonicalBound_0215 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 2 4 4)) 9 := by
  have htop : targetTop_0215 =
      topOfPattern (R := ℤ) (angle6 0 0 2 2 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0215

/-- Explicit target top block for canonical pattern `(0, 0, 2, 2, 4, 5)`. -/
def targetTop_0216 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0216 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 1]

def columnPerm_0216 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0216 : BottomDetBound targetTop_0216 9 := by
  have hU : rowTransform_0216.det.natAbs = 1 := by
    have hdet : rowTransform_0216.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0216 hU
  have hcols := hrows.permuteColumns columnPerm_0216
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0216 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0216 = targetTop_0216 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0216 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 2 4 5)) 9 := by
  have htop : targetTop_0216 =
      topOfPattern (R := ℤ) (angle6 0 0 2 2 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0216

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 2, 2, 4, 6)`. -/
def targetTop_0217 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0217 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0217 :
    TopRowRelation targetTop_0217 relationCoefficients_0217 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0217, relationCoefficients_0217, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0217 : BottomDetBound targetTop_0217 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0217

theorem canonicalBound_0217 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 2 4 6)) 9 := by
  have htop : targetTop_0217 =
      topOfPattern (R := ℤ) (angle6 0 0 2 2 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0217

/-- Explicit target top block for canonical pattern `(0, 0, 2, 2, 4, 7)`. -/
def targetTop_0218 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0218 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 1;
     0, 1, 1]

def columnPerm_0218 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0218 : BottomDetBound targetTop_0218 9 := by
  have hU : rowTransform_0218.det.natAbs = 1 := by
    have hdet : rowTransform_0218.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0218 hU
  have hcols := hrows.permuteColumns columnPerm_0218
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0218 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0218 = targetTop_0218 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0218 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 2 4 7)) 9 := by
  have htop : targetTop_0218 =
      topOfPattern (R := ℤ) (angle6 0 0 2 2 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0218

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 2, 2, 5, 5)`. -/
def targetTop_0219 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0219 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0219 :
    TopRowRelation targetTop_0219 relationCoefficients_0219 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0219, relationCoefficients_0219, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0219 : BottomDetBound targetTop_0219 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0219

theorem canonicalBound_0219 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 2 5 5)) 9 := by
  have htop : targetTop_0219 =
      topOfPattern (R := ℤ) (angle6 0 0 2 2 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0219

/-- Explicit target top block for canonical pattern `(0, 0, 2, 2, 5, 6)`. -/
def targetTop_0220 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 0;
     0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0220 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 1;
     0, 1, 1]

def columnPerm_0220 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0220 : BottomDetBound targetTop_0220 9 := by
  have hU : rowTransform_0220.det.natAbs = 1 := by
    have hdet : rowTransform_0220.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0220 hU
  have hcols := hrows.permuteColumns columnPerm_0220
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0220 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0220 = targetTop_0220 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0220 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 2 5 6)) 9 := by
  have htop : targetTop_0220 =
      topOfPattern (R := ℤ) (angle6 0 0 2 2 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0220

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 2, 2, 5, 7)`. -/
def targetTop_0221 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0221 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0221 :
    TopRowRelation targetTop_0221 relationCoefficients_0221 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0221, relationCoefficients_0221, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0221 : BottomDetBound targetTop_0221 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0221

theorem canonicalBound_0221 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 2 5 7)) 9 := by
  have htop : targetTop_0221 =
      topOfPattern (R := ℤ) (angle6 0 0 2 2 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0221

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 2, 2, 6, 6)`. -/
def targetTop_0222 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0222 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0222 :
    TopRowRelation targetTop_0222 relationCoefficients_0222 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0222, relationCoefficients_0222, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0222 : BottomDetBound targetTop_0222 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0222

theorem canonicalBound_0222 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 2 6 6)) 9 := by
  have htop : targetTop_0222 =
      topOfPattern (R := ℤ) (angle6 0 0 2 2 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0222

/-- Explicit target top block for canonical pattern `(0, 0, 2, 2, 6, 7)`. -/
def targetTop_0223 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0223 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, 1;
     0, 1, 1]

def columnPerm_0223 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0223 : BottomDetBound targetTop_0223 9 := by
  have hU : rowTransform_0223.det.natAbs = 1 := by
    have hdet : rowTransform_0223.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0223 hU
  have hcols := hrows.permuteColumns columnPerm_0223
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0223 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0223 = targetTop_0223 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0223 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 2 6 7)) 9 := by
  have htop : targetTop_0223 =
      topOfPattern (R := ℤ) (angle6 0 0 2 2 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0223

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard013
