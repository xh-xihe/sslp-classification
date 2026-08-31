-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R006.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R007.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard017

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 3, 3, 6, 6)`. -/
def targetTop_0272 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 0;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0272 : Fin 3 → ℤ :=
  ![1, (-1), 1]

theorem topRelation_0272 :
    TopRowRelation targetTop_0272 relationCoefficients_0272 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0272, relationCoefficients_0272, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0272 : BottomDetBound targetTop_0272 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0272

theorem canonicalBound_0272 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 3 6 6)) 9 := by
  have htop : targetTop_0272 =
      topOfPattern (R := ℤ) (angle6 0 0 3 3 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0272

/-- Explicit target top block for canonical pattern `(0, 0, 3, 3, 6, 7)`. -/
def targetTop_0273 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0273 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 1, 1;
     0, 1, 1]

def columnPerm_0273 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0273 : BottomDetBound targetTop_0273 9 := by
  have hU : rowTransform_0273.det.natAbs = 1 := by
    have hdet : rowTransform_0273.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0273 hU
  have hcols := hrows.permuteColumns columnPerm_0273
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0273 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0273 = targetTop_0273 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0273 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 3 6 7)) 9 := by
  have htop : targetTop_0273 =
      topOfPattern (R := ℤ) (angle6 0 0 3 3 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0273

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 3, 3, 7, 7)`. -/
def targetTop_0274 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0274 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0274 :
    TopRowRelation targetTop_0274 relationCoefficients_0274 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0274, relationCoefficients_0274, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0274 : BottomDetBound targetTop_0274 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0274

theorem canonicalBound_0274 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 3 7 7)) 9 := by
  have htop : targetTop_0274 =
      topOfPattern (R := ℤ) (angle6 0 0 3 3 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0274

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 3, 4, 4, 4)`. -/
def targetTop_0275 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0275 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0275 :
    TopRowRelation targetTop_0275 relationCoefficients_0275 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0275, relationCoefficients_0275, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0275 : BottomDetBound targetTop_0275 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0275

theorem canonicalBound_0275 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 4 4 4)) 9 := by
  have htop : targetTop_0275 =
      topOfPattern (R := ℤ) (angle6 0 0 3 4 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0275

/-- Explicit target top block for canonical pattern `(0, 0, 3, 4, 4, 5)`. -/
def targetTop_0276 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 1;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0276 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 1, 0;
     1, 0, 1]

def columnPerm_0276 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0276 : BottomDetBound targetTop_0276 9 := by
  have hU : rowTransform_0276.det.natAbs = 1 := by
    have hdet : rowTransform_0276.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0276 hU
  have hcols := hrows.permuteColumns columnPerm_0276
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0276 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0276 = targetTop_0276 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0276 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 4 4 5)) 9 := by
  have htop : targetTop_0276 =
      topOfPattern (R := ℤ) (angle6 0 0 3 4 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0276

/-- Explicit target top block for canonical pattern `(0, 0, 3, 4, 4, 6)`. -/
def targetTop_0277 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 0;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0277 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 1, 1;
     1, 0, 1]

def columnPerm_0277 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0277 : BottomDetBound targetTop_0277 9 := by
  have hU : rowTransform_0277.det.natAbs = 1 := by
    have hdet : rowTransform_0277.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0277 hU
  have hcols := hrows.permuteColumns columnPerm_0277
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0277 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0277 = targetTop_0277 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0277 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 4 4 6)) 9 := by
  have htop : targetTop_0277 =
      topOfPattern (R := ℤ) (angle6 0 0 3 4 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0277

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 3, 4, 4, 7)`. -/
def targetTop_0278 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 1;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0278 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0278 :
    TopRowRelation targetTop_0278 relationCoefficients_0278 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0278, relationCoefficients_0278, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0278 : BottomDetBound targetTop_0278 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0278

theorem canonicalBound_0278 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 4 4 7)) 9 := by
  have htop : targetTop_0278 =
      topOfPattern (R := ℤ) (angle6 0 0 3 4 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0278

/-- Explicit target top block for canonical pattern `(0, 0, 3, 4, 5, 5)`. -/
def targetTop_0279 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 1, 1;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0279 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 0;
     1, 0, 1]

def columnPerm_0279 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0279 : BottomDetBound targetTop_0279 9 := by
  have hU : rowTransform_0279.det.natAbs = 1 := by
    have hdet : rowTransform_0279.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0279 hU
  have hcols := hrows.permuteColumns columnPerm_0279
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0279 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0279 = targetTop_0279 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0279 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 4 5 5)) 9 := by
  have htop : targetTop_0279 =
      topOfPattern (R := ℤ) (angle6 0 0 3 4 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0279

/-- Explicit target top block for canonical pattern `(0, 0, 3, 4, 5, 6)`. -/
def targetTop_0280 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 1, 0;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0280 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_0280 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0280 : BottomDetBound targetTop_0280 9 := by
  have hU : rowTransform_0280.det.natAbs = 1 := by
    have hdet : rowTransform_0280.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R006.Aggregate.bottomBound.transformTopRows rowTransform_0280 hU
  have hcols := hrows.permuteColumns columnPerm_0280
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0280 MainTheory.Generated.BinaryBetaSixKernel.Representative.R006.Base.explicitTop)
          columnPerm_0280 = targetTop_0280 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0280 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 4 5 6)) 9 := by
  have htop : targetTop_0280 =
      topOfPattern (R := ℤ) (angle6 0 0 3 4 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0280

/-- Explicit target top block for canonical pattern `(0, 0, 3, 4, 5, 7)`. -/
def targetTop_0281 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 1, 1;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0281 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 0, 0;
     0, 1, 1]

def columnPerm_0281 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 5, 4]
  invFun := ![0, 1, 2, 3, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0281 : BottomDetBound targetTop_0281 9 := by
  have hU : rowTransform_0281.det.natAbs = 1 := by
    have hdet : rowTransform_0281.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Aggregate.bottomBound.transformTopRows rowTransform_0281 hU
  have hcols := hrows.permuteColumns columnPerm_0281
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0281 MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Base.explicitTop)
          columnPerm_0281 = targetTop_0281 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0281 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 4 5 7)) 9 := by
  have htop : targetTop_0281 =
      topOfPattern (R := ℤ) (angle6 0 0 3 4 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0281

/-- Explicit target top block for canonical pattern `(0, 0, 3, 4, 6, 6)`. -/
def targetTop_0282 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 0;
     0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0282 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 0;
     1, 0, 1]

def columnPerm_0282 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0282 : BottomDetBound targetTop_0282 9 := by
  have hU : rowTransform_0282.det.natAbs = 1 := by
    have hdet : rowTransform_0282.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0282 hU
  have hcols := hrows.permuteColumns columnPerm_0282
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0282 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0282 = targetTop_0282 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0282 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 4 6 6)) 9 := by
  have htop : targetTop_0282 =
      topOfPattern (R := ℤ) (angle6 0 0 3 4 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0282

/-- Explicit target top block for canonical pattern `(0, 0, 3, 4, 6, 7)`. -/
def targetTop_0283 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 1;
     0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0283 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 0, 1;
     0, 1, 1]

def columnPerm_0283 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 5, 4]
  invFun := ![0, 1, 2, 3, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0283 : BottomDetBound targetTop_0283 9 := by
  have hU : rowTransform_0283.det.natAbs = 1 := by
    have hdet : rowTransform_0283.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Aggregate.bottomBound.transformTopRows rowTransform_0283 hU
  have hcols := hrows.permuteColumns columnPerm_0283
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0283 MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Base.explicitTop)
          columnPerm_0283 = targetTop_0283 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0283 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 4 6 7)) 9 := by
  have htop : targetTop_0283 =
      topOfPattern (R := ℤ) (angle6 0 0 3 4 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0283

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 3, 4, 7, 7)`. -/
def targetTop_0284 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 1, 1;
     0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0284 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0284 :
    TopRowRelation targetTop_0284 relationCoefficients_0284 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0284, relationCoefficients_0284, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0284 : BottomDetBound targetTop_0284 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0284

theorem canonicalBound_0284 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 4 7 7)) 9 := by
  have htop : targetTop_0284 =
      topOfPattern (R := ℤ) (angle6 0 0 3 4 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0284

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 3, 5, 5, 5)`. -/
def targetTop_0285 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0285 : Fin 3 → ℤ :=
  ![1, (-1), (-1)]

theorem topRelation_0285 :
    TopRowRelation targetTop_0285 relationCoefficients_0285 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0285, relationCoefficients_0285, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0285 : BottomDetBound targetTop_0285 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0285

theorem canonicalBound_0285 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 5 5 5)) 9 := by
  have htop : targetTop_0285 =
      topOfPattern (R := ℤ) (angle6 0 0 3 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0285

/-- Explicit target top block for canonical pattern `(0, 0, 3, 5, 5, 6)`. -/
def targetTop_0286 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 0;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0286 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_0286 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0286 : BottomDetBound targetTop_0286 9 := by
  have hU : rowTransform_0286.det.natAbs = 1 := by
    have hdet : rowTransform_0286.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R007.Aggregate.bottomBound.transformTopRows rowTransform_0286 hU
  have hcols := hrows.permuteColumns columnPerm_0286
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0286 MainTheory.Generated.BinaryBetaSixKernel.Representative.R007.Base.explicitTop)
          columnPerm_0286 = targetTop_0286 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0286 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 5 5 6)) 9 := by
  have htop : targetTop_0286 =
      topOfPattern (R := ℤ) (angle6 0 0 3 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0286

/-- Explicit target top block for canonical pattern `(0, 0, 3, 5, 5, 7)`. -/
def targetTop_0287 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0287 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 1, 1;
     1, 0, 1]

def columnPerm_0287 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0287 : BottomDetBound targetTop_0287 9 := by
  have hU : rowTransform_0287.det.natAbs = 1 := by
    have hdet : rowTransform_0287.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0287 hU
  have hcols := hrows.permuteColumns columnPerm_0287
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0287 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0287 = targetTop_0287 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0287 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 5 5 7)) 9 := by
  have htop : targetTop_0287 =
      topOfPattern (R := ℤ) (angle6 0 0 3 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0287

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard017
