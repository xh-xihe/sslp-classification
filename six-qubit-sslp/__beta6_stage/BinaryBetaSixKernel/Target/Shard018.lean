-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R007.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R008.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard018

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(0, 0, 3, 5, 6, 6)`. -/
def targetTop_0288 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 0;
     0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0288 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_0288 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0288 : BottomDetBound targetTop_0288 9 := by
  have hU : rowTransform_0288.det.natAbs = 1 := by
    have hdet : rowTransform_0288.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R007.Aggregate.bottomBound.transformTopRows rowTransform_0288 hU
  have hcols := hrows.permuteColumns columnPerm_0288
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0288 MainTheory.Generated.BinaryBetaSixKernel.Representative.R007.Base.explicitTop)
          columnPerm_0288 = targetTop_0288 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0288 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 5 6 6)) 9 := by
  have htop : targetTop_0288 =
      topOfPattern (R := ℤ) (angle6 0 0 3 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0288

/-- Explicit target top block for canonical pattern `(0, 0, 3, 5, 6, 7)`. -/
def targetTop_0289 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 1;
     0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0289 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0289 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0289 : BottomDetBound targetTop_0289 9 := by
  have hU : rowTransform_0289.det.natAbs = 1 := by
    have hdet : rowTransform_0289.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R008.Aggregate.bottomBound.transformTopRows rowTransform_0289 hU
  have hcols := hrows.permuteColumns columnPerm_0289
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0289 MainTheory.Generated.BinaryBetaSixKernel.Representative.R008.Base.explicitTop)
          columnPerm_0289 = targetTop_0289 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0289 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 5 6 7)) 9 := by
  have htop : targetTop_0289 =
      topOfPattern (R := ℤ) (angle6 0 0 3 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0289

/-- Explicit target top block for canonical pattern `(0, 0, 3, 5, 7, 7)`. -/
def targetTop_0290 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0290 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     1, 1, 0;
     1, 0, 1]

def columnPerm_0290 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0290 : BottomDetBound targetTop_0290 9 := by
  have hU : rowTransform_0290.det.natAbs = 1 := by
    have hdet : rowTransform_0290.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0290 hU
  have hcols := hrows.permuteColumns columnPerm_0290
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0290 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0290 = targetTop_0290 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0290 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 5 7 7)) 9 := by
  have htop : targetTop_0290 =
      topOfPattern (R := ℤ) (angle6 0 0 3 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0290

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 3, 6, 6, 6)`. -/
def targetTop_0291 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 0;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0291 : Fin 3 → ℤ :=
  ![1, (-1), 1]

theorem topRelation_0291 :
    TopRowRelation targetTop_0291 relationCoefficients_0291 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0291, relationCoefficients_0291, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0291 : BottomDetBound targetTop_0291 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0291

theorem canonicalBound_0291 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 6 6 6)) 9 := by
  have htop : targetTop_0291 =
      topOfPattern (R := ℤ) (angle6 0 0 3 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0291

/-- Explicit target top block for canonical pattern `(0, 0, 3, 6, 6, 7)`. -/
def targetTop_0292 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0292 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 1, 1;
     1, 0, 1]

def columnPerm_0292 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0292 : BottomDetBound targetTop_0292 9 := by
  have hU : rowTransform_0292.det.natAbs = 1 := by
    have hdet : rowTransform_0292.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0292 hU
  have hcols := hrows.permuteColumns columnPerm_0292
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0292 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0292 = targetTop_0292 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0292 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 6 6 7)) 9 := by
  have htop : targetTop_0292 =
      topOfPattern (R := ℤ) (angle6 0 0 3 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0292

/-- Explicit target top block for canonical pattern `(0, 0, 3, 6, 7, 7)`. -/
def targetTop_0293 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0293 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 1, 1;
     1, 0, 1]

def columnPerm_0293 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0293 : BottomDetBound targetTop_0293 9 := by
  have hU : rowTransform_0293.det.natAbs = 1 := by
    have hdet : rowTransform_0293.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0293 hU
  have hcols := hrows.permuteColumns columnPerm_0293
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0293 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0293 = targetTop_0293 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0293 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 6 7 7)) 9 := by
  have htop : targetTop_0293 =
      topOfPattern (R := ℤ) (angle6 0 0 3 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0293

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 3, 7, 7, 7)`. -/
def targetTop_0294 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0294 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0294 :
    TopRowRelation targetTop_0294 relationCoefficients_0294 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0294, relationCoefficients_0294, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0294 : BottomDetBound targetTop_0294 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0294

theorem canonicalBound_0294 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 7 7 7)) 9 := by
  have htop : targetTop_0294 =
      topOfPattern (R := ℤ) (angle6 0 0 3 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0294

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 4, 4, 4, 4)`. -/
def targetTop_0295 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0295 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0295 :
    TopRowRelation targetTop_0295 relationCoefficients_0295 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0295, relationCoefficients_0295, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0295 : BottomDetBound targetTop_0295 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0295

theorem canonicalBound_0295 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 4 4 4 4)) 9 := by
  have htop : targetTop_0295 =
      topOfPattern (R := ℤ) (angle6 0 0 4 4 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0295

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 4, 4, 4, 5)`. -/
def targetTop_0296 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0296 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0296 :
    TopRowRelation targetTop_0296 relationCoefficients_0296 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0296, relationCoefficients_0296, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0296 : BottomDetBound targetTop_0296 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0296

theorem canonicalBound_0296 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 4 4 4 5)) 9 := by
  have htop : targetTop_0296 =
      topOfPattern (R := ℤ) (angle6 0 0 4 4 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0296

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 4, 4, 4, 6)`. -/
def targetTop_0297 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0297 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0297 :
    TopRowRelation targetTop_0297 relationCoefficients_0297 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0297, relationCoefficients_0297, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0297 : BottomDetBound targetTop_0297 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0297

theorem canonicalBound_0297 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 4 4 4 6)) 9 := by
  have htop : targetTop_0297 =
      topOfPattern (R := ℤ) (angle6 0 0 4 4 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0297

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 4, 4, 4, 7)`. -/
def targetTop_0298 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0298 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0298 :
    TopRowRelation targetTop_0298 relationCoefficients_0298 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0298, relationCoefficients_0298, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0298 : BottomDetBound targetTop_0298 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0298

theorem canonicalBound_0298 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 4 4 4 7)) 9 := by
  have htop : targetTop_0298 =
      topOfPattern (R := ℤ) (angle6 0 0 4 4 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0298

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 4, 4, 5, 5)`. -/
def targetTop_0299 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0299 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0299 :
    TopRowRelation targetTop_0299 relationCoefficients_0299 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0299, relationCoefficients_0299, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0299 : BottomDetBound targetTop_0299 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0299

theorem canonicalBound_0299 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 4 4 5 5)) 9 := by
  have htop : targetTop_0299 =
      topOfPattern (R := ℤ) (angle6 0 0 4 4 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0299

/-- Explicit target top block for canonical pattern `(0, 0, 4, 4, 5, 6)`. -/
def targetTop_0300 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0300 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 1, 1]

def columnPerm_0300 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0300 : BottomDetBound targetTop_0300 9 := by
  have hU : rowTransform_0300.det.natAbs = 1 := by
    have hdet : rowTransform_0300.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0300 hU
  have hcols := hrows.permuteColumns columnPerm_0300
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0300 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0300 = targetTop_0300 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0300 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 4 4 5 6)) 9 := by
  have htop : targetTop_0300 =
      topOfPattern (R := ℤ) (angle6 0 0 4 4 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0300

/-- Explicit target top block for canonical pattern `(0, 0, 4, 4, 5, 7)`. -/
def targetTop_0301 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0301 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 0, 1;
     1, 1, 1]

def columnPerm_0301 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0301 : BottomDetBound targetTop_0301 9 := by
  have hU : rowTransform_0301.det.natAbs = 1 := by
    have hdet : rowTransform_0301.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0301 hU
  have hcols := hrows.permuteColumns columnPerm_0301
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0301 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0301 = targetTop_0301 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0301 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 4 4 5 7)) 9 := by
  have htop : targetTop_0301 =
      topOfPattern (R := ℤ) (angle6 0 0 4 4 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0301

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 4, 4, 6, 6)`. -/
def targetTop_0302 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0302 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0302 :
    TopRowRelation targetTop_0302 relationCoefficients_0302 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0302, relationCoefficients_0302, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0302 : BottomDetBound targetTop_0302 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0302

theorem canonicalBound_0302 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 4 4 6 6)) 9 := by
  have htop : targetTop_0302 =
      topOfPattern (R := ℤ) (angle6 0 0 4 4 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0302

/-- Explicit target top block for canonical pattern `(0, 0, 4, 4, 6, 7)`. -/
def targetTop_0303 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0303 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 1;
     1, 1, 1]

def columnPerm_0303 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0303 : BottomDetBound targetTop_0303 9 := by
  have hU : rowTransform_0303.det.natAbs = 1 := by
    have hdet : rowTransform_0303.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0303 hU
  have hcols := hrows.permuteColumns columnPerm_0303
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0303 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0303 = targetTop_0303 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0303 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 4 4 6 7)) 9 := by
  have htop : targetTop_0303 =
      topOfPattern (R := ℤ) (angle6 0 0 4 4 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0303

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard018
