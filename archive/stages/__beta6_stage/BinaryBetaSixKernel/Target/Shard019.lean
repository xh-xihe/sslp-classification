-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R005.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard019

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 4, 4, 7, 7)`. -/
def targetTop_0304 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0304 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0304 :
    TopRowRelation targetTop_0304 relationCoefficients_0304 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0304, relationCoefficients_0304, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0304 : BottomDetBound targetTop_0304 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0304

theorem canonicalBound_0304 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 4 4 7 7)) 9 := by
  have htop : targetTop_0304 =
      topOfPattern (R := ℤ) (angle6 0 0 4 4 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0304

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 4, 5, 5, 5)`. -/
def targetTop_0305 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0305 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0305 :
    TopRowRelation targetTop_0305 relationCoefficients_0305 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0305, relationCoefficients_0305, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0305 : BottomDetBound targetTop_0305 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0305

theorem canonicalBound_0305 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 4 5 5 5)) 9 := by
  have htop : targetTop_0305 =
      topOfPattern (R := ℤ) (angle6 0 0 4 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0305

/-- Explicit target top block for canonical pattern `(0, 0, 4, 5, 5, 6)`. -/
def targetTop_0306 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0306 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     1, 1, 1]

def columnPerm_0306 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0306 : BottomDetBound targetTop_0306 9 := by
  have hU : rowTransform_0306.det.natAbs = 1 := by
    have hdet : rowTransform_0306.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0306 hU
  have hcols := hrows.permuteColumns columnPerm_0306
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0306 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0306 = targetTop_0306 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0306 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 4 5 5 6)) 9 := by
  have htop : targetTop_0306 =
      topOfPattern (R := ℤ) (angle6 0 0 4 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0306

/-- Explicit target top block for canonical pattern `(0, 0, 4, 5, 5, 7)`. -/
def targetTop_0307 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0307 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 0, 1;
     1, 1, 1]

def columnPerm_0307 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0307 : BottomDetBound targetTop_0307 9 := by
  have hU : rowTransform_0307.det.natAbs = 1 := by
    have hdet : rowTransform_0307.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0307 hU
  have hcols := hrows.permuteColumns columnPerm_0307
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0307 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0307 = targetTop_0307 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0307 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 4 5 5 7)) 9 := by
  have htop : targetTop_0307 =
      topOfPattern (R := ℤ) (angle6 0 0 4 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0307

/-- Explicit target top block for canonical pattern `(0, 0, 4, 5, 6, 6)`. -/
def targetTop_0308 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0308 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     1, 1, 1]

def columnPerm_0308 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0308 : BottomDetBound targetTop_0308 9 := by
  have hU : rowTransform_0308.det.natAbs = 1 := by
    have hdet : rowTransform_0308.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0308 hU
  have hcols := hrows.permuteColumns columnPerm_0308
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0308 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0308 = targetTop_0308 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0308 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 4 5 6 6)) 9 := by
  have htop : targetTop_0308 =
      topOfPattern (R := ℤ) (angle6 0 0 4 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0308

/-- Explicit target top block for canonical pattern `(0, 0, 4, 5, 6, 7)`. -/
def targetTop_0309 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0309 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 1, 0]

def columnPerm_0309 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0309 : BottomDetBound targetTop_0309 9 := by
  have hU : rowTransform_0309.det.natAbs = 1 := by
    have hdet : rowTransform_0309.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R005.Aggregate.bottomBound.transformTopRows rowTransform_0309 hU
  have hcols := hrows.permuteColumns columnPerm_0309
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0309 MainTheory.Generated.BinaryBetaSixKernel.Representative.R005.Base.explicitTop)
          columnPerm_0309 = targetTop_0309 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0309 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 4 5 6 7)) 9 := by
  have htop : targetTop_0309 =
      topOfPattern (R := ℤ) (angle6 0 0 4 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0309

/-- Explicit target top block for canonical pattern `(0, 0, 4, 5, 7, 7)`. -/
def targetTop_0310 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0310 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 0, 0;
     1, 1, 1]

def columnPerm_0310 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0310 : BottomDetBound targetTop_0310 9 := by
  have hU : rowTransform_0310.det.natAbs = 1 := by
    have hdet : rowTransform_0310.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0310 hU
  have hcols := hrows.permuteColumns columnPerm_0310
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0310 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0310 = targetTop_0310 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0310 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 4 5 7 7)) 9 := by
  have htop : targetTop_0310 =
      topOfPattern (R := ℤ) (angle6 0 0 4 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0310

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 4, 6, 6, 6)`. -/
def targetTop_0311 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0311 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0311 :
    TopRowRelation targetTop_0311 relationCoefficients_0311 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0311, relationCoefficients_0311, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0311 : BottomDetBound targetTop_0311 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0311

theorem canonicalBound_0311 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 4 6 6 6)) 9 := by
  have htop : targetTop_0311 =
      topOfPattern (R := ℤ) (angle6 0 0 4 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0311

/-- Explicit target top block for canonical pattern `(0, 0, 4, 6, 6, 7)`. -/
def targetTop_0312 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0312 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 1;
     1, 1, 1]

def columnPerm_0312 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0312 : BottomDetBound targetTop_0312 9 := by
  have hU : rowTransform_0312.det.natAbs = 1 := by
    have hdet : rowTransform_0312.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0312 hU
  have hcols := hrows.permuteColumns columnPerm_0312
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0312 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0312 = targetTop_0312 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0312 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 4 6 6 7)) 9 := by
  have htop : targetTop_0312 =
      topOfPattern (R := ℤ) (angle6 0 0 4 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0312

/-- Explicit target top block for canonical pattern `(0, 0, 4, 6, 7, 7)`. -/
def targetTop_0313 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0313 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 0, 1;
     1, 1, 1]

def columnPerm_0313 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0313 : BottomDetBound targetTop_0313 9 := by
  have hU : rowTransform_0313.det.natAbs = 1 := by
    have hdet : rowTransform_0313.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0313 hU
  have hcols := hrows.permuteColumns columnPerm_0313
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0313 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0313 = targetTop_0313 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0313 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 4 6 7 7)) 9 := by
  have htop : targetTop_0313 =
      topOfPattern (R := ℤ) (angle6 0 0 4 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0313

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 4, 7, 7, 7)`. -/
def targetTop_0314 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0314 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0314 :
    TopRowRelation targetTop_0314 relationCoefficients_0314 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0314, relationCoefficients_0314, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0314 : BottomDetBound targetTop_0314 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0314

theorem canonicalBound_0314 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 4 7 7 7)) 9 := by
  have htop : targetTop_0314 =
      topOfPattern (R := ℤ) (angle6 0 0 4 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0314

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 5, 5, 5, 5)`. -/
def targetTop_0315 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0315 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0315 :
    TopRowRelation targetTop_0315 relationCoefficients_0315 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0315, relationCoefficients_0315, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0315 : BottomDetBound targetTop_0315 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0315

theorem canonicalBound_0315 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 5 5 5 5)) 9 := by
  have htop : targetTop_0315 =
      topOfPattern (R := ℤ) (angle6 0 0 5 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0315

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 5, 5, 5, 6)`. -/
def targetTop_0316 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0316 : Fin 3 → ℤ :=
  ![1, 1, (-1)]

theorem topRelation_0316 :
    TopRowRelation targetTop_0316 relationCoefficients_0316 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0316, relationCoefficients_0316, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0316 : BottomDetBound targetTop_0316 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0316

theorem canonicalBound_0316 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 5 5 5 6)) 9 := by
  have htop : targetTop_0316 =
      topOfPattern (R := ℤ) (angle6 0 0 5 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0316

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 5, 5, 5, 7)`. -/
def targetTop_0317 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0317 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0317 :
    TopRowRelation targetTop_0317 relationCoefficients_0317 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0317, relationCoefficients_0317, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0317 : BottomDetBound targetTop_0317 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0317

theorem canonicalBound_0317 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 5 5 5 7)) 9 := by
  have htop : targetTop_0317 =
      topOfPattern (R := ℤ) (angle6 0 0 5 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0317

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 5, 5, 6, 6)`. -/
def targetTop_0318 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0318 : Fin 3 → ℤ :=
  ![1, 1, (-1)]

theorem topRelation_0318 :
    TopRowRelation targetTop_0318 relationCoefficients_0318 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0318, relationCoefficients_0318, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0318 : BottomDetBound targetTop_0318 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0318

theorem canonicalBound_0318 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 5 5 6 6)) 9 := by
  have htop : targetTop_0318 =
      topOfPattern (R := ℤ) (angle6 0 0 5 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0318

/-- Explicit target top block for canonical pattern `(0, 0, 5, 5, 6, 7)`. -/
def targetTop_0319 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0319 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 1;
     1, 1, 1]

def columnPerm_0319 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0319 : BottomDetBound targetTop_0319 9 := by
  have hU : rowTransform_0319.det.natAbs = 1 := by
    have hdet : rowTransform_0319.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0319 hU
  have hcols := hrows.permuteColumns columnPerm_0319
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0319 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0319 = targetTop_0319 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0319 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 5 5 6 7)) 9 := by
  have htop : targetTop_0319 =
      topOfPattern (R := ℤ) (angle6 0 0 5 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0319

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard019
