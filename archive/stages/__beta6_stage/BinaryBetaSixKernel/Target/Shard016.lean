-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R007.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard016

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 2, 6, 6, 6)`. -/
def targetTop_0256 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0256 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0256 :
    TopRowRelation targetTop_0256 relationCoefficients_0256 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0256, relationCoefficients_0256, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0256 : BottomDetBound targetTop_0256 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0256

theorem canonicalBound_0256 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 6 6 6)) 9 := by
  have htop : targetTop_0256 =
      topOfPattern (R := ℤ) (angle6 0 0 2 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0256

/-- Explicit target top block for canonical pattern `(0, 0, 2, 6, 6, 7)`. -/
def targetTop_0257 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0257 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, 1;
     1, 0, 1]

def columnPerm_0257 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0257 : BottomDetBound targetTop_0257 9 := by
  have hU : rowTransform_0257.det.natAbs = 1 := by
    have hdet : rowTransform_0257.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0257 hU
  have hcols := hrows.permuteColumns columnPerm_0257
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0257 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0257 = targetTop_0257 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0257 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 6 6 7)) 9 := by
  have htop : targetTop_0257 =
      topOfPattern (R := ℤ) (angle6 0 0 2 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0257

/-- Explicit target top block for canonical pattern `(0, 0, 2, 6, 7, 7)`. -/
def targetTop_0258 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0258 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, 1;
     1, 0, 1]

def columnPerm_0258 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0258 : BottomDetBound targetTop_0258 9 := by
  have hU : rowTransform_0258.det.natAbs = 1 := by
    have hdet : rowTransform_0258.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0258 hU
  have hcols := hrows.permuteColumns columnPerm_0258
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0258 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0258 = targetTop_0258 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0258 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 6 7 7)) 9 := by
  have htop : targetTop_0258 =
      topOfPattern (R := ℤ) (angle6 0 0 2 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0258

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 2, 7, 7, 7)`. -/
def targetTop_0259 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0259 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0259 :
    TopRowRelation targetTop_0259 relationCoefficients_0259 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0259, relationCoefficients_0259, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0259 : BottomDetBound targetTop_0259 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0259

theorem canonicalBound_0259 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 7 7 7)) 9 := by
  have htop : targetTop_0259 =
      topOfPattern (R := ℤ) (angle6 0 0 2 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0259

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 3, 3, 3, 3)`. -/
def targetTop_0260 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0260 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0260 :
    TopRowRelation targetTop_0260 relationCoefficients_0260 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0260, relationCoefficients_0260, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0260 : BottomDetBound targetTop_0260 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0260

theorem canonicalBound_0260 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 3 3 3)) 9 := by
  have htop : targetTop_0260 =
      topOfPattern (R := ℤ) (angle6 0 0 3 3 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0260

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 3, 3, 3, 4)`. -/
def targetTop_0261 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 0;
     0, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0261 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0261 :
    TopRowRelation targetTop_0261 relationCoefficients_0261 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0261, relationCoefficients_0261, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0261 : BottomDetBound targetTop_0261 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0261

theorem canonicalBound_0261 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 3 3 4)) 9 := by
  have htop : targetTop_0261 =
      topOfPattern (R := ℤ) (angle6 0 0 3 3 3 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0261

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 3, 3, 3, 5)`. -/
def targetTop_0262 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0262 : Fin 3 → ℤ :=
  ![1, (-1), (-1)]

theorem topRelation_0262 :
    TopRowRelation targetTop_0262 relationCoefficients_0262 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0262, relationCoefficients_0262, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0262 : BottomDetBound targetTop_0262 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0262

theorem canonicalBound_0262 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 3 3 5)) 9 := by
  have htop : targetTop_0262 =
      topOfPattern (R := ℤ) (angle6 0 0 3 3 3 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0262

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 3, 3, 3, 6)`. -/
def targetTop_0263 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 0;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0263 : Fin 3 → ℤ :=
  ![1, (-1), 1]

theorem topRelation_0263 :
    TopRowRelation targetTop_0263 relationCoefficients_0263 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0263, relationCoefficients_0263, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0263 : BottomDetBound targetTop_0263 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0263

theorem canonicalBound_0263 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 3 3 6)) 9 := by
  have htop : targetTop_0263 =
      topOfPattern (R := ℤ) (angle6 0 0 3 3 3 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0263

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 3, 3, 3, 7)`. -/
def targetTop_0264 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0264 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0264 :
    TopRowRelation targetTop_0264 relationCoefficients_0264 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0264, relationCoefficients_0264, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0264 : BottomDetBound targetTop_0264 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0264

theorem canonicalBound_0264 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 3 3 7)) 9 := by
  have htop : targetTop_0264 =
      topOfPattern (R := ℤ) (angle6 0 0 3 3 3 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0264

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 3, 3, 4, 4)`. -/
def targetTop_0265 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 0;
     0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0265 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0265 :
    TopRowRelation targetTop_0265 relationCoefficients_0265 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0265, relationCoefficients_0265, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0265 : BottomDetBound targetTop_0265 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0265

theorem canonicalBound_0265 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 3 4 4)) 9 := by
  have htop : targetTop_0265 =
      topOfPattern (R := ℤ) (angle6 0 0 3 3 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0265

/-- Explicit target top block for canonical pattern `(0, 0, 3, 3, 4, 5)`. -/
def targetTop_0266 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 1;
     0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0266 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 0, 0;
     0, 1, 1]

def columnPerm_0266 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0266 : BottomDetBound targetTop_0266 9 := by
  have hU : rowTransform_0266.det.natAbs = 1 := by
    have hdet : rowTransform_0266.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0266 hU
  have hcols := hrows.permuteColumns columnPerm_0266
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0266 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0266 = targetTop_0266 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0266 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 3 4 5)) 9 := by
  have htop : targetTop_0266 =
      topOfPattern (R := ℤ) (angle6 0 0 3 3 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0266

/-- Explicit target top block for canonical pattern `(0, 0, 3, 3, 4, 6)`. -/
def targetTop_0267 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 0;
     0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0267 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 0, 1;
     0, 1, 1]

def columnPerm_0267 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0267 : BottomDetBound targetTop_0267 9 := by
  have hU : rowTransform_0267.det.natAbs = 1 := by
    have hdet : rowTransform_0267.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0267 hU
  have hcols := hrows.permuteColumns columnPerm_0267
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0267 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0267 = targetTop_0267 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0267 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 3 4 6)) 9 := by
  have htop : targetTop_0267 =
      topOfPattern (R := ℤ) (angle6 0 0 3 3 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0267

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 3, 3, 4, 7)`. -/
def targetTop_0268 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 1;
     0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0268 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0268 :
    TopRowRelation targetTop_0268 relationCoefficients_0268 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0268, relationCoefficients_0268, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0268 : BottomDetBound targetTop_0268 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0268

theorem canonicalBound_0268 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 3 4 7)) 9 := by
  have htop : targetTop_0268 =
      topOfPattern (R := ℤ) (angle6 0 0 3 3 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0268

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 3, 3, 5, 5)`. -/
def targetTop_0269 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0269 : Fin 3 → ℤ :=
  ![1, (-1), (-1)]

theorem topRelation_0269 :
    TopRowRelation targetTop_0269 relationCoefficients_0269 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0269, relationCoefficients_0269, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0269 : BottomDetBound targetTop_0269 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0269

theorem canonicalBound_0269 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 3 5 5)) 9 := by
  have htop : targetTop_0269 =
      topOfPattern (R := ℤ) (angle6 0 0 3 3 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0269

/-- Explicit target top block for canonical pattern `(0, 0, 3, 3, 5, 6)`. -/
def targetTop_0270 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 0;
     0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0270 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0270 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0270 : BottomDetBound targetTop_0270 9 := by
  have hU : rowTransform_0270.det.natAbs = 1 := by
    have hdet : rowTransform_0270.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R007.Aggregate.bottomBound.transformTopRows rowTransform_0270 hU
  have hcols := hrows.permuteColumns columnPerm_0270
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0270 MainTheory.Generated.BinaryBetaSixKernel.Representative.R007.Base.explicitTop)
          columnPerm_0270 = targetTop_0270 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0270 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 3 5 6)) 9 := by
  have htop : targetTop_0270 =
      topOfPattern (R := ℤ) (angle6 0 0 3 3 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0270

/-- Explicit target top block for canonical pattern `(0, 0, 3, 3, 5, 7)`. -/
def targetTop_0271 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0271 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     1, 0, 1;
     0, 1, 1]

def columnPerm_0271 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0271 : BottomDetBound targetTop_0271 9 := by
  have hU : rowTransform_0271.det.natAbs = 1 := by
    have hdet : rowTransform_0271.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0271 hU
  have hcols := hrows.permuteColumns columnPerm_0271
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0271 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0271 = targetTop_0271 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0271 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 3 5 7)) 9 := by
  have htop : targetTop_0271 =
      topOfPattern (R := ℤ) (angle6 0 0 3 3 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0271

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard016
