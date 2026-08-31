-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard081

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(2, 2, 2, 4, 5, 7)`. -/
def targetTop_1296 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     1, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1296 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 1, 1]

def columnPerm_1296 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1296 : BottomDetBound targetTop_1296 9 := by
  have hU : rowTransform_1296.det.natAbs = 1 := by
    have hdet : rowTransform_1296.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_1296 hU
  have hcols := hrows.permuteColumns columnPerm_1296
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1296 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_1296 = targetTop_1296 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1296 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 4 5 7)) 9 := by
  have htop : targetTop_1296 =
      topOfPattern (R := ℤ) (angle6 2 2 2 4 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1296

/-- Explicit rank-deficient target for canonical pattern `(2, 2, 2, 4, 6, 6)`. -/
def targetTop_1297 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     1, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1297 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_1297 :
    TopRowRelation targetTop_1297 relationCoefficients_1297 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1297, relationCoefficients_1297, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1297 : BottomDetBound targetTop_1297 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1297

theorem canonicalBound_1297 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 4 6 6)) 9 := by
  have htop : targetTop_1297 =
      topOfPattern (R := ℤ) (angle6 2 2 2 4 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1297

/-- Explicit target top block for canonical pattern `(2, 2, 2, 4, 6, 7)`. -/
def targetTop_1298 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     1, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1298 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 1;
     0, 1, 1]

def columnPerm_1298 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1298 : BottomDetBound targetTop_1298 9 := by
  have hU : rowTransform_1298.det.natAbs = 1 := by
    have hdet : rowTransform_1298.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_1298 hU
  have hcols := hrows.permuteColumns columnPerm_1298
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1298 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_1298 = targetTop_1298 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1298 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 4 6 7)) 9 := by
  have htop : targetTop_1298 =
      topOfPattern (R := ℤ) (angle6 2 2 2 4 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1298

/-- Explicit target top block for canonical pattern `(2, 2, 2, 4, 7, 7)`. -/
def targetTop_1299 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     1, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1299 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 0;
     0, 1, 1]

def columnPerm_1299 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1299 : BottomDetBound targetTop_1299 9 := by
  have hU : rowTransform_1299.det.natAbs = 1 := by
    have hdet : rowTransform_1299.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1299 hU
  have hcols := hrows.permuteColumns columnPerm_1299
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1299 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1299 = targetTop_1299 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1299 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 4 7 7)) 9 := by
  have htop : targetTop_1299 =
      topOfPattern (R := ℤ) (angle6 2 2 2 4 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1299

/-- Explicit rank-deficient target for canonical pattern `(2, 2, 2, 5, 5, 5)`. -/
def targetTop_1300 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     1, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1300 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_1300 :
    TopRowRelation targetTop_1300 relationCoefficients_1300 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1300, relationCoefficients_1300, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1300 : BottomDetBound targetTop_1300 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1300

theorem canonicalBound_1300 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 5 5 5)) 9 := by
  have htop : targetTop_1300 =
      topOfPattern (R := ℤ) (angle6 2 2 2 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1300

/-- Explicit target top block for canonical pattern `(2, 2, 2, 5, 5, 6)`. -/
def targetTop_1301 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 0;
     1, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1301 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 1;
     0, 1, 1]

def columnPerm_1301 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1301 : BottomDetBound targetTop_1301 9 := by
  have hU : rowTransform_1301.det.natAbs = 1 := by
    have hdet : rowTransform_1301.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1301 hU
  have hcols := hrows.permuteColumns columnPerm_1301
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1301 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1301 = targetTop_1301 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1301 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 5 5 6)) 9 := by
  have htop : targetTop_1301 =
      topOfPattern (R := ℤ) (angle6 2 2 2 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1301

/-- Explicit rank-deficient target for canonical pattern `(2, 2, 2, 5, 5, 7)`. -/
def targetTop_1302 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     1, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1302 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_1302 :
    TopRowRelation targetTop_1302 relationCoefficients_1302 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1302, relationCoefficients_1302, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1302 : BottomDetBound targetTop_1302 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1302

theorem canonicalBound_1302 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 5 5 7)) 9 := by
  have htop : targetTop_1302 =
      topOfPattern (R := ℤ) (angle6 2 2 2 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1302

/-- Explicit target top block for canonical pattern `(2, 2, 2, 5, 6, 6)`. -/
def targetTop_1303 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 0;
     1, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1303 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, 0;
     0, 1, 1]

def columnPerm_1303 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1303 : BottomDetBound targetTop_1303 9 := by
  have hU : rowTransform_1303.det.natAbs = 1 := by
    have hdet : rowTransform_1303.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1303 hU
  have hcols := hrows.permuteColumns columnPerm_1303
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1303 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1303 = targetTop_1303 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1303 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 5 6 6)) 9 := by
  have htop : targetTop_1303 =
      topOfPattern (R := ℤ) (angle6 2 2 2 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1303

/-- Explicit target top block for canonical pattern `(2, 2, 2, 5, 6, 7)`. -/
def targetTop_1304 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 1;
     1, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1304 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 1;
     0, 1, 1]

def columnPerm_1304 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 5, 4]
  invFun := ![0, 1, 2, 3, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1304 : BottomDetBound targetTop_1304 9 := by
  have hU : rowTransform_1304.det.natAbs = 1 := by
    have hdet : rowTransform_1304.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_1304 hU
  have hcols := hrows.permuteColumns columnPerm_1304
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1304 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_1304 = targetTop_1304 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1304 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 5 6 7)) 9 := by
  have htop : targetTop_1304 =
      topOfPattern (R := ℤ) (angle6 2 2 2 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1304

/-- Explicit rank-deficient target for canonical pattern `(2, 2, 2, 5, 7, 7)`. -/
def targetTop_1305 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     1, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1305 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_1305 :
    TopRowRelation targetTop_1305 relationCoefficients_1305 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1305, relationCoefficients_1305, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1305 : BottomDetBound targetTop_1305 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1305

theorem canonicalBound_1305 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 5 7 7)) 9 := by
  have htop : targetTop_1305 =
      topOfPattern (R := ℤ) (angle6 2 2 2 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1305

/-- Explicit rank-deficient target for canonical pattern `(2, 2, 2, 6, 6, 6)`. -/
def targetTop_1306 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1306 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_1306 :
    TopRowRelation targetTop_1306 relationCoefficients_1306 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1306, relationCoefficients_1306, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1306 : BottomDetBound targetTop_1306 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1306

theorem canonicalBound_1306 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 6 6 6)) 9 := by
  have htop : targetTop_1306 =
      topOfPattern (R := ℤ) (angle6 2 2 2 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1306

/-- Explicit target top block for canonical pattern `(2, 2, 2, 6, 6, 7)`. -/
def targetTop_1307 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1307 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, 1;
     0, 1, 1]

def columnPerm_1307 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1307 : BottomDetBound targetTop_1307 9 := by
  have hU : rowTransform_1307.det.natAbs = 1 := by
    have hdet : rowTransform_1307.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1307 hU
  have hcols := hrows.permuteColumns columnPerm_1307
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1307 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1307 = targetTop_1307 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1307 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 6 6 7)) 9 := by
  have htop : targetTop_1307 =
      topOfPattern (R := ℤ) (angle6 2 2 2 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1307

/-- Explicit target top block for canonical pattern `(2, 2, 2, 6, 7, 7)`. -/
def targetTop_1308 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1308 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 1;
     0, 1, 1]

def columnPerm_1308 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1308 : BottomDetBound targetTop_1308 9 := by
  have hU : rowTransform_1308.det.natAbs = 1 := by
    have hdet : rowTransform_1308.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1308 hU
  have hcols := hrows.permuteColumns columnPerm_1308
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1308 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1308 = targetTop_1308 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1308 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 6 7 7)) 9 := by
  have htop : targetTop_1308 =
      topOfPattern (R := ℤ) (angle6 2 2 2 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1308

/-- Explicit rank-deficient target for canonical pattern `(2, 2, 2, 7, 7, 7)`. -/
def targetTop_1309 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1309 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_1309 :
    TopRowRelation targetTop_1309 relationCoefficients_1309 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1309, relationCoefficients_1309, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1309 : BottomDetBound targetTop_1309 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1309

theorem canonicalBound_1309 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 7 7 7)) 9 := by
  have htop : targetTop_1309 =
      topOfPattern (R := ℤ) (angle6 2 2 2 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1309

/-- Explicit rank-deficient target for canonical pattern `(2, 2, 3, 3, 3, 3)`. -/
def targetTop_1310 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1310 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_1310 :
    TopRowRelation targetTop_1310 relationCoefficients_1310 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1310, relationCoefficients_1310, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1310 : BottomDetBound targetTop_1310 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1310

theorem canonicalBound_1310 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 3 3 3)) 9 := by
  have htop : targetTop_1310 =
      topOfPattern (R := ℤ) (angle6 2 2 3 3 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1310

/-- Explicit target top block for canonical pattern `(2, 2, 3, 3, 3, 4)`. -/
def targetTop_1311 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 0;
     1, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1311 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, 0;
     0, 0, 1]

def columnPerm_1311 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1311 : BottomDetBound targetTop_1311 9 := by
  have hU : rowTransform_1311.det.natAbs = 1 := by
    have hdet : rowTransform_1311.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1311 hU
  have hcols := hrows.permuteColumns columnPerm_1311
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1311 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1311 = targetTop_1311 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1311 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 3 3 4)) 9 := by
  have htop : targetTop_1311 =
      topOfPattern (R := ℤ) (angle6 2 2 3 3 3 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1311

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard081
