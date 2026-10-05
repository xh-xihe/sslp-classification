-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard079

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(2, 2, 2, 2, 3, 7)`. -/
def targetTop_1264 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1264 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 1, 1;
     0, 0, 1]

def columnPerm_1264 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1264 : BottomDetBound targetTop_1264 9 := by
  have hU : rowTransform_1264.det.natAbs = 1 := by
    have hdet : rowTransform_1264.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1264 hU
  have hcols := hrows.permuteColumns columnPerm_1264
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1264 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1264 = targetTop_1264 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1264 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 2 3 7)) 9 := by
  have htop : targetTop_1264 =
      topOfPattern (R := ℤ) (angle6 2 2 2 2 3 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1264

/-- Explicit rank-deficient target for canonical pattern `(2, 2, 2, 2, 4, 4)`. -/
def targetTop_1265 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     1, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1265 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_1265 :
    TopRowRelation targetTop_1265 relationCoefficients_1265 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1265, relationCoefficients_1265, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1265 : BottomDetBound targetTop_1265 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1265

theorem canonicalBound_1265 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 2 4 4)) 9 := by
  have htop : targetTop_1265 =
      topOfPattern (R := ℤ) (angle6 2 2 2 2 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1265

/-- Explicit target top block for canonical pattern `(2, 2, 2, 2, 4, 5)`. -/
def targetTop_1266 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     1, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1266 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 1]

def columnPerm_1266 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1266 : BottomDetBound targetTop_1266 9 := by
  have hU : rowTransform_1266.det.natAbs = 1 := by
    have hdet : rowTransform_1266.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1266 hU
  have hcols := hrows.permuteColumns columnPerm_1266
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1266 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1266 = targetTop_1266 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1266 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 2 4 5)) 9 := by
  have htop : targetTop_1266 =
      topOfPattern (R := ℤ) (angle6 2 2 2 2 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1266

/-- Explicit rank-deficient target for canonical pattern `(2, 2, 2, 2, 4, 6)`. -/
def targetTop_1267 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     1, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1267 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_1267 :
    TopRowRelation targetTop_1267 relationCoefficients_1267 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1267, relationCoefficients_1267, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1267 : BottomDetBound targetTop_1267 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1267

theorem canonicalBound_1267 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 2 4 6)) 9 := by
  have htop : targetTop_1267 =
      topOfPattern (R := ℤ) (angle6 2 2 2 2 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1267

/-- Explicit target top block for canonical pattern `(2, 2, 2, 2, 4, 7)`. -/
def targetTop_1268 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     1, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1268 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 1;
     0, 1, 1]

def columnPerm_1268 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1268 : BottomDetBound targetTop_1268 9 := by
  have hU : rowTransform_1268.det.natAbs = 1 := by
    have hdet : rowTransform_1268.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1268 hU
  have hcols := hrows.permuteColumns columnPerm_1268
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1268 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1268 = targetTop_1268 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1268 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 2 4 7)) 9 := by
  have htop : targetTop_1268 =
      topOfPattern (R := ℤ) (angle6 2 2 2 2 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1268

/-- Explicit rank-deficient target for canonical pattern `(2, 2, 2, 2, 5, 5)`. -/
def targetTop_1269 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     1, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1269 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_1269 :
    TopRowRelation targetTop_1269 relationCoefficients_1269 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1269, relationCoefficients_1269, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1269 : BottomDetBound targetTop_1269 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1269

theorem canonicalBound_1269 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 2 5 5)) 9 := by
  have htop : targetTop_1269 =
      topOfPattern (R := ℤ) (angle6 2 2 2 2 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1269

/-- Explicit target top block for canonical pattern `(2, 2, 2, 2, 5, 6)`. -/
def targetTop_1270 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 0;
     1, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1270 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 1;
     0, 1, 1]

def columnPerm_1270 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1270 : BottomDetBound targetTop_1270 9 := by
  have hU : rowTransform_1270.det.natAbs = 1 := by
    have hdet : rowTransform_1270.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1270 hU
  have hcols := hrows.permuteColumns columnPerm_1270
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1270 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1270 = targetTop_1270 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1270 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 2 5 6)) 9 := by
  have htop : targetTop_1270 =
      topOfPattern (R := ℤ) (angle6 2 2 2 2 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1270

/-- Explicit rank-deficient target for canonical pattern `(2, 2, 2, 2, 5, 7)`. -/
def targetTop_1271 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     1, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1271 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_1271 :
    TopRowRelation targetTop_1271 relationCoefficients_1271 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1271, relationCoefficients_1271, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1271 : BottomDetBound targetTop_1271 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1271

theorem canonicalBound_1271 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 2 5 7)) 9 := by
  have htop : targetTop_1271 =
      topOfPattern (R := ℤ) (angle6 2 2 2 2 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1271

/-- Explicit rank-deficient target for canonical pattern `(2, 2, 2, 2, 6, 6)`. -/
def targetTop_1272 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1272 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_1272 :
    TopRowRelation targetTop_1272 relationCoefficients_1272 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1272, relationCoefficients_1272, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1272 : BottomDetBound targetTop_1272 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1272

theorem canonicalBound_1272 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 2 6 6)) 9 := by
  have htop : targetTop_1272 =
      topOfPattern (R := ℤ) (angle6 2 2 2 2 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1272

/-- Explicit target top block for canonical pattern `(2, 2, 2, 2, 6, 7)`. -/
def targetTop_1273 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1273 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, 1;
     0, 1, 1]

def columnPerm_1273 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1273 : BottomDetBound targetTop_1273 9 := by
  have hU : rowTransform_1273.det.natAbs = 1 := by
    have hdet : rowTransform_1273.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1273 hU
  have hcols := hrows.permuteColumns columnPerm_1273
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1273 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1273 = targetTop_1273 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1273 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 2 6 7)) 9 := by
  have htop : targetTop_1273 =
      topOfPattern (R := ℤ) (angle6 2 2 2 2 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1273

/-- Explicit rank-deficient target for canonical pattern `(2, 2, 2, 2, 7, 7)`. -/
def targetTop_1274 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1274 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_1274 :
    TopRowRelation targetTop_1274 relationCoefficients_1274 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1274, relationCoefficients_1274, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1274 : BottomDetBound targetTop_1274 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1274

theorem canonicalBound_1274 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 2 7 7)) 9 := by
  have htop : targetTop_1274 =
      topOfPattern (R := ℤ) (angle6 2 2 2 2 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1274

/-- Explicit rank-deficient target for canonical pattern `(2, 2, 2, 3, 3, 3)`. -/
def targetTop_1275 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1275 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_1275 :
    TopRowRelation targetTop_1275 relationCoefficients_1275 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1275, relationCoefficients_1275, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1275 : BottomDetBound targetTop_1275 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1275

theorem canonicalBound_1275 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 3 3 3)) 9 := by
  have htop : targetTop_1275 =
      topOfPattern (R := ℤ) (angle6 2 2 2 3 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1275

/-- Explicit target top block for canonical pattern `(2, 2, 2, 3, 3, 4)`. -/
def targetTop_1276 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 0;
     1, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1276 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 0;
     0, 0, 1]

def columnPerm_1276 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1276 : BottomDetBound targetTop_1276 9 := by
  have hU : rowTransform_1276.det.natAbs = 1 := by
    have hdet : rowTransform_1276.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1276 hU
  have hcols := hrows.permuteColumns columnPerm_1276
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1276 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1276 = targetTop_1276 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1276 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 3 3 4)) 9 := by
  have htop : targetTop_1276 =
      topOfPattern (R := ℤ) (angle6 2 2 2 3 3 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1276

/-- Explicit target top block for canonical pattern `(2, 2, 2, 3, 3, 5)`. -/
def targetTop_1277 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     1, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1277 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 1, 0;
     0, 0, 1]

def columnPerm_1277 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1277 : BottomDetBound targetTop_1277 9 := by
  have hU : rowTransform_1277.det.natAbs = 1 := by
    have hdet : rowTransform_1277.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1277 hU
  have hcols := hrows.permuteColumns columnPerm_1277
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1277 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1277 = targetTop_1277 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1277 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 3 3 5)) 9 := by
  have htop : targetTop_1277 =
      topOfPattern (R := ℤ) (angle6 2 2 2 3 3 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1277

/-- Explicit target top block for canonical pattern `(2, 2, 2, 3, 3, 6)`. -/
def targetTop_1278 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 0;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1278 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 1;
     0, 0, 1]

def columnPerm_1278 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1278 : BottomDetBound targetTop_1278 9 := by
  have hU : rowTransform_1278.det.natAbs = 1 := by
    have hdet : rowTransform_1278.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1278 hU
  have hcols := hrows.permuteColumns columnPerm_1278
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1278 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1278 = targetTop_1278 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1278 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 3 3 6)) 9 := by
  have htop : targetTop_1278 =
      topOfPattern (R := ℤ) (angle6 2 2 2 3 3 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1278

/-- Explicit target top block for canonical pattern `(2, 2, 2, 3, 3, 7)`. -/
def targetTop_1279 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1279 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 1, 1;
     0, 0, 1]

def columnPerm_1279 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1279 : BottomDetBound targetTop_1279 9 := by
  have hU : rowTransform_1279.det.natAbs = 1 := by
    have hdet : rowTransform_1279.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1279 hU
  have hcols := hrows.permuteColumns columnPerm_1279
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1279 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1279 = targetTop_1279 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1279 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 3 3 7)) 9 := by
  have htop : targetTop_1279 =
      topOfPattern (R := ℤ) (angle6 2 2 2 3 3 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1279

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard079
