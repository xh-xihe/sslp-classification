-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard078

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit rank-deficient target for canonical pattern `(1, 6, 6, 6, 6, 6)`. -/
def targetTop_1248 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1248 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_1248 :
    TopRowRelation targetTop_1248 relationCoefficients_1248 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1248, relationCoefficients_1248, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1248 : BottomDetBound targetTop_1248 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1248

theorem canonicalBound_1248 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 6 6 6 6 6)) 9 := by
  have htop : targetTop_1248 =
      topOfPattern (R := ℤ) (angle6 1 6 6 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1248

/-- Explicit rank-deficient target for canonical pattern `(1, 6, 6, 6, 6, 7)`. -/
def targetTop_1249 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1249 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_1249 :
    TopRowRelation targetTop_1249 relationCoefficients_1249 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1249, relationCoefficients_1249, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1249 : BottomDetBound targetTop_1249 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1249

theorem canonicalBound_1249 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 6 6 6 6 7)) 9 := by
  have htop : targetTop_1249 =
      topOfPattern (R := ℤ) (angle6 1 6 6 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1249

/-- Explicit rank-deficient target for canonical pattern `(1, 6, 6, 6, 7, 7)`. -/
def targetTop_1250 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1250 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_1250 :
    TopRowRelation targetTop_1250 relationCoefficients_1250 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1250, relationCoefficients_1250, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1250 : BottomDetBound targetTop_1250 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1250

theorem canonicalBound_1250 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 6 6 6 7 7)) 9 := by
  have htop : targetTop_1250 =
      topOfPattern (R := ℤ) (angle6 1 6 6 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1250

/-- Explicit rank-deficient target for canonical pattern `(1, 6, 6, 7, 7, 7)`. -/
def targetTop_1251 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1251 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_1251 :
    TopRowRelation targetTop_1251 relationCoefficients_1251 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1251, relationCoefficients_1251, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1251 : BottomDetBound targetTop_1251 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1251

theorem canonicalBound_1251 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 6 6 7 7 7)) 9 := by
  have htop : targetTop_1251 =
      topOfPattern (R := ℤ) (angle6 1 6 6 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1251

/-- Explicit rank-deficient target for canonical pattern `(1, 6, 7, 7, 7, 7)`. -/
def targetTop_1252 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1252 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_1252 :
    TopRowRelation targetTop_1252 relationCoefficients_1252 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1252, relationCoefficients_1252, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1252 : BottomDetBound targetTop_1252 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1252

theorem canonicalBound_1252 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 6 7 7 7 7)) 9 := by
  have htop : targetTop_1252 =
      topOfPattern (R := ℤ) (angle6 1 6 7 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1252

/-- Explicit rank-deficient target for canonical pattern `(1, 7, 7, 7, 7, 7)`. -/
def targetTop_1253 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1253 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_1253 :
    TopRowRelation targetTop_1253 relationCoefficients_1253 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1253, relationCoefficients_1253, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1253 : BottomDetBound targetTop_1253 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1253

theorem canonicalBound_1253 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 7 7 7 7 7)) 9 := by
  have htop : targetTop_1253 =
      topOfPattern (R := ℤ) (angle6 1 7 7 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1253

/-- Explicit rank-deficient target for canonical pattern `(2, 2, 2, 2, 2, 2)`. -/
def targetTop_1254 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1254 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_1254 :
    TopRowRelation targetTop_1254 relationCoefficients_1254 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1254, relationCoefficients_1254, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1254 : BottomDetBound targetTop_1254 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1254

theorem canonicalBound_1254 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 2 2 2)) 9 := by
  have htop : targetTop_1254 =
      topOfPattern (R := ℤ) (angle6 2 2 2 2 2 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1254

/-- Explicit rank-deficient target for canonical pattern `(2, 2, 2, 2, 2, 3)`. -/
def targetTop_1255 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1255 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_1255 :
    TopRowRelation targetTop_1255 relationCoefficients_1255 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1255, relationCoefficients_1255, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1255 : BottomDetBound targetTop_1255 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1255

theorem canonicalBound_1255 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 2 2 3)) 9 := by
  have htop : targetTop_1255 =
      topOfPattern (R := ℤ) (angle6 2 2 2 2 2 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1255

/-- Explicit rank-deficient target for canonical pattern `(2, 2, 2, 2, 2, 4)`. -/
def targetTop_1256 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     1, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1256 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_1256 :
    TopRowRelation targetTop_1256 relationCoefficients_1256 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1256, relationCoefficients_1256, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1256 : BottomDetBound targetTop_1256 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1256

theorem canonicalBound_1256 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 2 2 4)) 9 := by
  have htop : targetTop_1256 =
      topOfPattern (R := ℤ) (angle6 2 2 2 2 2 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1256

/-- Explicit rank-deficient target for canonical pattern `(2, 2, 2, 2, 2, 5)`. -/
def targetTop_1257 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     1, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1257 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_1257 :
    TopRowRelation targetTop_1257 relationCoefficients_1257 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1257, relationCoefficients_1257, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1257 : BottomDetBound targetTop_1257 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1257

theorem canonicalBound_1257 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 2 2 5)) 9 := by
  have htop : targetTop_1257 =
      topOfPattern (R := ℤ) (angle6 2 2 2 2 2 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1257

/-- Explicit rank-deficient target for canonical pattern `(2, 2, 2, 2, 2, 6)`. -/
def targetTop_1258 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1258 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_1258 :
    TopRowRelation targetTop_1258 relationCoefficients_1258 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1258, relationCoefficients_1258, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1258 : BottomDetBound targetTop_1258 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1258

theorem canonicalBound_1258 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 2 2 6)) 9 := by
  have htop : targetTop_1258 =
      topOfPattern (R := ℤ) (angle6 2 2 2 2 2 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1258

/-- Explicit rank-deficient target for canonical pattern `(2, 2, 2, 2, 2, 7)`. -/
def targetTop_1259 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1259 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_1259 :
    TopRowRelation targetTop_1259 relationCoefficients_1259 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1259, relationCoefficients_1259, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1259 : BottomDetBound targetTop_1259 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1259

theorem canonicalBound_1259 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 2 2 7)) 9 := by
  have htop : targetTop_1259 =
      topOfPattern (R := ℤ) (angle6 2 2 2 2 2 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1259

/-- Explicit rank-deficient target for canonical pattern `(2, 2, 2, 2, 3, 3)`. -/
def targetTop_1260 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1260 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_1260 :
    TopRowRelation targetTop_1260 relationCoefficients_1260 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1260, relationCoefficients_1260, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1260 : BottomDetBound targetTop_1260 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1260

theorem canonicalBound_1260 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 2 3 3)) 9 := by
  have htop : targetTop_1260 =
      topOfPattern (R := ℤ) (angle6 2 2 2 2 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1260

/-- Explicit target top block for canonical pattern `(2, 2, 2, 2, 3, 4)`. -/
def targetTop_1261 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 0;
     1, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1261 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 0;
     0, 0, 1]

def columnPerm_1261 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1261 : BottomDetBound targetTop_1261 9 := by
  have hU : rowTransform_1261.det.natAbs = 1 := by
    have hdet : rowTransform_1261.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1261 hU
  have hcols := hrows.permuteColumns columnPerm_1261
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1261 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1261 = targetTop_1261 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1261 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 2 3 4)) 9 := by
  have htop : targetTop_1261 =
      topOfPattern (R := ℤ) (angle6 2 2 2 2 3 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1261

/-- Explicit target top block for canonical pattern `(2, 2, 2, 2, 3, 5)`. -/
def targetTop_1262 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     1, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1262 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 1, 0;
     0, 0, 1]

def columnPerm_1262 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1262 : BottomDetBound targetTop_1262 9 := by
  have hU : rowTransform_1262.det.natAbs = 1 := by
    have hdet : rowTransform_1262.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1262 hU
  have hcols := hrows.permuteColumns columnPerm_1262
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1262 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1262 = targetTop_1262 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1262 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 2 3 5)) 9 := by
  have htop : targetTop_1262 =
      topOfPattern (R := ℤ) (angle6 2 2 2 2 3 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1262

/-- Explicit target top block for canonical pattern `(2, 2, 2, 2, 3, 6)`. -/
def targetTop_1263 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 0;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1263 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 1;
     0, 0, 1]

def columnPerm_1263 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1263 : BottomDetBound targetTop_1263 9 := by
  have hU : rowTransform_1263.det.natAbs = 1 := by
    have hdet : rowTransform_1263.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1263 hU
  have hcols := hrows.permuteColumns columnPerm_1263
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1263 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1263 = targetTop_1263 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1263 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 2 3 6)) 9 := by
  have htop : targetTop_1263 =
      topOfPattern (R := ℤ) (angle6 2 2 2 2 3 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1263

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard078
