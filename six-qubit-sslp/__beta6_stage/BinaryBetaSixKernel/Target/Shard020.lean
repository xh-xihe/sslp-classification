-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard020

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 5, 5, 7, 7)`. -/
def targetTop_0320 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0320 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0320 :
    TopRowRelation targetTop_0320 relationCoefficients_0320 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0320, relationCoefficients_0320, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0320 : BottomDetBound targetTop_0320 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0320

theorem canonicalBound_0320 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 5 5 7 7)) 9 := by
  have htop : targetTop_0320 =
      topOfPattern (R := ℤ) (angle6 0 0 5 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0320

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 5, 6, 6, 6)`. -/
def targetTop_0321 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0321 : Fin 3 → ℤ :=
  ![1, 1, (-1)]

theorem topRelation_0321 :
    TopRowRelation targetTop_0321 relationCoefficients_0321 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0321, relationCoefficients_0321, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0321 : BottomDetBound targetTop_0321 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0321

theorem canonicalBound_0321 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 5 6 6 6)) 9 := by
  have htop : targetTop_0321 =
      topOfPattern (R := ℤ) (angle6 0 0 5 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0321

/-- Explicit target top block for canonical pattern `(0, 0, 5, 6, 6, 7)`. -/
def targetTop_0322 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0322 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 1;
     1, 1, 1]

def columnPerm_0322 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0322 : BottomDetBound targetTop_0322 9 := by
  have hU : rowTransform_0322.det.natAbs = 1 := by
    have hdet : rowTransform_0322.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0322 hU
  have hcols := hrows.permuteColumns columnPerm_0322
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0322 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0322 = targetTop_0322 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0322 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 5 6 6 7)) 9 := by
  have htop : targetTop_0322 =
      topOfPattern (R := ℤ) (angle6 0 0 5 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0322

/-- Explicit target top block for canonical pattern `(0, 0, 5, 6, 7, 7)`. -/
def targetTop_0323 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0323 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 1;
     1, 1, 1]

def columnPerm_0323 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0323 : BottomDetBound targetTop_0323 9 := by
  have hU : rowTransform_0323.det.natAbs = 1 := by
    have hdet : rowTransform_0323.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0323 hU
  have hcols := hrows.permuteColumns columnPerm_0323
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0323 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0323 = targetTop_0323 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0323 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 5 6 7 7)) 9 := by
  have htop : targetTop_0323 =
      topOfPattern (R := ℤ) (angle6 0 0 5 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0323

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 5, 7, 7, 7)`. -/
def targetTop_0324 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0324 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0324 :
    TopRowRelation targetTop_0324 relationCoefficients_0324 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0324, relationCoefficients_0324, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0324 : BottomDetBound targetTop_0324 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0324

theorem canonicalBound_0324 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 5 7 7 7)) 9 := by
  have htop : targetTop_0324 =
      topOfPattern (R := ℤ) (angle6 0 0 5 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0324

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 6, 6, 6, 6)`. -/
def targetTop_0325 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0325 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0325 :
    TopRowRelation targetTop_0325 relationCoefficients_0325 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0325, relationCoefficients_0325, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0325 : BottomDetBound targetTop_0325 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0325

theorem canonicalBound_0325 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 6 6 6 6)) 9 := by
  have htop : targetTop_0325 =
      topOfPattern (R := ℤ) (angle6 0 0 6 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0325

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 6, 6, 6, 7)`. -/
def targetTop_0326 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0326 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0326 :
    TopRowRelation targetTop_0326 relationCoefficients_0326 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0326, relationCoefficients_0326, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0326 : BottomDetBound targetTop_0326 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0326

theorem canonicalBound_0326 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 6 6 6 7)) 9 := by
  have htop : targetTop_0326 =
      topOfPattern (R := ℤ) (angle6 0 0 6 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0326

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 6, 6, 7, 7)`. -/
def targetTop_0327 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0327 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0327 :
    TopRowRelation targetTop_0327 relationCoefficients_0327 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0327, relationCoefficients_0327, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0327 : BottomDetBound targetTop_0327 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0327

theorem canonicalBound_0327 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 6 6 7 7)) 9 := by
  have htop : targetTop_0327 =
      topOfPattern (R := ℤ) (angle6 0 0 6 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0327

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 6, 7, 7, 7)`. -/
def targetTop_0328 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0328 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0328 :
    TopRowRelation targetTop_0328 relationCoefficients_0328 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0328, relationCoefficients_0328, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0328 : BottomDetBound targetTop_0328 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0328

theorem canonicalBound_0328 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 6 7 7 7)) 9 := by
  have htop : targetTop_0328 =
      topOfPattern (R := ℤ) (angle6 0 0 6 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0328

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 7, 7, 7, 7)`. -/
def targetTop_0329 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0329 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0329 :
    TopRowRelation targetTop_0329 relationCoefficients_0329 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0329, relationCoefficients_0329, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0329 : BottomDetBound targetTop_0329 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0329

theorem canonicalBound_0329 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 7 7 7 7)) 9 := by
  have htop : targetTop_0329 =
      topOfPattern (R := ℤ) (angle6 0 0 7 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0329

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 1, 1, 1, 1)`. -/
def targetTop_0330 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0330 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0330 :
    TopRowRelation targetTop_0330 relationCoefficients_0330 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0330, relationCoefficients_0330, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0330 : BottomDetBound targetTop_0330 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0330

theorem canonicalBound_0330 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 1 1)) 9 := by
  have htop : targetTop_0330 =
      topOfPattern (R := ℤ) (angle6 0 1 1 1 1 1) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0330

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 1, 1, 1, 2)`. -/
def targetTop_0331 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0331 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0331 :
    TopRowRelation targetTop_0331 relationCoefficients_0331 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0331, relationCoefficients_0331, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0331 : BottomDetBound targetTop_0331 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0331

theorem canonicalBound_0331 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 1 2)) 9 := by
  have htop : targetTop_0331 =
      topOfPattern (R := ℤ) (angle6 0 1 1 1 1 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0331

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 1, 1, 1, 3)`. -/
def targetTop_0332 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0332 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0332 :
    TopRowRelation targetTop_0332 relationCoefficients_0332 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0332, relationCoefficients_0332, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0332 : BottomDetBound targetTop_0332 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0332

theorem canonicalBound_0332 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 1 3)) 9 := by
  have htop : targetTop_0332 =
      topOfPattern (R := ℤ) (angle6 0 1 1 1 1 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0332

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 1, 1, 1, 4)`. -/
def targetTop_0333 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0333 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0333 :
    TopRowRelation targetTop_0333 relationCoefficients_0333 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0333, relationCoefficients_0333, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0333 : BottomDetBound targetTop_0333 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0333

theorem canonicalBound_0333 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 1 4)) 9 := by
  have htop : targetTop_0333 =
      topOfPattern (R := ℤ) (angle6 0 1 1 1 1 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0333

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 1, 1, 1, 5)`. -/
def targetTop_0334 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0334 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0334 :
    TopRowRelation targetTop_0334 relationCoefficients_0334 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0334, relationCoefficients_0334, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0334 : BottomDetBound targetTop_0334 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0334

theorem canonicalBound_0334 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 1 5)) 9 := by
  have htop : targetTop_0334 =
      topOfPattern (R := ℤ) (angle6 0 1 1 1 1 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0334

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 1, 1, 1, 6)`. -/
def targetTop_0335 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0335 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0335 :
    TopRowRelation targetTop_0335 relationCoefficients_0335 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0335, relationCoefficients_0335, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0335 : BottomDetBound targetTop_0335 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0335

theorem canonicalBound_0335 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 1 6)) 9 := by
  have htop : targetTop_0335 =
      topOfPattern (R := ℤ) (angle6 0 1 1 1 1 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0335

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard020
