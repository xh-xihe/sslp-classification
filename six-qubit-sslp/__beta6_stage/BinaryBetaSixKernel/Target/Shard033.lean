-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard033

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(0, 1, 5, 5, 6, 6)`. -/
def targetTop_0528 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0528 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 0;
     1, 1, 0]

def columnPerm_0528 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0528 : BottomDetBound targetTop_0528 9 := by
  have hU : rowTransform_0528.det.natAbs = 1 := by
    have hdet : rowTransform_0528.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0528 hU
  have hcols := hrows.permuteColumns columnPerm_0528
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0528 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0528 = targetTop_0528 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0528 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 5 5 6 6)) 9 := by
  have htop : targetTop_0528 =
      topOfPattern (R := ℤ) (angle6 0 1 5 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0528

/-- Explicit target top block for canonical pattern `(0, 1, 5, 5, 6, 7)`. -/
def targetTop_0529 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0529 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 0, 1;
     1, 0, 1]

def columnPerm_0529 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 4, 5]
  invFun := ![0, 2, 3, 1, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0529 : BottomDetBound targetTop_0529 9 := by
  have hU : rowTransform_0529.det.natAbs = 1 := by
    have hdet : rowTransform_0529.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate.bottomBound.transformTopRows rowTransform_0529 hU
  have hcols := hrows.permuteColumns columnPerm_0529
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0529 MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Base.explicitTop)
          columnPerm_0529 = targetTop_0529 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0529 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 5 5 6 7)) 9 := by
  have htop : targetTop_0529 =
      topOfPattern (R := ℤ) (angle6 0 1 5 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0529

/-- Explicit target top block for canonical pattern `(0, 1, 5, 5, 7, 7)`. -/
def targetTop_0530 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0530 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 1, 0;
     1, 1, 0]

def columnPerm_0530 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0530 : BottomDetBound targetTop_0530 9 := by
  have hU : rowTransform_0530.det.natAbs = 1 := by
    have hdet : rowTransform_0530.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0530 hU
  have hcols := hrows.permuteColumns columnPerm_0530
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0530 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0530 = targetTop_0530 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0530 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 5 5 7 7)) 9 := by
  have htop : targetTop_0530 =
      topOfPattern (R := ℤ) (angle6 0 1 5 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0530

/-- Explicit target top block for canonical pattern `(0, 1, 5, 6, 6, 6)`. -/
def targetTop_0531 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0531 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 0;
     1, 0, 1]

def columnPerm_0531 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0531 : BottomDetBound targetTop_0531 9 := by
  have hU : rowTransform_0531.det.natAbs = 1 := by
    have hdet : rowTransform_0531.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0531 hU
  have hcols := hrows.permuteColumns columnPerm_0531
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0531 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0531 = targetTop_0531 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0531 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 5 6 6 6)) 9 := by
  have htop : targetTop_0531 =
      topOfPattern (R := ℤ) (angle6 0 1 5 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0531

/-- Explicit target top block for canonical pattern `(0, 1, 5, 6, 6, 7)`. -/
def targetTop_0532 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0532 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 0;
     1, 0, 1]

def columnPerm_0532 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 5, 1, 2, 4]
  invFun := ![0, 3, 4, 1, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0532 : BottomDetBound targetTop_0532 9 := by
  have hU : rowTransform_0532.det.natAbs = 1 := by
    have hdet : rowTransform_0532.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0532 hU
  have hcols := hrows.permuteColumns columnPerm_0532
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0532 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0532 = targetTop_0532 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0532 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 5 6 6 7)) 9 := by
  have htop : targetTop_0532 =
      topOfPattern (R := ℤ) (angle6 0 1 5 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0532

/-- Explicit target top block for canonical pattern `(0, 1, 5, 6, 7, 7)`. -/
def targetTop_0533 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0533 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 0;
     0, 1, 1]

def columnPerm_0533 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0533 : BottomDetBound targetTop_0533 9 := by
  have hU : rowTransform_0533.det.natAbs = 1 := by
    have hdet : rowTransform_0533.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Aggregate.bottomBound.transformTopRows rowTransform_0533 hU
  have hcols := hrows.permuteColumns columnPerm_0533
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0533 MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Base.explicitTop)
          columnPerm_0533 = targetTop_0533 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0533 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 5 6 7 7)) 9 := by
  have htop : targetTop_0533 =
      topOfPattern (R := ℤ) (angle6 0 1 5 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0533

/-- Explicit target top block for canonical pattern `(0, 1, 5, 7, 7, 7)`. -/
def targetTop_0534 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0534 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     1, 0, 0;
     1, 0, 1]

def columnPerm_0534 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0534 : BottomDetBound targetTop_0534 9 := by
  have hU : rowTransform_0534.det.natAbs = 1 := by
    have hdet : rowTransform_0534.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0534 hU
  have hcols := hrows.permuteColumns columnPerm_0534
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0534 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0534 = targetTop_0534 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0534 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 5 7 7 7)) 9 := by
  have htop : targetTop_0534 =
      topOfPattern (R := ℤ) (angle6 0 1 5 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0534

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 6, 6, 6, 6)`. -/
def targetTop_0535 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0535 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0535 :
    TopRowRelation targetTop_0535 relationCoefficients_0535 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0535, relationCoefficients_0535, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0535 : BottomDetBound targetTop_0535 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0535

theorem canonicalBound_0535 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 6 6 6 6)) 9 := by
  have htop : targetTop_0535 =
      topOfPattern (R := ℤ) (angle6 0 1 6 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0535

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 6, 6, 6, 7)`. -/
def targetTop_0536 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0536 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0536 :
    TopRowRelation targetTop_0536 relationCoefficients_0536 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0536, relationCoefficients_0536, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0536 : BottomDetBound targetTop_0536 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0536

theorem canonicalBound_0536 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 6 6 6 7)) 9 := by
  have htop : targetTop_0536 =
      topOfPattern (R := ℤ) (angle6 0 1 6 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0536

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 6, 6, 7, 7)`. -/
def targetTop_0537 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0537 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0537 :
    TopRowRelation targetTop_0537 relationCoefficients_0537 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0537, relationCoefficients_0537, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0537 : BottomDetBound targetTop_0537 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0537

theorem canonicalBound_0537 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 6 6 7 7)) 9 := by
  have htop : targetTop_0537 =
      topOfPattern (R := ℤ) (angle6 0 1 6 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0537

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 6, 7, 7, 7)`. -/
def targetTop_0538 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0538 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0538 :
    TopRowRelation targetTop_0538 relationCoefficients_0538 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0538, relationCoefficients_0538, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0538 : BottomDetBound targetTop_0538 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0538

theorem canonicalBound_0538 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 6 7 7 7)) 9 := by
  have htop : targetTop_0538 =
      topOfPattern (R := ℤ) (angle6 0 1 6 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0538

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 7, 7, 7, 7)`. -/
def targetTop_0539 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0539 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0539 :
    TopRowRelation targetTop_0539 relationCoefficients_0539 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0539, relationCoefficients_0539, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0539 : BottomDetBound targetTop_0539 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0539

theorem canonicalBound_0539 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 7 7 7 7)) 9 := by
  have htop : targetTop_0539 =
      topOfPattern (R := ℤ) (angle6 0 1 7 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0539

/-- Explicit rank-deficient target for canonical pattern `(0, 2, 2, 2, 2, 2)`. -/
def targetTop_0540 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0540 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0540 :
    TopRowRelation targetTop_0540 relationCoefficients_0540 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0540, relationCoefficients_0540, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0540 : BottomDetBound targetTop_0540 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0540

theorem canonicalBound_0540 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 2 2 2)) 9 := by
  have htop : targetTop_0540 =
      topOfPattern (R := ℤ) (angle6 0 2 2 2 2 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0540

/-- Explicit rank-deficient target for canonical pattern `(0, 2, 2, 2, 2, 3)`. -/
def targetTop_0541 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0541 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0541 :
    TopRowRelation targetTop_0541 relationCoefficients_0541 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0541, relationCoefficients_0541, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0541 : BottomDetBound targetTop_0541 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0541

theorem canonicalBound_0541 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 2 2 3)) 9 := by
  have htop : targetTop_0541 =
      topOfPattern (R := ℤ) (angle6 0 2 2 2 2 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0541

/-- Explicit rank-deficient target for canonical pattern `(0, 2, 2, 2, 2, 4)`. -/
def targetTop_0542 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0542 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0542 :
    TopRowRelation targetTop_0542 relationCoefficients_0542 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0542, relationCoefficients_0542, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0542 : BottomDetBound targetTop_0542 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0542

theorem canonicalBound_0542 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 2 2 4)) 9 := by
  have htop : targetTop_0542 =
      topOfPattern (R := ℤ) (angle6 0 2 2 2 2 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0542

/-- Explicit rank-deficient target for canonical pattern `(0, 2, 2, 2, 2, 5)`. -/
def targetTop_0543 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0543 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0543 :
    TopRowRelation targetTop_0543 relationCoefficients_0543 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0543, relationCoefficients_0543, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0543 : BottomDetBound targetTop_0543 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0543

theorem canonicalBound_0543 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 2 2 5)) 9 := by
  have htop : targetTop_0543 =
      topOfPattern (R := ℤ) (angle6 0 2 2 2 2 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0543

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard033
