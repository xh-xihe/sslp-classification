-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R022.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R023.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R024.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard031

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(0, 1, 3, 5, 5, 6)`. -/
def targetTop_0496 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 0;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0496 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_0496 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0496 : BottomDetBound targetTop_0496 9 := by
  have hU : rowTransform_0496.det.natAbs = 1 := by
    have hdet : rowTransform_0496.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R022.Aggregate.bottomBound.transformTopRows rowTransform_0496 hU
  have hcols := hrows.permuteColumns columnPerm_0496
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0496 MainTheory.Generated.BinaryBetaSixKernel.Representative.R022.Base.explicitTop)
          columnPerm_0496 = targetTop_0496 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0496 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 3 5 5 6)) 9 := by
  have htop : targetTop_0496 =
      topOfPattern (R := ℤ) (angle6 0 1 3 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0496

/-- Explicit target top block for canonical pattern `(0, 1, 3, 5, 5, 7)`. -/
def targetTop_0497 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0497 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_0497 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 5, 1, 2, 4]
  invFun := ![0, 3, 4, 1, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0497 : BottomDetBound targetTop_0497 9 := by
  have hU : rowTransform_0497.det.natAbs = 1 := by
    have hdet : rowTransform_0497.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Aggregate.bottomBound.transformTopRows rowTransform_0497 hU
  have hcols := hrows.permuteColumns columnPerm_0497
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0497 MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Base.explicitTop)
          columnPerm_0497 = targetTop_0497 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0497 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 3 5 5 7)) 9 := by
  have htop : targetTop_0497 =
      topOfPattern (R := ℤ) (angle6 0 1 3 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0497

/-- Explicit target top block for canonical pattern `(0, 1, 3, 5, 6, 6)`. -/
def targetTop_0498 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 0;
     0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0498 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0498 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0498 : BottomDetBound targetTop_0498 9 := by
  have hU : rowTransform_0498.det.natAbs = 1 := by
    have hdet : rowTransform_0498.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R023.Aggregate.bottomBound.transformTopRows rowTransform_0498 hU
  have hcols := hrows.permuteColumns columnPerm_0498
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0498 MainTheory.Generated.BinaryBetaSixKernel.Representative.R023.Base.explicitTop)
          columnPerm_0498 = targetTop_0498 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0498 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 3 5 6 6)) 9 := by
  have htop : targetTop_0498 =
      topOfPattern (R := ℤ) (angle6 0 1 3 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0498

/-- Explicit target top block for canonical pattern `(0, 1, 3, 5, 6, 7)`. -/
def targetTop_0499 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 1;
     0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0499 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0499 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0499 : BottomDetBound targetTop_0499 9 := by
  have hU : rowTransform_0499.det.natAbs = 1 := by
    have hdet : rowTransform_0499.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R024.Aggregate.bottomBound.transformTopRows rowTransform_0499 hU
  have hcols := hrows.permuteColumns columnPerm_0499
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0499 MainTheory.Generated.BinaryBetaSixKernel.Representative.R024.Base.explicitTop)
          columnPerm_0499 = targetTop_0499 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0499 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 3 5 6 7)) 9 := by
  have htop : targetTop_0499 =
      topOfPattern (R := ℤ) (angle6 0 1 3 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0499

/-- Explicit target top block for canonical pattern `(0, 1, 3, 5, 7, 7)`. -/
def targetTop_0500 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0500 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 1, (-1);
     1, 0, 0]

def columnPerm_0500 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 3, 4, 1, 2]
  invFun := ![0, 4, 5, 2, 3, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0500 : BottomDetBound targetTop_0500 9 := by
  have hU : rowTransform_0500.det.natAbs = 1 := by
    have hdet : rowTransform_0500.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Aggregate.bottomBound.transformTopRows rowTransform_0500 hU
  have hcols := hrows.permuteColumns columnPerm_0500
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0500 MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Base.explicitTop)
          columnPerm_0500 = targetTop_0500 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0500 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 3 5 7 7)) 9 := by
  have htop : targetTop_0500 =
      topOfPattern (R := ℤ) (angle6 0 1 3 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0500

/-- Explicit target top block for canonical pattern `(0, 1, 3, 6, 6, 6)`. -/
def targetTop_0501 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 0;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0501 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 1;
     1, 0, 0]

def columnPerm_0501 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0501 : BottomDetBound targetTop_0501 9 := by
  have hU : rowTransform_0501.det.natAbs = 1 := by
    have hdet : rowTransform_0501.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0501 hU
  have hcols := hrows.permuteColumns columnPerm_0501
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0501 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0501 = targetTop_0501 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0501 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 3 6 6 6)) 9 := by
  have htop : targetTop_0501 =
      topOfPattern (R := ℤ) (angle6 0 1 3 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0501

/-- Explicit target top block for canonical pattern `(0, 1, 3, 6, 6, 7)`. -/
def targetTop_0502 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0502 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 1;
     1, 0, 0]

def columnPerm_0502 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 5, 1, 2, 4]
  invFun := ![0, 3, 4, 1, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0502 : BottomDetBound targetTop_0502 9 := by
  have hU : rowTransform_0502.det.natAbs = 1 := by
    have hdet : rowTransform_0502.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0502 hU
  have hcols := hrows.permuteColumns columnPerm_0502
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0502 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0502 = targetTop_0502 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0502 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 3 6 6 7)) 9 := by
  have htop : targetTop_0502 =
      topOfPattern (R := ℤ) (angle6 0 1 3 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0502

/-- Explicit target top block for canonical pattern `(0, 1, 3, 6, 7, 7)`. -/
def targetTop_0503 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0503 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 1;
     0, 1, 0]

def columnPerm_0503 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0503 : BottomDetBound targetTop_0503 9 := by
  have hU : rowTransform_0503.det.natAbs = 1 := by
    have hdet : rowTransform_0503.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Aggregate.bottomBound.transformTopRows rowTransform_0503 hU
  have hcols := hrows.permuteColumns columnPerm_0503
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0503 MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Base.explicitTop)
          columnPerm_0503 = targetTop_0503 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0503 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 3 6 7 7)) 9 := by
  have htop : targetTop_0503 =
      topOfPattern (R := ℤ) (angle6 0 1 3 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0503

/-- Explicit target top block for canonical pattern `(0, 1, 3, 7, 7, 7)`. -/
def targetTop_0504 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0504 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     1, 0, 1;
     1, 0, 0]

def columnPerm_0504 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0504 : BottomDetBound targetTop_0504 9 := by
  have hU : rowTransform_0504.det.natAbs = 1 := by
    have hdet : rowTransform_0504.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0504 hU
  have hcols := hrows.permuteColumns columnPerm_0504
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0504 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0504 = targetTop_0504 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0504 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 3 7 7 7)) 9 := by
  have htop : targetTop_0504 =
      topOfPattern (R := ℤ) (angle6 0 1 3 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0504

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 4, 4, 4, 4)`. -/
def targetTop_0505 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0505 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0505 :
    TopRowRelation targetTop_0505 relationCoefficients_0505 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0505, relationCoefficients_0505, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0505 : BottomDetBound targetTop_0505 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0505

theorem canonicalBound_0505 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 4 4 4 4)) 9 := by
  have htop : targetTop_0505 =
      topOfPattern (R := ℤ) (angle6 0 1 4 4 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0505

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 4, 4, 4, 5)`. -/
def targetTop_0506 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0506 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0506 :
    TopRowRelation targetTop_0506 relationCoefficients_0506 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0506, relationCoefficients_0506, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0506 : BottomDetBound targetTop_0506 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0506

theorem canonicalBound_0506 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 4 4 4 5)) 9 := by
  have htop : targetTop_0506 =
      topOfPattern (R := ℤ) (angle6 0 1 4 4 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0506

/-- Explicit target top block for canonical pattern `(0, 1, 4, 4, 4, 6)`. -/
def targetTop_0507 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0507 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 1]

def columnPerm_0507 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 3, 5]
  invFun := ![0, 2, 3, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0507 : BottomDetBound targetTop_0507 9 := by
  have hU : rowTransform_0507.det.natAbs = 1 := by
    have hdet : rowTransform_0507.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0507 hU
  have hcols := hrows.permuteColumns columnPerm_0507
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0507 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0507 = targetTop_0507 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0507 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 4 4 4 6)) 9 := by
  have htop : targetTop_0507 =
      topOfPattern (R := ℤ) (angle6 0 1 4 4 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0507

/-- Explicit target top block for canonical pattern `(0, 1, 4, 4, 4, 7)`. -/
def targetTop_0508 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0508 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 0, 1;
     1, 0, 1]

def columnPerm_0508 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 3, 5]
  invFun := ![0, 2, 3, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0508 : BottomDetBound targetTop_0508 9 := by
  have hU : rowTransform_0508.det.natAbs = 1 := by
    have hdet : rowTransform_0508.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0508 hU
  have hcols := hrows.permuteColumns columnPerm_0508
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0508 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0508 = targetTop_0508 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0508 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 4 4 4 7)) 9 := by
  have htop : targetTop_0508 =
      topOfPattern (R := ℤ) (angle6 0 1 4 4 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0508

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 4, 4, 5, 5)`. -/
def targetTop_0509 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0509 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0509 :
    TopRowRelation targetTop_0509 relationCoefficients_0509 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0509, relationCoefficients_0509, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0509 : BottomDetBound targetTop_0509 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0509

theorem canonicalBound_0509 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 4 4 5 5)) 9 := by
  have htop : targetTop_0509 =
      topOfPattern (R := ℤ) (angle6 0 1 4 4 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0509

/-- Explicit target top block for canonical pattern `(0, 1, 4, 4, 5, 6)`. -/
def targetTop_0510 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0510 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 1]

def columnPerm_0510 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 4, 5]
  invFun := ![0, 2, 3, 1, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0510 : BottomDetBound targetTop_0510 9 := by
  have hU : rowTransform_0510.det.natAbs = 1 := by
    have hdet : rowTransform_0510.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0510 hU
  have hcols := hrows.permuteColumns columnPerm_0510
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0510 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0510 = targetTop_0510 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0510 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 4 4 5 6)) 9 := by
  have htop : targetTop_0510 =
      topOfPattern (R := ℤ) (angle6 0 1 4 4 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0510

/-- Explicit target top block for canonical pattern `(0, 1, 4, 4, 5, 7)`. -/
def targetTop_0511 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0511 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 0, 1;
     1, 0, 1]

def columnPerm_0511 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 4, 5]
  invFun := ![0, 2, 3, 1, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0511 : BottomDetBound targetTop_0511 9 := by
  have hU : rowTransform_0511.det.natAbs = 1 := by
    have hdet : rowTransform_0511.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0511 hU
  have hcols := hrows.permuteColumns columnPerm_0511
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0511 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0511 = targetTop_0511 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0511 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 4 4 5 7)) 9 := by
  have htop : targetTop_0511 =
      topOfPattern (R := ℤ) (angle6 0 1 4 4 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0511

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard031
