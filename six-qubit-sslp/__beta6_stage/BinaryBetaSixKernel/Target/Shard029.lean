-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R021.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard029

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(0, 1, 2, 5, 6, 7)`. -/
def targetTop_0464 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 0, 1;
     0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0464 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0464 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0464 : BottomDetBound targetTop_0464 9 := by
  have hU : rowTransform_0464.det.natAbs = 1 := by
    have hdet : rowTransform_0464.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R021.Aggregate.bottomBound.transformTopRows rowTransform_0464 hU
  have hcols := hrows.permuteColumns columnPerm_0464
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0464 MainTheory.Generated.BinaryBetaSixKernel.Representative.R021.Base.explicitTop)
          columnPerm_0464 = targetTop_0464 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0464 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 5 6 7)) 9 := by
  have htop : targetTop_0464 =
      topOfPattern (R := ℤ) (angle6 0 1 2 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0464

/-- Explicit target top block for canonical pattern `(0, 1, 2, 5, 7, 7)`. -/
def targetTop_0465 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 1, 1;
     0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0465 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_0465 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0465 : BottomDetBound targetTop_0465 9 := by
  have hU : rowTransform_0465.det.natAbs = 1 := by
    have hdet : rowTransform_0465.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Aggregate.bottomBound.transformTopRows rowTransform_0465 hU
  have hcols := hrows.permuteColumns columnPerm_0465
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0465 MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Base.explicitTop)
          columnPerm_0465 = targetTop_0465 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0465 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 5 7 7)) 9 := by
  have htop : targetTop_0465 =
      topOfPattern (R := ℤ) (angle6 0 1 2 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0465

/-- Explicit target top block for canonical pattern `(0, 1, 2, 6, 6, 6)`. -/
def targetTop_0466 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0466 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 1;
     1, 0, 0]

def columnPerm_0466 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0466 : BottomDetBound targetTop_0466 9 := by
  have hU : rowTransform_0466.det.natAbs = 1 := by
    have hdet : rowTransform_0466.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0466 hU
  have hcols := hrows.permuteColumns columnPerm_0466
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0466 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0466 = targetTop_0466 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0466 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 6 6 6)) 9 := by
  have htop : targetTop_0466 =
      topOfPattern (R := ℤ) (angle6 0 1 2 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0466

/-- Explicit target top block for canonical pattern `(0, 1, 2, 6, 6, 7)`. -/
def targetTop_0467 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0467 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 1;
     1, 0, 0]

def columnPerm_0467 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 5, 1, 2, 4]
  invFun := ![0, 3, 4, 1, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0467 : BottomDetBound targetTop_0467 9 := by
  have hU : rowTransform_0467.det.natAbs = 1 := by
    have hdet : rowTransform_0467.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0467 hU
  have hcols := hrows.permuteColumns columnPerm_0467
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0467 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0467 = targetTop_0467 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0467 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 6 6 7)) 9 := by
  have htop : targetTop_0467 =
      topOfPattern (R := ℤ) (angle6 0 1 2 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0467

/-- Explicit target top block for canonical pattern `(0, 1, 2, 6, 7, 7)`. -/
def targetTop_0468 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0468 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     0, 1, 0]

def columnPerm_0468 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0468 : BottomDetBound targetTop_0468 9 := by
  have hU : rowTransform_0468.det.natAbs = 1 := by
    have hdet : rowTransform_0468.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Aggregate.bottomBound.transformTopRows rowTransform_0468 hU
  have hcols := hrows.permuteColumns columnPerm_0468
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0468 MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Base.explicitTop)
          columnPerm_0468 = targetTop_0468 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0468 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 6 7 7)) 9 := by
  have htop : targetTop_0468 =
      topOfPattern (R := ℤ) (angle6 0 1 2 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0468

/-- Explicit target top block for canonical pattern `(0, 1, 2, 7, 7, 7)`. -/
def targetTop_0469 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0469 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 1;
     1, 0, 0]

def columnPerm_0469 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0469 : BottomDetBound targetTop_0469 9 := by
  have hU : rowTransform_0469.det.natAbs = 1 := by
    have hdet : rowTransform_0469.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0469 hU
  have hcols := hrows.permuteColumns columnPerm_0469
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0469 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0469 = targetTop_0469 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0469 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 7 7 7)) 9 := by
  have htop : targetTop_0469 =
      topOfPattern (R := ℤ) (angle6 0 1 2 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0469

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 3, 3, 3, 3)`. -/
def targetTop_0470 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0470 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0470 :
    TopRowRelation targetTop_0470 relationCoefficients_0470 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0470, relationCoefficients_0470, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0470 : BottomDetBound targetTop_0470 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0470

theorem canonicalBound_0470 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 3 3 3 3)) 9 := by
  have htop : targetTop_0470 =
      topOfPattern (R := ℤ) (angle6 0 1 3 3 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0470

/-- Explicit target top block for canonical pattern `(0, 1, 3, 3, 3, 4)`. -/
def targetTop_0471 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 0;
     0, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0471 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_0471 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 3, 5]
  invFun := ![0, 2, 3, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0471 : BottomDetBound targetTop_0471 9 := by
  have hU : rowTransform_0471.det.natAbs = 1 := by
    have hdet : rowTransform_0471.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0471 hU
  have hcols := hrows.permuteColumns columnPerm_0471
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0471 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0471 = targetTop_0471 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0471 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 3 3 3 4)) 9 := by
  have htop : targetTop_0471 =
      topOfPattern (R := ℤ) (angle6 0 1 3 3 3 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0471

/-- Explicit target top block for canonical pattern `(0, 1, 3, 3, 3, 5)`. -/
def targetTop_0472 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0472 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     1, 0, 0;
     0, 0, 1]

def columnPerm_0472 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 3, 5]
  invFun := ![0, 2, 3, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0472 : BottomDetBound targetTop_0472 9 := by
  have hU : rowTransform_0472.det.natAbs = 1 := by
    have hdet : rowTransform_0472.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0472 hU
  have hcols := hrows.permuteColumns columnPerm_0472
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0472 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0472 = targetTop_0472 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0472 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 3 3 3 5)) 9 := by
  have htop : targetTop_0472 =
      topOfPattern (R := ℤ) (angle6 0 1 3 3 3 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0472

/-- Explicit target top block for canonical pattern `(0, 1, 3, 3, 3, 6)`. -/
def targetTop_0473 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 0;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0473 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 1;
     0, 0, 1]

def columnPerm_0473 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 3, 5]
  invFun := ![0, 2, 3, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0473 : BottomDetBound targetTop_0473 9 := by
  have hU : rowTransform_0473.det.natAbs = 1 := by
    have hdet : rowTransform_0473.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0473 hU
  have hcols := hrows.permuteColumns columnPerm_0473
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0473 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0473 = targetTop_0473 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0473 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 3 3 3 6)) 9 := by
  have htop : targetTop_0473 =
      topOfPattern (R := ℤ) (angle6 0 1 3 3 3 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0473

/-- Explicit target top block for canonical pattern `(0, 1, 3, 3, 3, 7)`. -/
def targetTop_0474 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0474 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     1, 0, 1;
     0, 0, 1]

def columnPerm_0474 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 3, 5]
  invFun := ![0, 2, 3, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0474 : BottomDetBound targetTop_0474 9 := by
  have hU : rowTransform_0474.det.natAbs = 1 := by
    have hdet : rowTransform_0474.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0474 hU
  have hcols := hrows.permuteColumns columnPerm_0474
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0474 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0474 = targetTop_0474 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0474 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 3 3 3 7)) 9 := by
  have htop : targetTop_0474 =
      topOfPattern (R := ℤ) (angle6 0 1 3 3 3 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0474

/-- Explicit target top block for canonical pattern `(0, 1, 3, 3, 4, 4)`. -/
def targetTop_0475 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 0;
     0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0475 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_0475 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0475 : BottomDetBound targetTop_0475 9 := by
  have hU : rowTransform_0475.det.natAbs = 1 := by
    have hdet : rowTransform_0475.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0475 hU
  have hcols := hrows.permuteColumns columnPerm_0475
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0475 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0475 = targetTop_0475 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0475 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 3 3 4 4)) 9 := by
  have htop : targetTop_0475 =
      topOfPattern (R := ℤ) (angle6 0 1 3 3 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0475

/-- Explicit target top block for canonical pattern `(0, 1, 3, 3, 4, 5)`. -/
def targetTop_0476 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 1;
     0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0476 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_0476 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 4, 5]
  invFun := ![0, 2, 3, 1, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0476 : BottomDetBound targetTop_0476 9 := by
  have hU : rowTransform_0476.det.natAbs = 1 := by
    have hdet : rowTransform_0476.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate.bottomBound.transformTopRows rowTransform_0476 hU
  have hcols := hrows.permuteColumns columnPerm_0476
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0476 MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Base.explicitTop)
          columnPerm_0476 = targetTop_0476 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0476 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 3 3 4 5)) 9 := by
  have htop : targetTop_0476 =
      topOfPattern (R := ℤ) (angle6 0 1 3 3 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0476

/-- Explicit target top block for canonical pattern `(0, 1, 3, 3, 4, 6)`. -/
def targetTop_0477 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 0;
     0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0477 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, (-1);
     1, 0, 0;
     0, 0, 1]

def columnPerm_0477 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 5, 4]
  invFun := ![0, 2, 3, 1, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0477 : BottomDetBound targetTop_0477 9 := by
  have hU : rowTransform_0477.det.natAbs = 1 := by
    have hdet : rowTransform_0477.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Aggregate.bottomBound.transformTopRows rowTransform_0477 hU
  have hcols := hrows.permuteColumns columnPerm_0477
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0477 MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Base.explicitTop)
          columnPerm_0477 = targetTop_0477 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0477 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 3 3 4 6)) 9 := by
  have htop : targetTop_0477 =
      topOfPattern (R := ℤ) (angle6 0 1 3 3 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0477

/-- Explicit target top block for canonical pattern `(0, 1, 3, 3, 4, 7)`. -/
def targetTop_0478 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 1;
     0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0478 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_0478 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0478 : BottomDetBound targetTop_0478 9 := by
  have hU : rowTransform_0478.det.natAbs = 1 := by
    have hdet : rowTransform_0478.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0478 hU
  have hcols := hrows.permuteColumns columnPerm_0478
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0478 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0478 = targetTop_0478 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0478 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 3 3 4 7)) 9 := by
  have htop : targetTop_0478 =
      topOfPattern (R := ℤ) (angle6 0 1 3 3 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0478

/-- Explicit target top block for canonical pattern `(0, 1, 3, 3, 5, 5)`. -/
def targetTop_0479 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0479 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_0479 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0479 : BottomDetBound targetTop_0479 9 := by
  have hU : rowTransform_0479.det.natAbs = 1 := by
    have hdet : rowTransform_0479.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0479 hU
  have hcols := hrows.permuteColumns columnPerm_0479
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0479 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0479 = targetTop_0479 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0479 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 3 3 5 5)) 9 := by
  have htop : targetTop_0479 =
      topOfPattern (R := ℤ) (angle6 0 1 3 3 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0479

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard029
