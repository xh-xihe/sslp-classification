-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R017.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard032

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(0, 1, 4, 4, 6, 6)`. -/
def targetTop_0512 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0512 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 1, 0]

def columnPerm_0512 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0512 : BottomDetBound targetTop_0512 9 := by
  have hU : rowTransform_0512.det.natAbs = 1 := by
    have hdet : rowTransform_0512.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0512 hU
  have hcols := hrows.permuteColumns columnPerm_0512
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0512 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0512 = targetTop_0512 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0512 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 4 4 6 6)) 9 := by
  have htop : targetTop_0512 =
      topOfPattern (R := ℤ) (angle6 0 1 4 4 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0512

/-- Explicit target top block for canonical pattern `(0, 1, 4, 4, 6, 7)`. -/
def targetTop_0513 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0513 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 1]

def columnPerm_0513 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 4, 5]
  invFun := ![0, 2, 3, 1, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0513 : BottomDetBound targetTop_0513 9 := by
  have hU : rowTransform_0513.det.natAbs = 1 := by
    have hdet : rowTransform_0513.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate.bottomBound.transformTopRows rowTransform_0513 hU
  have hcols := hrows.permuteColumns columnPerm_0513
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0513 MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Base.explicitTop)
          columnPerm_0513 = targetTop_0513 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0513 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 4 4 6 7)) 9 := by
  have htop : targetTop_0513 =
      topOfPattern (R := ℤ) (angle6 0 1 4 4 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0513

/-- Explicit target top block for canonical pattern `(0, 1, 4, 4, 7, 7)`. -/
def targetTop_0514 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0514 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 1, 0;
     1, 1, 0]

def columnPerm_0514 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0514 : BottomDetBound targetTop_0514 9 := by
  have hU : rowTransform_0514.det.natAbs = 1 := by
    have hdet : rowTransform_0514.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0514 hU
  have hcols := hrows.permuteColumns columnPerm_0514
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0514 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0514 = targetTop_0514 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0514 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 4 4 7 7)) 9 := by
  have htop : targetTop_0514 =
      topOfPattern (R := ℤ) (angle6 0 1 4 4 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0514

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 4, 5, 5, 5)`. -/
def targetTop_0515 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0515 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0515 :
    TopRowRelation targetTop_0515 relationCoefficients_0515 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0515, relationCoefficients_0515, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0515 : BottomDetBound targetTop_0515 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0515

theorem canonicalBound_0515 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 4 5 5 5)) 9 := by
  have htop : targetTop_0515 =
      topOfPattern (R := ℤ) (angle6 0 1 4 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0515

/-- Explicit target top block for canonical pattern `(0, 1, 4, 5, 5, 6)`. -/
def targetTop_0516 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0516 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0516 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0516 : BottomDetBound targetTop_0516 9 := by
  have hU : rowTransform_0516.det.natAbs = 1 := by
    have hdet : rowTransform_0516.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Aggregate.bottomBound.transformTopRows rowTransform_0516 hU
  have hcols := hrows.permuteColumns columnPerm_0516
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0516 MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Base.explicitTop)
          columnPerm_0516 = targetTop_0516 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0516 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 4 5 5 6)) 9 := by
  have htop : targetTop_0516 =
      topOfPattern (R := ℤ) (angle6 0 1 4 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0516

/-- Explicit target top block for canonical pattern `(0, 1, 4, 5, 5, 7)`. -/
def targetTop_0517 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0517 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0517 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0517 : BottomDetBound targetTop_0517 9 := by
  have hU : rowTransform_0517.det.natAbs = 1 := by
    have hdet : rowTransform_0517.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Aggregate.bottomBound.transformTopRows rowTransform_0517 hU
  have hcols := hrows.permuteColumns columnPerm_0517
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0517 MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Base.explicitTop)
          columnPerm_0517 = targetTop_0517 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0517 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 4 5 5 7)) 9 := by
  have htop : targetTop_0517 =
      topOfPattern (R := ℤ) (angle6 0 1 4 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0517

/-- Explicit target top block for canonical pattern `(0, 1, 4, 5, 6, 6)`. -/
def targetTop_0518 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0518 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     1, 0, 1]

def columnPerm_0518 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 4, 5, 1, 2]
  invFun := ![0, 4, 5, 1, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0518 : BottomDetBound targetTop_0518 9 := by
  have hU : rowTransform_0518.det.natAbs = 1 := by
    have hdet : rowTransform_0518.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate.bottomBound.transformTopRows rowTransform_0518 hU
  have hcols := hrows.permuteColumns columnPerm_0518
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0518 MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Base.explicitTop)
          columnPerm_0518 = targetTop_0518 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0518 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 4 5 6 6)) 9 := by
  have htop : targetTop_0518 =
      topOfPattern (R := ℤ) (angle6 0 1 4 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0518

/-- Explicit target top block for canonical pattern `(0, 1, 4, 5, 6, 7)`. -/
def targetTop_0519 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0519 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0519 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0519 : BottomDetBound targetTop_0519 9 := by
  have hU : rowTransform_0519.det.natAbs = 1 := by
    have hdet : rowTransform_0519.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R017.Aggregate.bottomBound.transformTopRows rowTransform_0519 hU
  have hcols := hrows.permuteColumns columnPerm_0519
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0519 MainTheory.Generated.BinaryBetaSixKernel.Representative.R017.Base.explicitTop)
          columnPerm_0519 = targetTop_0519 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0519 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 4 5 6 7)) 9 := by
  have htop : targetTop_0519 =
      topOfPattern (R := ℤ) (angle6 0 1 4 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0519

/-- Explicit target top block for canonical pattern `(0, 1, 4, 5, 7, 7)`. -/
def targetTop_0520 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0520 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 0;
     1, 0, 1]

def columnPerm_0520 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 4, 5, 1, 2]
  invFun := ![0, 4, 5, 1, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0520 : BottomDetBound targetTop_0520 9 := by
  have hU : rowTransform_0520.det.natAbs = 1 := by
    have hdet : rowTransform_0520.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate.bottomBound.transformTopRows rowTransform_0520 hU
  have hcols := hrows.permuteColumns columnPerm_0520
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0520 MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Base.explicitTop)
          columnPerm_0520 = targetTop_0520 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0520 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 4 5 7 7)) 9 := by
  have htop : targetTop_0520 =
      topOfPattern (R := ℤ) (angle6 0 1 4 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0520

/-- Explicit target top block for canonical pattern `(0, 1, 4, 6, 6, 6)`. -/
def targetTop_0521 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 0;
     0, 0, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0521 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     1, 0, 1]

def columnPerm_0521 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0521 : BottomDetBound targetTop_0521 9 := by
  have hU : rowTransform_0521.det.natAbs = 1 := by
    have hdet : rowTransform_0521.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0521 hU
  have hcols := hrows.permuteColumns columnPerm_0521
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0521 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0521 = targetTop_0521 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0521 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 4 6 6 6)) 9 := by
  have htop : targetTop_0521 =
      topOfPattern (R := ℤ) (angle6 0 1 4 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0521

/-- Explicit target top block for canonical pattern `(0, 1, 4, 6, 6, 7)`. -/
def targetTop_0522 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0522 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     1, 0, 1]

def columnPerm_0522 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 5, 1, 2, 4]
  invFun := ![0, 3, 4, 1, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0522 : BottomDetBound targetTop_0522 9 := by
  have hU : rowTransform_0522.det.natAbs = 1 := by
    have hdet : rowTransform_0522.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0522 hU
  have hcols := hrows.permuteColumns columnPerm_0522
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0522 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0522 = targetTop_0522 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0522 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 4 6 6 7)) 9 := by
  have htop : targetTop_0522 =
      topOfPattern (R := ℤ) (angle6 0 1 4 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0522

/-- Explicit target top block for canonical pattern `(0, 1, 4, 6, 7, 7)`. -/
def targetTop_0523 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0523 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 1, 1]

def columnPerm_0523 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0523 : BottomDetBound targetTop_0523 9 := by
  have hU : rowTransform_0523.det.natAbs = 1 := by
    have hdet : rowTransform_0523.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Aggregate.bottomBound.transformTopRows rowTransform_0523 hU
  have hcols := hrows.permuteColumns columnPerm_0523
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0523 MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Base.explicitTop)
          columnPerm_0523 = targetTop_0523 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0523 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 4 6 7 7)) 9 := by
  have htop : targetTop_0523 =
      topOfPattern (R := ℤ) (angle6 0 1 4 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0523

/-- Explicit target top block for canonical pattern `(0, 1, 4, 7, 7, 7)`. -/
def targetTop_0524 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0524 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 0;
     1, 0, 1]

def columnPerm_0524 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0524 : BottomDetBound targetTop_0524 9 := by
  have hU : rowTransform_0524.det.natAbs = 1 := by
    have hdet : rowTransform_0524.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0524 hU
  have hcols := hrows.permuteColumns columnPerm_0524
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0524 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0524 = targetTop_0524 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0524 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 4 7 7 7)) 9 := by
  have htop : targetTop_0524 =
      topOfPattern (R := ℤ) (angle6 0 1 4 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0524

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 5, 5, 5, 5)`. -/
def targetTop_0525 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0525 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0525 :
    TopRowRelation targetTop_0525 relationCoefficients_0525 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0525, relationCoefficients_0525, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0525 : BottomDetBound targetTop_0525 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0525

theorem canonicalBound_0525 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 5 5 5 5)) 9 := by
  have htop : targetTop_0525 =
      topOfPattern (R := ℤ) (angle6 0 1 5 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0525

/-- Explicit target top block for canonical pattern `(0, 1, 5, 5, 5, 6)`. -/
def targetTop_0526 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0526 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 0, 1;
     1, 0, 1]

def columnPerm_0526 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 3, 5]
  invFun := ![0, 2, 3, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0526 : BottomDetBound targetTop_0526 9 := by
  have hU : rowTransform_0526.det.natAbs = 1 := by
    have hdet : rowTransform_0526.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0526 hU
  have hcols := hrows.permuteColumns columnPerm_0526
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0526 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0526 = targetTop_0526 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0526 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 5 5 5 6)) 9 := by
  have htop : targetTop_0526 =
      topOfPattern (R := ℤ) (angle6 0 1 5 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0526

/-- Explicit target top block for canonical pattern `(0, 1, 5, 5, 5, 7)`. -/
def targetTop_0527 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0527 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 0, 1;
     1, 0, 1]

def columnPerm_0527 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 3, 5]
  invFun := ![0, 2, 3, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0527 : BottomDetBound targetTop_0527 9 := by
  have hU : rowTransform_0527.det.natAbs = 1 := by
    have hdet : rowTransform_0527.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0527 hU
  have hcols := hrows.permuteColumns columnPerm_0527
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0527 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0527 = targetTop_0527 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0527 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 5 5 5 7)) 9 := by
  have htop : targetTop_0527 =
      topOfPattern (R := ℤ) (angle6 0 1 5 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0527

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard032
