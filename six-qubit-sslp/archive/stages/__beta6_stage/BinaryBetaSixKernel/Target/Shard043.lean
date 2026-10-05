-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R026.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R027.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard043

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(0, 3, 3, 4, 6, 6)`. -/
def targetTop_0688 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 0;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0688 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, 0;
     0, 1, 1]

def columnPerm_0688 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0688 : BottomDetBound targetTop_0688 9 := by
  have hU : rowTransform_0688.det.natAbs = 1 := by
    have hdet : rowTransform_0688.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0688 hU
  have hcols := hrows.permuteColumns columnPerm_0688
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0688 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0688 = targetTop_0688 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0688 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 3 4 6 6)) 9 := by
  have htop : targetTop_0688 =
      topOfPattern (R := ℤ) (angle6 0 3 3 4 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0688

/-- Explicit target top block for canonical pattern `(0, 3, 3, 4, 6, 7)`. -/
def targetTop_0689 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 1;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0689 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 0, 1;
     0, 1, 1]

def columnPerm_0689 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 5, 4]
  invFun := ![0, 1, 2, 3, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0689 : BottomDetBound targetTop_0689 9 := by
  have hU : rowTransform_0689.det.natAbs = 1 := by
    have hdet : rowTransform_0689.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0689 hU
  have hcols := hrows.permuteColumns columnPerm_0689
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0689 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0689 = targetTop_0689 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0689 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 3 4 6 7)) 9 := by
  have htop : targetTop_0689 =
      topOfPattern (R := ℤ) (angle6 0 3 3 4 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0689

/-- Explicit rank-deficient target for canonical pattern `(0, 3, 3, 4, 7, 7)`. -/
def targetTop_0690 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 1, 1;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0690 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0690 :
    TopRowRelation targetTop_0690 relationCoefficients_0690 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0690, relationCoefficients_0690, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0690 : BottomDetBound targetTop_0690 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0690

theorem canonicalBound_0690 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 3 4 7 7)) 9 := by
  have htop : targetTop_0690 =
      topOfPattern (R := ℤ) (angle6 0 3 3 4 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0690

/-- Explicit rank-deficient target for canonical pattern `(0, 3, 3, 5, 5, 5)`. -/
def targetTop_0691 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0691 : Fin 3 → ℤ :=
  ![1, (-1), (-1)]

theorem topRelation_0691 :
    TopRowRelation targetTop_0691 relationCoefficients_0691 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0691, relationCoefficients_0691, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0691 : BottomDetBound targetTop_0691 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0691

theorem canonicalBound_0691 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 3 5 5 5)) 9 := by
  have htop : targetTop_0691 =
      topOfPattern (R := ℤ) (angle6 0 3 3 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0691

/-- Explicit target top block for canonical pattern `(0, 3, 3, 5, 5, 6)`. -/
def targetTop_0692 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 0;
     0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0692 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0692 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0692 : BottomDetBound targetTop_0692 9 := by
  have hU : rowTransform_0692.det.natAbs = 1 := by
    have hdet : rowTransform_0692.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R026.Aggregate.bottomBound.transformTopRows rowTransform_0692 hU
  have hcols := hrows.permuteColumns columnPerm_0692
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0692 MainTheory.Generated.BinaryBetaSixKernel.Representative.R026.Base.explicitTop)
          columnPerm_0692 = targetTop_0692 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0692 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 3 5 5 6)) 9 := by
  have htop : targetTop_0692 =
      topOfPattern (R := ℤ) (angle6 0 3 3 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0692

/-- Explicit target top block for canonical pattern `(0, 3, 3, 5, 5, 7)`. -/
def targetTop_0693 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0693 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     1, 0, 1;
     0, 1, 1]

def columnPerm_0693 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0693 : BottomDetBound targetTop_0693 9 := by
  have hU : rowTransform_0693.det.natAbs = 1 := by
    have hdet : rowTransform_0693.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0693 hU
  have hcols := hrows.permuteColumns columnPerm_0693
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0693 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0693 = targetTop_0693 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0693 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 3 5 5 7)) 9 := by
  have htop : targetTop_0693 =
      topOfPattern (R := ℤ) (angle6 0 3 3 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0693

/-- Explicit target top block for canonical pattern `(0, 3, 3, 5, 6, 6)`. -/
def targetTop_0694 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 0;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0694 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_0694 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0694 : BottomDetBound targetTop_0694 9 := by
  have hU : rowTransform_0694.det.natAbs = 1 := by
    have hdet : rowTransform_0694.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R026.Aggregate.bottomBound.transformTopRows rowTransform_0694 hU
  have hcols := hrows.permuteColumns columnPerm_0694
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0694 MainTheory.Generated.BinaryBetaSixKernel.Representative.R026.Base.explicitTop)
          columnPerm_0694 = targetTop_0694 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0694 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 3 5 6 6)) 9 := by
  have htop : targetTop_0694 =
      topOfPattern (R := ℤ) (angle6 0 3 3 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0694

/-- Explicit target top block for canonical pattern `(0, 3, 3, 5, 6, 7)`. -/
def targetTop_0695 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 1;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0695 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0695 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0695 : BottomDetBound targetTop_0695 9 := by
  have hU : rowTransform_0695.det.natAbs = 1 := by
    have hdet : rowTransform_0695.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R027.Aggregate.bottomBound.transformTopRows rowTransform_0695 hU
  have hcols := hrows.permuteColumns columnPerm_0695
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0695 MainTheory.Generated.BinaryBetaSixKernel.Representative.R027.Base.explicitTop)
          columnPerm_0695 = targetTop_0695 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0695 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 3 5 6 7)) 9 := by
  have htop : targetTop_0695 =
      topOfPattern (R := ℤ) (angle6 0 3 3 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0695

/-- Explicit target top block for canonical pattern `(0, 3, 3, 5, 7, 7)`. -/
def targetTop_0696 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0696 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     1, 1, 0;
     0, 1, 1]

def columnPerm_0696 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0696 : BottomDetBound targetTop_0696 9 := by
  have hU : rowTransform_0696.det.natAbs = 1 := by
    have hdet : rowTransform_0696.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0696 hU
  have hcols := hrows.permuteColumns columnPerm_0696
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0696 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0696 = targetTop_0696 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0696 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 3 5 7 7)) 9 := by
  have htop : targetTop_0696 =
      topOfPattern (R := ℤ) (angle6 0 3 3 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0696

/-- Explicit rank-deficient target for canonical pattern `(0, 3, 3, 6, 6, 6)`. -/
def targetTop_0697 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 0;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0697 : Fin 3 → ℤ :=
  ![1, (-1), 1]

theorem topRelation_0697 :
    TopRowRelation targetTop_0697 relationCoefficients_0697 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0697, relationCoefficients_0697, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0697 : BottomDetBound targetTop_0697 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0697

theorem canonicalBound_0697 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 3 6 6 6)) 9 := by
  have htop : targetTop_0697 =
      topOfPattern (R := ℤ) (angle6 0 3 3 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0697

/-- Explicit target top block for canonical pattern `(0, 3, 3, 6, 6, 7)`. -/
def targetTop_0698 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0698 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 1, 1;
     0, 1, 1]

def columnPerm_0698 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0698 : BottomDetBound targetTop_0698 9 := by
  have hU : rowTransform_0698.det.natAbs = 1 := by
    have hdet : rowTransform_0698.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0698 hU
  have hcols := hrows.permuteColumns columnPerm_0698
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0698 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0698 = targetTop_0698 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0698 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 3 6 6 7)) 9 := by
  have htop : targetTop_0698 =
      topOfPattern (R := ℤ) (angle6 0 3 3 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0698

/-- Explicit target top block for canonical pattern `(0, 3, 3, 6, 7, 7)`. -/
def targetTop_0699 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0699 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 1, 1;
     0, 1, 1]

def columnPerm_0699 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0699 : BottomDetBound targetTop_0699 9 := by
  have hU : rowTransform_0699.det.natAbs = 1 := by
    have hdet : rowTransform_0699.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0699 hU
  have hcols := hrows.permuteColumns columnPerm_0699
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0699 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0699 = targetTop_0699 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0699 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 3 6 7 7)) 9 := by
  have htop : targetTop_0699 =
      topOfPattern (R := ℤ) (angle6 0 3 3 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0699

/-- Explicit rank-deficient target for canonical pattern `(0, 3, 3, 7, 7, 7)`. -/
def targetTop_0700 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0700 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0700 :
    TopRowRelation targetTop_0700 relationCoefficients_0700 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0700, relationCoefficients_0700, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0700 : BottomDetBound targetTop_0700 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0700

theorem canonicalBound_0700 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 3 7 7 7)) 9 := by
  have htop : targetTop_0700 =
      topOfPattern (R := ℤ) (angle6 0 3 3 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0700

/-- Explicit rank-deficient target for canonical pattern `(0, 3, 4, 4, 4, 4)`. -/
def targetTop_0701 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0701 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0701 :
    TopRowRelation targetTop_0701 relationCoefficients_0701 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0701, relationCoefficients_0701, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0701 : BottomDetBound targetTop_0701 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0701

theorem canonicalBound_0701 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 4 4 4 4)) 9 := by
  have htop : targetTop_0701 =
      topOfPattern (R := ℤ) (angle6 0 3 4 4 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0701

/-- Explicit target top block for canonical pattern `(0, 3, 4, 4, 4, 5)`. -/
def targetTop_0702 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 1;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0702 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 1, 0;
     1, 0, 1]

def columnPerm_0702 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 3, 5]
  invFun := ![0, 2, 3, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0702 : BottomDetBound targetTop_0702 9 := by
  have hU : rowTransform_0702.det.natAbs = 1 := by
    have hdet : rowTransform_0702.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0702 hU
  have hcols := hrows.permuteColumns columnPerm_0702
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0702 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0702 = targetTop_0702 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0702 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 4 4 4 5)) 9 := by
  have htop : targetTop_0702 =
      topOfPattern (R := ℤ) (angle6 0 3 4 4 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0702

/-- Explicit target top block for canonical pattern `(0, 3, 4, 4, 4, 6)`. -/
def targetTop_0703 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0703 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 1, 1;
     1, 0, 1]

def columnPerm_0703 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 3, 5]
  invFun := ![0, 2, 3, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0703 : BottomDetBound targetTop_0703 9 := by
  have hU : rowTransform_0703.det.natAbs = 1 := by
    have hdet : rowTransform_0703.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0703 hU
  have hcols := hrows.permuteColumns columnPerm_0703
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0703 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0703 = targetTop_0703 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0703 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 4 4 4 6)) 9 := by
  have htop : targetTop_0703 =
      topOfPattern (R := ℤ) (angle6 0 3 4 4 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0703

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard043
