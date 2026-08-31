-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard048

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(0, 4, 6, 6, 7, 7)`. -/
def targetTop_0768 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0768 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 0;
     1, 1, 1]

def columnPerm_0768 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0768 : BottomDetBound targetTop_0768 9 := by
  have hU : rowTransform_0768.det.natAbs = 1 := by
    have hdet : rowTransform_0768.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0768 hU
  have hcols := hrows.permuteColumns columnPerm_0768
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0768 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0768 = targetTop_0768 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0768 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 4 6 6 7 7)) 9 := by
  have htop : targetTop_0768 =
      topOfPattern (R := ℤ) (angle6 0 4 6 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0768

/-- Explicit target top block for canonical pattern `(0, 4, 6, 7, 7, 7)`. -/
def targetTop_0769 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0769 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 0, 1;
     1, 1, 1]

def columnPerm_0769 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0769 : BottomDetBound targetTop_0769 9 := by
  have hU : rowTransform_0769.det.natAbs = 1 := by
    have hdet : rowTransform_0769.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0769 hU
  have hcols := hrows.permuteColumns columnPerm_0769
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0769 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0769 = targetTop_0769 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0769 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 4 6 7 7 7)) 9 := by
  have htop : targetTop_0769 =
      topOfPattern (R := ℤ) (angle6 0 4 6 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0769

/-- Explicit rank-deficient target for canonical pattern `(0, 4, 7, 7, 7, 7)`. -/
def targetTop_0770 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0770 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0770 :
    TopRowRelation targetTop_0770 relationCoefficients_0770 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0770, relationCoefficients_0770, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0770 : BottomDetBound targetTop_0770 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0770

theorem canonicalBound_0770 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 4 7 7 7 7)) 9 := by
  have htop : targetTop_0770 =
      topOfPattern (R := ℤ) (angle6 0 4 7 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0770

/-- Explicit rank-deficient target for canonical pattern `(0, 5, 5, 5, 5, 5)`. -/
def targetTop_0771 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0771 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0771 :
    TopRowRelation targetTop_0771 relationCoefficients_0771 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0771, relationCoefficients_0771, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0771 : BottomDetBound targetTop_0771 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0771

theorem canonicalBound_0771 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 5 5 5 5 5)) 9 := by
  have htop : targetTop_0771 =
      topOfPattern (R := ℤ) (angle6 0 5 5 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0771

/-- Explicit rank-deficient target for canonical pattern `(0, 5, 5, 5, 5, 6)`. -/
def targetTop_0772 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0772 : Fin 3 → ℤ :=
  ![1, 1, (-1)]

theorem topRelation_0772 :
    TopRowRelation targetTop_0772 relationCoefficients_0772 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0772, relationCoefficients_0772, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0772 : BottomDetBound targetTop_0772 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0772

theorem canonicalBound_0772 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 5 5 5 5 6)) 9 := by
  have htop : targetTop_0772 =
      topOfPattern (R := ℤ) (angle6 0 5 5 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0772

/-- Explicit rank-deficient target for canonical pattern `(0, 5, 5, 5, 5, 7)`. -/
def targetTop_0773 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0773 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0773 :
    TopRowRelation targetTop_0773 relationCoefficients_0773 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0773, relationCoefficients_0773, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0773 : BottomDetBound targetTop_0773 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0773

theorem canonicalBound_0773 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 5 5 5 5 7)) 9 := by
  have htop : targetTop_0773 =
      topOfPattern (R := ℤ) (angle6 0 5 5 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0773

/-- Explicit rank-deficient target for canonical pattern `(0, 5, 5, 5, 6, 6)`. -/
def targetTop_0774 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0774 : Fin 3 → ℤ :=
  ![1, 1, (-1)]

theorem topRelation_0774 :
    TopRowRelation targetTop_0774 relationCoefficients_0774 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0774, relationCoefficients_0774, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0774 : BottomDetBound targetTop_0774 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0774

theorem canonicalBound_0774 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 5 5 5 6 6)) 9 := by
  have htop : targetTop_0774 =
      topOfPattern (R := ℤ) (angle6 0 5 5 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0774

/-- Explicit target top block for canonical pattern `(0, 5, 5, 5, 6, 7)`. -/
def targetTop_0775 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0775 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 1;
     1, 1, 1]

def columnPerm_0775 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0775 : BottomDetBound targetTop_0775 9 := by
  have hU : rowTransform_0775.det.natAbs = 1 := by
    have hdet : rowTransform_0775.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0775 hU
  have hcols := hrows.permuteColumns columnPerm_0775
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0775 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0775 = targetTop_0775 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0775 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 5 5 5 6 7)) 9 := by
  have htop : targetTop_0775 =
      topOfPattern (R := ℤ) (angle6 0 5 5 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0775

/-- Explicit rank-deficient target for canonical pattern `(0, 5, 5, 5, 7, 7)`. -/
def targetTop_0776 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0776 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0776 :
    TopRowRelation targetTop_0776 relationCoefficients_0776 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0776, relationCoefficients_0776, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0776 : BottomDetBound targetTop_0776 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0776

theorem canonicalBound_0776 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 5 5 5 7 7)) 9 := by
  have htop : targetTop_0776 =
      topOfPattern (R := ℤ) (angle6 0 5 5 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0776

/-- Explicit rank-deficient target for canonical pattern `(0, 5, 5, 6, 6, 6)`. -/
def targetTop_0777 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0777 : Fin 3 → ℤ :=
  ![1, 1, (-1)]

theorem topRelation_0777 :
    TopRowRelation targetTop_0777 relationCoefficients_0777 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0777, relationCoefficients_0777, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0777 : BottomDetBound targetTop_0777 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0777

theorem canonicalBound_0777 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 5 5 6 6 6)) 9 := by
  have htop : targetTop_0777 =
      topOfPattern (R := ℤ) (angle6 0 5 5 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0777

/-- Explicit target top block for canonical pattern `(0, 5, 5, 6, 6, 7)`. -/
def targetTop_0778 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0778 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 1;
     1, 1, 1]

def columnPerm_0778 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0778 : BottomDetBound targetTop_0778 9 := by
  have hU : rowTransform_0778.det.natAbs = 1 := by
    have hdet : rowTransform_0778.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0778 hU
  have hcols := hrows.permuteColumns columnPerm_0778
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0778 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0778 = targetTop_0778 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0778 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 5 5 6 6 7)) 9 := by
  have htop : targetTop_0778 =
      topOfPattern (R := ℤ) (angle6 0 5 5 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0778

/-- Explicit target top block for canonical pattern `(0, 5, 5, 6, 7, 7)`. -/
def targetTop_0779 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0779 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 1;
     1, 1, 1]

def columnPerm_0779 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0779 : BottomDetBound targetTop_0779 9 := by
  have hU : rowTransform_0779.det.natAbs = 1 := by
    have hdet : rowTransform_0779.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0779 hU
  have hcols := hrows.permuteColumns columnPerm_0779
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0779 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0779 = targetTop_0779 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0779 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 5 5 6 7 7)) 9 := by
  have htop : targetTop_0779 =
      topOfPattern (R := ℤ) (angle6 0 5 5 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0779

/-- Explicit rank-deficient target for canonical pattern `(0, 5, 5, 7, 7, 7)`. -/
def targetTop_0780 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0780 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0780 :
    TopRowRelation targetTop_0780 relationCoefficients_0780 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0780, relationCoefficients_0780, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0780 : BottomDetBound targetTop_0780 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0780

theorem canonicalBound_0780 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 5 5 7 7 7)) 9 := by
  have htop : targetTop_0780 =
      topOfPattern (R := ℤ) (angle6 0 5 5 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0780

/-- Explicit rank-deficient target for canonical pattern `(0, 5, 6, 6, 6, 6)`. -/
def targetTop_0781 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0781 : Fin 3 → ℤ :=
  ![1, 1, (-1)]

theorem topRelation_0781 :
    TopRowRelation targetTop_0781 relationCoefficients_0781 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0781, relationCoefficients_0781, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0781 : BottomDetBound targetTop_0781 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0781

theorem canonicalBound_0781 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 5 6 6 6 6)) 9 := by
  have htop : targetTop_0781 =
      topOfPattern (R := ℤ) (angle6 0 5 6 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0781

/-- Explicit target top block for canonical pattern `(0, 5, 6, 6, 6, 7)`. -/
def targetTop_0782 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0782 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 1;
     1, 1, 1]

def columnPerm_0782 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 3, 5]
  invFun := ![0, 2, 3, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0782 : BottomDetBound targetTop_0782 9 := by
  have hU : rowTransform_0782.det.natAbs = 1 := by
    have hdet : rowTransform_0782.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0782 hU
  have hcols := hrows.permuteColumns columnPerm_0782
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0782 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0782 = targetTop_0782 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0782 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 5 6 6 6 7)) 9 := by
  have htop : targetTop_0782 =
      topOfPattern (R := ℤ) (angle6 0 5 6 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0782

/-- Explicit target top block for canonical pattern `(0, 5, 6, 6, 7, 7)`. -/
def targetTop_0783 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0783 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 1, 0;
     1, 1, 1]

def columnPerm_0783 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0783 : BottomDetBound targetTop_0783 9 := by
  have hU : rowTransform_0783.det.natAbs = 1 := by
    have hdet : rowTransform_0783.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0783 hU
  have hcols := hrows.permuteColumns columnPerm_0783
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0783 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0783 = targetTop_0783 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0783 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 5 6 6 7 7)) 9 := by
  have htop : targetTop_0783 =
      topOfPattern (R := ℤ) (angle6 0 5 6 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0783

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard048
