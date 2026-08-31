-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard051

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(1, 1, 1, 1, 5, 7)`. -/
def targetTop_0816 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0816 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0816 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0816 : BottomDetBound targetTop_0816 9 := by
  have hU : rowTransform_0816.det.natAbs = 1 := by
    have hdet : rowTransform_0816.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_0816 hU
  have hcols := hrows.permuteColumns columnPerm_0816
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0816 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_0816 = targetTop_0816 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0816 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 1 5 7)) 9 := by
  have htop : targetTop_0816 =
      topOfPattern (R := ℤ) (angle6 1 1 1 1 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0816

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 1, 1, 6, 6)`. -/
def targetTop_0817 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0817 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0817 :
    TopRowRelation targetTop_0817 relationCoefficients_0817 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0817, relationCoefficients_0817, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0817 : BottomDetBound targetTop_0817 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0817

theorem canonicalBound_0817 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 1 6 6)) 9 := by
  have htop : targetTop_0817 =
      topOfPattern (R := ℤ) (angle6 1 1 1 1 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0817

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 1, 1, 6, 7)`. -/
def targetTop_0818 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0818 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0818 :
    TopRowRelation targetTop_0818 relationCoefficients_0818 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0818, relationCoefficients_0818, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0818 : BottomDetBound targetTop_0818 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0818

theorem canonicalBound_0818 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 1 6 7)) 9 := by
  have htop : targetTop_0818 =
      topOfPattern (R := ℤ) (angle6 1 1 1 1 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0818

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 1, 1, 7, 7)`. -/
def targetTop_0819 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0819 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0819 :
    TopRowRelation targetTop_0819 relationCoefficients_0819 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0819, relationCoefficients_0819, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0819 : BottomDetBound targetTop_0819 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0819

theorem canonicalBound_0819 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 1 7 7)) 9 := by
  have htop : targetTop_0819 =
      topOfPattern (R := ℤ) (angle6 1 1 1 1 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0819

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 1, 2, 2, 2)`. -/
def targetTop_0820 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0820 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0820 :
    TopRowRelation targetTop_0820 relationCoefficients_0820 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0820, relationCoefficients_0820, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0820 : BottomDetBound targetTop_0820 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0820

theorem canonicalBound_0820 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 2 2 2)) 9 := by
  have htop : targetTop_0820 =
      topOfPattern (R := ℤ) (angle6 1 1 1 2 2 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0820

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 1, 2, 2, 3)`. -/
def targetTop_0821 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0821 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0821 :
    TopRowRelation targetTop_0821 relationCoefficients_0821 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0821, relationCoefficients_0821, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0821 : BottomDetBound targetTop_0821 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0821

theorem canonicalBound_0821 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 2 2 3)) 9 := by
  have htop : targetTop_0821 =
      topOfPattern (R := ℤ) (angle6 1 1 1 2 2 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0821

/-- Explicit target top block for canonical pattern `(1, 1, 1, 2, 2, 4)`. -/
def targetTop_0822 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0822 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0822 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0822 : BottomDetBound targetTop_0822 9 := by
  have hU : rowTransform_0822.det.natAbs = 1 := by
    have hdet : rowTransform_0822.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0822 hU
  have hcols := hrows.permuteColumns columnPerm_0822
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0822 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0822 = targetTop_0822 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0822 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 2 2 4)) 9 := by
  have htop : targetTop_0822 =
      topOfPattern (R := ℤ) (angle6 1 1 1 2 2 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0822

/-- Explicit target top block for canonical pattern `(1, 1, 1, 2, 2, 5)`. -/
def targetTop_0823 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0823 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0823 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0823 : BottomDetBound targetTop_0823 9 := by
  have hU : rowTransform_0823.det.natAbs = 1 := by
    have hdet : rowTransform_0823.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0823 hU
  have hcols := hrows.permuteColumns columnPerm_0823
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0823 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0823 = targetTop_0823 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0823 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 2 2 5)) 9 := by
  have htop : targetTop_0823 =
      topOfPattern (R := ℤ) (angle6 1 1 1 2 2 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0823

/-- Explicit target top block for canonical pattern `(1, 1, 1, 2, 2, 6)`. -/
def targetTop_0824 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0824 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0824 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0824 : BottomDetBound targetTop_0824 9 := by
  have hU : rowTransform_0824.det.natAbs = 1 := by
    have hdet : rowTransform_0824.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0824 hU
  have hcols := hrows.permuteColumns columnPerm_0824
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0824 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0824 = targetTop_0824 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0824 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 2 2 6)) 9 := by
  have htop : targetTop_0824 =
      topOfPattern (R := ℤ) (angle6 1 1 1 2 2 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0824

/-- Explicit target top block for canonical pattern `(1, 1, 1, 2, 2, 7)`. -/
def targetTop_0825 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0825 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0825 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0825 : BottomDetBound targetTop_0825 9 := by
  have hU : rowTransform_0825.det.natAbs = 1 := by
    have hdet : rowTransform_0825.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0825 hU
  have hcols := hrows.permuteColumns columnPerm_0825
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0825 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0825 = targetTop_0825 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0825 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 2 2 7)) 9 := by
  have htop : targetTop_0825 =
      topOfPattern (R := ℤ) (angle6 1 1 1 2 2 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0825

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 1, 2, 3, 3)`. -/
def targetTop_0826 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0826 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0826 :
    TopRowRelation targetTop_0826 relationCoefficients_0826 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0826, relationCoefficients_0826, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0826 : BottomDetBound targetTop_0826 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0826

theorem canonicalBound_0826 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 2 3 3)) 9 := by
  have htop : targetTop_0826 =
      topOfPattern (R := ℤ) (angle6 1 1 1 2 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0826

/-- Explicit target top block for canonical pattern `(1, 1, 1, 2, 3, 4)`. -/
def targetTop_0827 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 1, 0;
     0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0827 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0827 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0827 : BottomDetBound targetTop_0827 9 := by
  have hU : rowTransform_0827.det.natAbs = 1 := by
    have hdet : rowTransform_0827.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_0827 hU
  have hcols := hrows.permuteColumns columnPerm_0827
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0827 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_0827 = targetTop_0827 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0827 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 2 3 4)) 9 := by
  have htop : targetTop_0827 =
      topOfPattern (R := ℤ) (angle6 1 1 1 2 3 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0827

/-- Explicit target top block for canonical pattern `(1, 1, 1, 2, 3, 5)`. -/
def targetTop_0828 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0828 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0828 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0828 : BottomDetBound targetTop_0828 9 := by
  have hU : rowTransform_0828.det.natAbs = 1 := by
    have hdet : rowTransform_0828.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_0828 hU
  have hcols := hrows.permuteColumns columnPerm_0828
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0828 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_0828 = targetTop_0828 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0828 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 2 3 5)) 9 := by
  have htop : targetTop_0828 =
      topOfPattern (R := ℤ) (angle6 1 1 1 2 3 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0828

/-- Explicit target top block for canonical pattern `(1, 1, 1, 2, 3, 6)`. -/
def targetTop_0829 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 1, 0;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0829 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0829 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0829 : BottomDetBound targetTop_0829 9 := by
  have hU : rowTransform_0829.det.natAbs = 1 := by
    have hdet : rowTransform_0829.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_0829 hU
  have hcols := hrows.permuteColumns columnPerm_0829
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0829 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_0829 = targetTop_0829 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0829 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 2 3 6)) 9 := by
  have htop : targetTop_0829 =
      topOfPattern (R := ℤ) (angle6 1 1 1 2 3 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0829

/-- Explicit target top block for canonical pattern `(1, 1, 1, 2, 3, 7)`. -/
def targetTop_0830 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0830 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0830 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0830 : BottomDetBound targetTop_0830 9 := by
  have hU : rowTransform_0830.det.natAbs = 1 := by
    have hdet : rowTransform_0830.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_0830 hU
  have hcols := hrows.permuteColumns columnPerm_0830
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0830 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_0830 = targetTop_0830 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0830 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 2 3 7)) 9 := by
  have htop : targetTop_0830 =
      topOfPattern (R := ℤ) (angle6 1 1 1 2 3 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0830

/-- Explicit target top block for canonical pattern `(1, 1, 1, 2, 4, 4)`. -/
def targetTop_0831 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0831 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_0831 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0831 : BottomDetBound targetTop_0831 9 := by
  have hU : rowTransform_0831.det.natAbs = 1 := by
    have hdet : rowTransform_0831.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0831 hU
  have hcols := hrows.permuteColumns columnPerm_0831
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0831 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0831 = targetTop_0831 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0831 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 2 4 4)) 9 := by
  have htop : targetTop_0831 =
      topOfPattern (R := ℤ) (angle6 1 1 1 2 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0831

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard051
