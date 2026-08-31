-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R035.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard053

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(1, 1, 1, 3, 4, 6)`. -/
def targetTop_0848 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 0;
     0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0848 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, (-1);
     0, 1, 0;
     0, 0, 1]

def columnPerm_0848 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0848 : BottomDetBound targetTop_0848 9 := by
  have hU : rowTransform_0848.det.natAbs = 1 := by
    have hdet : rowTransform_0848.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate.bottomBound.transformTopRows rowTransform_0848 hU
  have hcols := hrows.permuteColumns columnPerm_0848
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0848 MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Base.explicitTop)
          columnPerm_0848 = targetTop_0848 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0848 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 3 4 6)) 9 := by
  have htop : targetTop_0848 =
      topOfPattern (R := ℤ) (angle6 1 1 1 3 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0848

/-- Explicit target top block for canonical pattern `(1, 1, 1, 3, 4, 7)`. -/
def targetTop_0849 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 1;
     0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0849 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0849 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0849 : BottomDetBound targetTop_0849 9 := by
  have hU : rowTransform_0849.det.natAbs = 1 := by
    have hdet : rowTransform_0849.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate.bottomBound.transformTopRows rowTransform_0849 hU
  have hcols := hrows.permuteColumns columnPerm_0849
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0849 MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Base.explicitTop)
          columnPerm_0849 = targetTop_0849 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0849 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 3 4 7)) 9 := by
  have htop : targetTop_0849 =
      topOfPattern (R := ℤ) (angle6 1 1 1 3 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0849

/-- Explicit target top block for canonical pattern `(1, 1, 1, 3, 5, 5)`. -/
def targetTop_0850 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0850 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 0, 1;
     0, 1, 0]

def columnPerm_0850 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0850 : BottomDetBound targetTop_0850 9 := by
  have hU : rowTransform_0850.det.natAbs = 1 := by
    have hdet : rowTransform_0850.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0850 hU
  have hcols := hrows.permuteColumns columnPerm_0850
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0850 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0850 = targetTop_0850 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0850 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 3 5 5)) 9 := by
  have htop : targetTop_0850 =
      topOfPattern (R := ℤ) (angle6 1 1 1 3 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0850

/-- Explicit target top block for canonical pattern `(1, 1, 1, 3, 5, 6)`. -/
def targetTop_0851 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 0;
     0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0851 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0851 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0851 : BottomDetBound targetTop_0851 9 := by
  have hU : rowTransform_0851.det.natAbs = 1 := by
    have hdet : rowTransform_0851.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R035.Aggregate.bottomBound.transformTopRows rowTransform_0851 hU
  have hcols := hrows.permuteColumns columnPerm_0851
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0851 MainTheory.Generated.BinaryBetaSixKernel.Representative.R035.Base.explicitTop)
          columnPerm_0851 = targetTop_0851 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0851 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 3 5 6)) 9 := by
  have htop : targetTop_0851 =
      topOfPattern (R := ℤ) (angle6 1 1 1 3 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0851

/-- Explicit target top block for canonical pattern `(1, 1, 1, 3, 5, 7)`. -/
def targetTop_0852 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0852 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0852 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0852 : BottomDetBound targetTop_0852 9 := by
  have hU : rowTransform_0852.det.natAbs = 1 := by
    have hdet : rowTransform_0852.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate.bottomBound.transformTopRows rowTransform_0852 hU
  have hcols := hrows.permuteColumns columnPerm_0852
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0852 MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Base.explicitTop)
          columnPerm_0852 = targetTop_0852 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0852 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 3 5 7)) 9 := by
  have htop : targetTop_0852 =
      topOfPattern (R := ℤ) (angle6 1 1 1 3 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0852

/-- Explicit target top block for canonical pattern `(1, 1, 1, 3, 6, 6)`. -/
def targetTop_0853 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 0;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0853 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 1;
     0, 1, 0]

def columnPerm_0853 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0853 : BottomDetBound targetTop_0853 9 := by
  have hU : rowTransform_0853.det.natAbs = 1 := by
    have hdet : rowTransform_0853.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0853 hU
  have hcols := hrows.permuteColumns columnPerm_0853
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0853 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0853 = targetTop_0853 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0853 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 3 6 6)) 9 := by
  have htop : targetTop_0853 =
      topOfPattern (R := ℤ) (angle6 1 1 1 3 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0853

/-- Explicit target top block for canonical pattern `(1, 1, 1, 3, 6, 7)`. -/
def targetTop_0854 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0854 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 1;
     0, 1, 0]

def columnPerm_0854 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0854 : BottomDetBound targetTop_0854 9 := by
  have hU : rowTransform_0854.det.natAbs = 1 := by
    have hdet : rowTransform_0854.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_0854 hU
  have hcols := hrows.permuteColumns columnPerm_0854
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0854 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_0854 = targetTop_0854 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0854 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 3 6 7)) 9 := by
  have htop : targetTop_0854 =
      topOfPattern (R := ℤ) (angle6 1 1 1 3 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0854

/-- Explicit target top block for canonical pattern `(1, 1, 1, 3, 7, 7)`. -/
def targetTop_0855 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0855 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 1, 1;
     0, 1, 0]

def columnPerm_0855 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0855 : BottomDetBound targetTop_0855 9 := by
  have hU : rowTransform_0855.det.natAbs = 1 := by
    have hdet : rowTransform_0855.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0855 hU
  have hcols := hrows.permuteColumns columnPerm_0855
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0855 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0855 = targetTop_0855 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0855 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 3 7 7)) 9 := by
  have htop : targetTop_0855 =
      topOfPattern (R := ℤ) (angle6 1 1 1 3 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0855

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 1, 4, 4, 4)`. -/
def targetTop_0856 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0856 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0856 :
    TopRowRelation targetTop_0856 relationCoefficients_0856 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0856, relationCoefficients_0856, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0856 : BottomDetBound targetTop_0856 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0856

theorem canonicalBound_0856 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 4 4 4)) 9 := by
  have htop : targetTop_0856 =
      topOfPattern (R := ℤ) (angle6 1 1 1 4 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0856

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 1, 4, 4, 5)`. -/
def targetTop_0857 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0857 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0857 :
    TopRowRelation targetTop_0857 relationCoefficients_0857 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0857, relationCoefficients_0857, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0857 : BottomDetBound targetTop_0857 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0857

theorem canonicalBound_0857 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 4 4 5)) 9 := by
  have htop : targetTop_0857 =
      topOfPattern (R := ℤ) (angle6 1 1 1 4 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0857

/-- Explicit target top block for canonical pattern `(1, 1, 1, 4, 4, 6)`. -/
def targetTop_0858 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0858 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0858 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0858 : BottomDetBound targetTop_0858 9 := by
  have hU : rowTransform_0858.det.natAbs = 1 := by
    have hdet : rowTransform_0858.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0858 hU
  have hcols := hrows.permuteColumns columnPerm_0858
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0858 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0858 = targetTop_0858 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0858 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 4 4 6)) 9 := by
  have htop : targetTop_0858 =
      topOfPattern (R := ℤ) (angle6 1 1 1 4 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0858

/-- Explicit target top block for canonical pattern `(1, 1, 1, 4, 4, 7)`. -/
def targetTop_0859 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0859 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0859 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0859 : BottomDetBound targetTop_0859 9 := by
  have hU : rowTransform_0859.det.natAbs = 1 := by
    have hdet : rowTransform_0859.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0859 hU
  have hcols := hrows.permuteColumns columnPerm_0859
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0859 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0859 = targetTop_0859 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0859 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 4 4 7)) 9 := by
  have htop : targetTop_0859 =
      topOfPattern (R := ℤ) (angle6 1 1 1 4 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0859

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 1, 4, 5, 5)`. -/
def targetTop_0860 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0860 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0860 :
    TopRowRelation targetTop_0860 relationCoefficients_0860 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0860, relationCoefficients_0860, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0860 : BottomDetBound targetTop_0860 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0860

theorem canonicalBound_0860 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 4 5 5)) 9 := by
  have htop : targetTop_0860 =
      topOfPattern (R := ℤ) (angle6 1 1 1 4 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0860

/-- Explicit target top block for canonical pattern `(1, 1, 1, 4, 5, 6)`. -/
def targetTop_0861 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0861 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0861 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0861 : BottomDetBound targetTop_0861 9 := by
  have hU : rowTransform_0861.det.natAbs = 1 := by
    have hdet : rowTransform_0861.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_0861 hU
  have hcols := hrows.permuteColumns columnPerm_0861
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0861 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_0861 = targetTop_0861 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0861 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 4 5 6)) 9 := by
  have htop : targetTop_0861 =
      topOfPattern (R := ℤ) (angle6 1 1 1 4 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0861

/-- Explicit target top block for canonical pattern `(1, 1, 1, 4, 5, 7)`. -/
def targetTop_0862 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0862 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0862 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0862 : BottomDetBound targetTop_0862 9 := by
  have hU : rowTransform_0862.det.natAbs = 1 := by
    have hdet : rowTransform_0862.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_0862 hU
  have hcols := hrows.permuteColumns columnPerm_0862
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0862 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_0862 = targetTop_0862 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0862 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 4 5 7)) 9 := by
  have htop : targetTop_0862 =
      topOfPattern (R := ℤ) (angle6 1 1 1 4 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0862

/-- Explicit target top block for canonical pattern `(1, 1, 1, 4, 6, 6)`. -/
def targetTop_0863 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0863 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 1, 1]

def columnPerm_0863 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0863 : BottomDetBound targetTop_0863 9 := by
  have hU : rowTransform_0863.det.natAbs = 1 := by
    have hdet : rowTransform_0863.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0863 hU
  have hcols := hrows.permuteColumns columnPerm_0863
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0863 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0863 = targetTop_0863 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0863 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 4 6 6)) 9 := by
  have htop : targetTop_0863 =
      topOfPattern (R := ℤ) (angle6 1 1 1 4 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0863

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard053
