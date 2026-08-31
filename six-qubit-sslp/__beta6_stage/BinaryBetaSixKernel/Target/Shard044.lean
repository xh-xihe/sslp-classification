-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R015.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R022.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R024.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard044

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit rank-deficient target for canonical pattern `(0, 3, 4, 4, 4, 7)`. -/
def targetTop_0704 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 1;
     0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0704 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0704 :
    TopRowRelation targetTop_0704 relationCoefficients_0704 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0704, relationCoefficients_0704, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0704 : BottomDetBound targetTop_0704 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0704

theorem canonicalBound_0704 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 4 4 4 7)) 9 := by
  have htop : targetTop_0704 =
      topOfPattern (R := ℤ) (angle6 0 3 4 4 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0704

/-- Explicit target top block for canonical pattern `(0, 3, 4, 4, 5, 5)`. -/
def targetTop_0705 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 1, 1;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0705 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 0, 1;
     1, 1, 0]

def columnPerm_0705 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0705 : BottomDetBound targetTop_0705 9 := by
  have hU : rowTransform_0705.det.natAbs = 1 := by
    have hdet : rowTransform_0705.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0705 hU
  have hcols := hrows.permuteColumns columnPerm_0705
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0705 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0705 = targetTop_0705 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0705 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 4 4 5 5)) 9 := by
  have htop : targetTop_0705 =
      topOfPattern (R := ℤ) (angle6 0 3 4 4 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0705

/-- Explicit target top block for canonical pattern `(0, 3, 4, 4, 5, 6)`. -/
def targetTop_0706 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 1, 0;
     0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0706 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_0706 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0706 : BottomDetBound targetTop_0706 9 := by
  have hU : rowTransform_0706.det.natAbs = 1 := by
    have hdet : rowTransform_0706.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R015.Aggregate.bottomBound.transformTopRows rowTransform_0706 hU
  have hcols := hrows.permuteColumns columnPerm_0706
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0706 MainTheory.Generated.BinaryBetaSixKernel.Representative.R015.Base.explicitTop)
          columnPerm_0706 = targetTop_0706 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0706 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 4 4 5 6)) 9 := by
  have htop : targetTop_0706 =
      topOfPattern (R := ℤ) (angle6 0 3 4 4 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0706

/-- Explicit target top block for canonical pattern `(0, 3, 4, 4, 5, 7)`. -/
def targetTop_0707 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 1, 1;
     0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0707 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 1, 0;
     1, 0, 1]

def columnPerm_0707 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 5, 4]
  invFun := ![0, 2, 3, 1, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0707 : BottomDetBound targetTop_0707 9 := by
  have hU : rowTransform_0707.det.natAbs = 1 := by
    have hdet : rowTransform_0707.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0707 hU
  have hcols := hrows.permuteColumns columnPerm_0707
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0707 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0707 = targetTop_0707 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0707 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 4 4 5 7)) 9 := by
  have htop : targetTop_0707 =
      topOfPattern (R := ℤ) (angle6 0 3 4 4 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0707

/-- Explicit target top block for canonical pattern `(0, 3, 4, 4, 6, 6)`. -/
def targetTop_0708 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 0;
     0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0708 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 1;
     1, 1, 0]

def columnPerm_0708 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0708 : BottomDetBound targetTop_0708 9 := by
  have hU : rowTransform_0708.det.natAbs = 1 := by
    have hdet : rowTransform_0708.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0708 hU
  have hcols := hrows.permuteColumns columnPerm_0708
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0708 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0708 = targetTop_0708 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0708 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 4 4 6 6)) 9 := by
  have htop : targetTop_0708 =
      topOfPattern (R := ℤ) (angle6 0 3 4 4 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0708

/-- Explicit target top block for canonical pattern `(0, 3, 4, 4, 6, 7)`. -/
def targetTop_0709 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 1;
     0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0709 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 1, 1;
     1, 0, 1]

def columnPerm_0709 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 5, 4]
  invFun := ![0, 2, 3, 1, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0709 : BottomDetBound targetTop_0709 9 := by
  have hU : rowTransform_0709.det.natAbs = 1 := by
    have hdet : rowTransform_0709.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0709 hU
  have hcols := hrows.permuteColumns columnPerm_0709
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0709 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0709 = targetTop_0709 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0709 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 4 4 6 7)) 9 := by
  have htop : targetTop_0709 =
      topOfPattern (R := ℤ) (angle6 0 3 4 4 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0709

/-- Explicit rank-deficient target for canonical pattern `(0, 3, 4, 4, 7, 7)`. -/
def targetTop_0710 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 1, 1;
     0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0710 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0710 :
    TopRowRelation targetTop_0710 relationCoefficients_0710 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0710, relationCoefficients_0710, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0710 : BottomDetBound targetTop_0710 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0710

theorem canonicalBound_0710 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 4 4 7 7)) 9 := by
  have htop : targetTop_0710 =
      topOfPattern (R := ℤ) (angle6 0 3 4 4 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0710

/-- Explicit target top block for canonical pattern `(0, 3, 4, 5, 5, 5)`. -/
def targetTop_0711 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 1, 1;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0711 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 0;
     1, 0, 1]

def columnPerm_0711 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0711 : BottomDetBound targetTop_0711 9 := by
  have hU : rowTransform_0711.det.natAbs = 1 := by
    have hdet : rowTransform_0711.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0711 hU
  have hcols := hrows.permuteColumns columnPerm_0711
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0711 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0711 = targetTop_0711 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0711 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 4 5 5 5)) 9 := by
  have htop : targetTop_0711 =
      topOfPattern (R := ℤ) (angle6 0 3 4 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0711

/-- Explicit target top block for canonical pattern `(0, 3, 4, 5, 5, 6)`. -/
def targetTop_0712 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 1, 0;
     0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0712 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_0712 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0712 : BottomDetBound targetTop_0712 9 := by
  have hU : rowTransform_0712.det.natAbs = 1 := by
    have hdet : rowTransform_0712.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R022.Aggregate.bottomBound.transformTopRows rowTransform_0712 hU
  have hcols := hrows.permuteColumns columnPerm_0712
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0712 MainTheory.Generated.BinaryBetaSixKernel.Representative.R022.Base.explicitTop)
          columnPerm_0712 = targetTop_0712 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0712 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 4 5 5 6)) 9 := by
  have htop : targetTop_0712 =
      topOfPattern (R := ℤ) (angle6 0 3 4 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0712

/-- Explicit target top block for canonical pattern `(0, 3, 4, 5, 5, 7)`. -/
def targetTop_0713 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 1, 1;
     0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0713 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 0;
     1, 0, 1]

def columnPerm_0713 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 4, 1, 2, 5]
  invFun := ![0, 3, 4, 1, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0713 : BottomDetBound targetTop_0713 9 := by
  have hU : rowTransform_0713.det.natAbs = 1 := by
    have hdet : rowTransform_0713.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate.bottomBound.transformTopRows rowTransform_0713 hU
  have hcols := hrows.permuteColumns columnPerm_0713
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0713 MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Base.explicitTop)
          columnPerm_0713 = targetTop_0713 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0713 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 4 5 5 7)) 9 := by
  have htop : targetTop_0713 =
      topOfPattern (R := ℤ) (angle6 0 3 4 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0713

/-- Explicit target top block for canonical pattern `(0, 3, 4, 5, 6, 6)`. -/
def targetTop_0714 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 0, 0;
     0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0714 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 0]

def columnPerm_0714 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 4, 2, 3]
  invFun := ![0, 2, 4, 5, 3, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0714 : BottomDetBound targetTop_0714 9 := by
  have hU : rowTransform_0714.det.natAbs = 1 := by
    have hdet : rowTransform_0714.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R022.Aggregate.bottomBound.transformTopRows rowTransform_0714 hU
  have hcols := hrows.permuteColumns columnPerm_0714
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0714 MainTheory.Generated.BinaryBetaSixKernel.Representative.R022.Base.explicitTop)
          columnPerm_0714 = targetTop_0714 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0714 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 4 5 6 6)) 9 := by
  have htop : targetTop_0714 =
      topOfPattern (R := ℤ) (angle6 0 3 4 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0714

/-- Explicit target top block for canonical pattern `(0, 3, 4, 5, 6, 7)`. -/
def targetTop_0715 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 0, 1;
     0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0715 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_0715 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 3, 5]
  invFun := ![0, 2, 3, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0715 : BottomDetBound targetTop_0715 9 := by
  have hU : rowTransform_0715.det.natAbs = 1 := by
    have hdet : rowTransform_0715.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R024.Aggregate.bottomBound.transformTopRows rowTransform_0715 hU
  have hcols := hrows.permuteColumns columnPerm_0715
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0715 MainTheory.Generated.BinaryBetaSixKernel.Representative.R024.Base.explicitTop)
          columnPerm_0715 = targetTop_0715 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0715 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 4 5 6 7)) 9 := by
  have htop : targetTop_0715 =
      topOfPattern (R := ℤ) (angle6 0 3 4 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0715

/-- Explicit target top block for canonical pattern `(0, 3, 4, 5, 7, 7)`. -/
def targetTop_0716 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 1, 1;
     0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0716 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 0, 0;
     0, 1, 1]

def columnPerm_0716 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0716 : BottomDetBound targetTop_0716 9 := by
  have hU : rowTransform_0716.det.natAbs = 1 := by
    have hdet : rowTransform_0716.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Aggregate.bottomBound.transformTopRows rowTransform_0716 hU
  have hcols := hrows.permuteColumns columnPerm_0716
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0716 MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Base.explicitTop)
          columnPerm_0716 = targetTop_0716 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0716 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 4 5 7 7)) 9 := by
  have htop : targetTop_0716 =
      topOfPattern (R := ℤ) (angle6 0 3 4 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0716

/-- Explicit target top block for canonical pattern `(0, 3, 4, 6, 6, 6)`. -/
def targetTop_0717 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 0;
     0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0717 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 0;
     1, 0, 1]

def columnPerm_0717 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0717 : BottomDetBound targetTop_0717 9 := by
  have hU : rowTransform_0717.det.natAbs = 1 := by
    have hdet : rowTransform_0717.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0717 hU
  have hcols := hrows.permuteColumns columnPerm_0717
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0717 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0717 = targetTop_0717 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0717 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 4 6 6 6)) 9 := by
  have htop : targetTop_0717 =
      topOfPattern (R := ℤ) (angle6 0 3 4 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0717

/-- Explicit target top block for canonical pattern `(0, 3, 4, 6, 6, 7)`. -/
def targetTop_0718 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 1;
     0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0718 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 0;
     1, 0, 1]

def columnPerm_0718 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 4, 1, 2, 5]
  invFun := ![0, 3, 4, 1, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0718 : BottomDetBound targetTop_0718 9 := by
  have hU : rowTransform_0718.det.natAbs = 1 := by
    have hdet : rowTransform_0718.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate.bottomBound.transformTopRows rowTransform_0718 hU
  have hcols := hrows.permuteColumns columnPerm_0718
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0718 MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Base.explicitTop)
          columnPerm_0718 = targetTop_0718 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0718 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 4 6 6 7)) 9 := by
  have htop : targetTop_0718 =
      topOfPattern (R := ℤ) (angle6 0 3 4 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0718

/-- Explicit target top block for canonical pattern `(0, 3, 4, 6, 7, 7)`. -/
def targetTop_0719 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 1, 1;
     0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0719 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 0, 1;
     0, 1, 1]

def columnPerm_0719 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0719 : BottomDetBound targetTop_0719 9 := by
  have hU : rowTransform_0719.det.natAbs = 1 := by
    have hdet : rowTransform_0719.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Aggregate.bottomBound.transformTopRows rowTransform_0719 hU
  have hcols := hrows.permuteColumns columnPerm_0719
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0719 MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Base.explicitTop)
          columnPerm_0719 = targetTop_0719 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0719 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 4 6 7 7)) 9 := by
  have htop : targetTop_0719 =
      topOfPattern (R := ℤ) (angle6 0 3 4 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0719

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard044
