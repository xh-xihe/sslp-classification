-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R004.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R005.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard010

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(0, 0, 1, 2, 4, 5)`. -/
def targetTop_0160 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0160 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_0160 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0160 : BottomDetBound targetTop_0160 9 := by
  have hU : rowTransform_0160.det.natAbs = 1 := by
    have hdet : rowTransform_0160.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Aggregate.bottomBound.transformTopRows rowTransform_0160 hU
  have hcols := hrows.permuteColumns columnPerm_0160
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0160 MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Base.explicitTop)
          columnPerm_0160 = targetTop_0160 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0160 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 2 4 5)) 9 := by
  have htop : targetTop_0160 =
      topOfPattern (R := ℤ) (angle6 0 0 1 2 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0160

/-- Explicit target top block for canonical pattern `(0, 0, 1, 2, 4, 6)`. -/
def targetTop_0161 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0161 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_0161 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0161 : BottomDetBound targetTop_0161 9 := by
  have hU : rowTransform_0161.det.natAbs = 1 := by
    have hdet : rowTransform_0161.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Aggregate.bottomBound.transformTopRows rowTransform_0161 hU
  have hcols := hrows.permuteColumns columnPerm_0161
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0161 MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Base.explicitTop)
          columnPerm_0161 = targetTop_0161 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0161 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 2 4 6)) 9 := by
  have htop : targetTop_0161 =
      topOfPattern (R := ℤ) (angle6 0 0 1 2 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0161

/-- Explicit target top block for canonical pattern `(0, 0, 1, 2, 4, 7)`. -/
def targetTop_0162 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0162 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0162 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0162 : BottomDetBound targetTop_0162 9 := by
  have hU : rowTransform_0162.det.natAbs = 1 := by
    have hdet : rowTransform_0162.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R004.Aggregate.bottomBound.transformTopRows rowTransform_0162 hU
  have hcols := hrows.permuteColumns columnPerm_0162
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0162 MainTheory.Generated.BinaryBetaSixKernel.Representative.R004.Base.explicitTop)
          columnPerm_0162 = targetTop_0162 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0162 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 2 4 7)) 9 := by
  have htop : targetTop_0162 =
      topOfPattern (R := ℤ) (angle6 0 0 1 2 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0162

/-- Explicit target top block for canonical pattern `(0, 0, 1, 2, 5, 5)`. -/
def targetTop_0163 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0163 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_0163 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0163 : BottomDetBound targetTop_0163 9 := by
  have hU : rowTransform_0163.det.natAbs = 1 := by
    have hdet : rowTransform_0163.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0163 hU
  have hcols := hrows.permuteColumns columnPerm_0163
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0163 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0163 = targetTop_0163 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0163 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 2 5 5)) 9 := by
  have htop : targetTop_0163 =
      topOfPattern (R := ℤ) (angle6 0 0 1 2 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0163

/-- Explicit target top block for canonical pattern `(0, 0, 1, 2, 5, 6)`. -/
def targetTop_0164 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 1, 0;
     0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0164 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0164 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0164 : BottomDetBound targetTop_0164 9 := by
  have hU : rowTransform_0164.det.natAbs = 1 := by
    have hdet : rowTransform_0164.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R005.Aggregate.bottomBound.transformTopRows rowTransform_0164 hU
  have hcols := hrows.permuteColumns columnPerm_0164
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0164 MainTheory.Generated.BinaryBetaSixKernel.Representative.R005.Base.explicitTop)
          columnPerm_0164 = targetTop_0164 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0164 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 2 5 6)) 9 := by
  have htop : targetTop_0164 =
      topOfPattern (R := ℤ) (angle6 0 0 1 2 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0164

/-- Explicit target top block for canonical pattern `(0, 0, 1, 2, 5, 7)`. -/
def targetTop_0165 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0165 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_0165 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0165 : BottomDetBound targetTop_0165 9 := by
  have hU : rowTransform_0165.det.natAbs = 1 := by
    have hdet : rowTransform_0165.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Aggregate.bottomBound.transformTopRows rowTransform_0165 hU
  have hcols := hrows.permuteColumns columnPerm_0165
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0165 MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Base.explicitTop)
          columnPerm_0165 = targetTop_0165 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0165 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 2 5 7)) 9 := by
  have htop : targetTop_0165 =
      topOfPattern (R := ℤ) (angle6 0 0 1 2 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0165

/-- Explicit target top block for canonical pattern `(0, 0, 1, 2, 6, 6)`. -/
def targetTop_0166 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0166 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 1;
     1, 0, 0]

def columnPerm_0166 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0166 : BottomDetBound targetTop_0166 9 := by
  have hU : rowTransform_0166.det.natAbs = 1 := by
    have hdet : rowTransform_0166.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0166 hU
  have hcols := hrows.permuteColumns columnPerm_0166
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0166 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0166 = targetTop_0166 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0166 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 2 6 6)) 9 := by
  have htop : targetTop_0166 =
      topOfPattern (R := ℤ) (angle6 0 0 1 2 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0166

/-- Explicit target top block for canonical pattern `(0, 0, 1, 2, 6, 7)`. -/
def targetTop_0167 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0167 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     0, 1, 0]

def columnPerm_0167 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0167 : BottomDetBound targetTop_0167 9 := by
  have hU : rowTransform_0167.det.natAbs = 1 := by
    have hdet : rowTransform_0167.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Aggregate.bottomBound.transformTopRows rowTransform_0167 hU
  have hcols := hrows.permuteColumns columnPerm_0167
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0167 MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Base.explicitTop)
          columnPerm_0167 = targetTop_0167 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0167 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 2 6 7)) 9 := by
  have htop : targetTop_0167 =
      topOfPattern (R := ℤ) (angle6 0 0 1 2 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0167

/-- Explicit target top block for canonical pattern `(0, 0, 1, 2, 7, 7)`. -/
def targetTop_0168 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0168 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 1;
     1, 0, 0]

def columnPerm_0168 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0168 : BottomDetBound targetTop_0168 9 := by
  have hU : rowTransform_0168.det.natAbs = 1 := by
    have hdet : rowTransform_0168.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0168 hU
  have hcols := hrows.permuteColumns columnPerm_0168
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0168 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0168 = targetTop_0168 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0168 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 2 7 7)) 9 := by
  have htop : targetTop_0168 =
      topOfPattern (R := ℤ) (angle6 0 0 1 2 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0168

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 1, 3, 3, 3)`. -/
def targetTop_0169 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0169 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0169 :
    TopRowRelation targetTop_0169 relationCoefficients_0169 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0169, relationCoefficients_0169, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0169 : BottomDetBound targetTop_0169 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0169

theorem canonicalBound_0169 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 3 3 3)) 9 := by
  have htop : targetTop_0169 =
      topOfPattern (R := ℤ) (angle6 0 0 1 3 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0169

/-- Explicit target top block for canonical pattern `(0, 0, 1, 3, 3, 4)`. -/
def targetTop_0170 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 0;
     0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0170 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_0170 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0170 : BottomDetBound targetTop_0170 9 := by
  have hU : rowTransform_0170.det.natAbs = 1 := by
    have hdet : rowTransform_0170.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0170 hU
  have hcols := hrows.permuteColumns columnPerm_0170
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0170 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0170 = targetTop_0170 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0170 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 3 3 4)) 9 := by
  have htop : targetTop_0170 =
      topOfPattern (R := ℤ) (angle6 0 0 1 3 3 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0170

/-- Explicit target top block for canonical pattern `(0, 0, 1, 3, 3, 5)`. -/
def targetTop_0171 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0171 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     1, 0, 0;
     0, 0, 1]

def columnPerm_0171 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0171 : BottomDetBound targetTop_0171 9 := by
  have hU : rowTransform_0171.det.natAbs = 1 := by
    have hdet : rowTransform_0171.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0171 hU
  have hcols := hrows.permuteColumns columnPerm_0171
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0171 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0171 = targetTop_0171 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0171 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 3 3 5)) 9 := by
  have htop : targetTop_0171 =
      topOfPattern (R := ℤ) (angle6 0 0 1 3 3 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0171

/-- Explicit target top block for canonical pattern `(0, 0, 1, 3, 3, 6)`. -/
def targetTop_0172 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 0;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0172 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 1;
     0, 0, 1]

def columnPerm_0172 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0172 : BottomDetBound targetTop_0172 9 := by
  have hU : rowTransform_0172.det.natAbs = 1 := by
    have hdet : rowTransform_0172.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0172 hU
  have hcols := hrows.permuteColumns columnPerm_0172
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0172 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0172 = targetTop_0172 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0172 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 3 3 6)) 9 := by
  have htop : targetTop_0172 =
      topOfPattern (R := ℤ) (angle6 0 0 1 3 3 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0172

/-- Explicit target top block for canonical pattern `(0, 0, 1, 3, 3, 7)`. -/
def targetTop_0173 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0173 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     1, 0, 1;
     0, 0, 1]

def columnPerm_0173 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0173 : BottomDetBound targetTop_0173 9 := by
  have hU : rowTransform_0173.det.natAbs = 1 := by
    have hdet : rowTransform_0173.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0173 hU
  have hcols := hrows.permuteColumns columnPerm_0173
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0173 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0173 = targetTop_0173 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0173 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 3 3 7)) 9 := by
  have htop : targetTop_0173 =
      topOfPattern (R := ℤ) (angle6 0 0 1 3 3 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0173

/-- Explicit target top block for canonical pattern `(0, 0, 1, 3, 4, 4)`. -/
def targetTop_0174 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0174 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 0, 1;
     1, 0, 0]

def columnPerm_0174 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0174 : BottomDetBound targetTop_0174 9 := by
  have hU : rowTransform_0174.det.natAbs = 1 := by
    have hdet : rowTransform_0174.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0174 hU
  have hcols := hrows.permuteColumns columnPerm_0174
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0174 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0174 = targetTop_0174 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0174 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 3 4 4)) 9 := by
  have htop : targetTop_0174 =
      topOfPattern (R := ℤ) (angle6 0 0 1 3 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0174

/-- Explicit target top block for canonical pattern `(0, 0, 1, 3, 4, 5)`. -/
def targetTop_0175 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 1;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0175 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 0, 1;
     0, 1, 0]

def columnPerm_0175 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0175 : BottomDetBound targetTop_0175 9 := by
  have hU : rowTransform_0175.det.natAbs = 1 := by
    have hdet : rowTransform_0175.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Aggregate.bottomBound.transformTopRows rowTransform_0175 hU
  have hcols := hrows.permuteColumns columnPerm_0175
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0175 MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Base.explicitTop)
          columnPerm_0175 = targetTop_0175 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0175 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 3 4 5)) 9 := by
  have htop : targetTop_0175 =
      topOfPattern (R := ℤ) (angle6 0 0 1 3 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0175

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard010
