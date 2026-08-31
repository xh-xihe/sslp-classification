-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard012

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(0, 0, 1, 4, 6, 7)`. -/
def targetTop_0192 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0192 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 1, 1]

def columnPerm_0192 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0192 : BottomDetBound targetTop_0192 9 := by
  have hU : rowTransform_0192.det.natAbs = 1 := by
    have hdet : rowTransform_0192.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Aggregate.bottomBound.transformTopRows rowTransform_0192 hU
  have hcols := hrows.permuteColumns columnPerm_0192
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0192 MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Base.explicitTop)
          columnPerm_0192 = targetTop_0192 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0192 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 4 6 7)) 9 := by
  have htop : targetTop_0192 =
      topOfPattern (R := ℤ) (angle6 0 0 1 4 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0192

/-- Explicit target top block for canonical pattern `(0, 0, 1, 4, 7, 7)`. -/
def targetTop_0193 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0193 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 0;
     1, 0, 1]

def columnPerm_0193 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0193 : BottomDetBound targetTop_0193 9 := by
  have hU : rowTransform_0193.det.natAbs = 1 := by
    have hdet : rowTransform_0193.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0193 hU
  have hcols := hrows.permuteColumns columnPerm_0193
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0193 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0193 = targetTop_0193 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0193 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 4 7 7)) 9 := by
  have htop : targetTop_0193 =
      topOfPattern (R := ℤ) (angle6 0 0 1 4 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0193

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 1, 5, 5, 5)`. -/
def targetTop_0194 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0194 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0194 :
    TopRowRelation targetTop_0194 relationCoefficients_0194 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0194, relationCoefficients_0194, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0194 : BottomDetBound targetTop_0194 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0194

theorem canonicalBound_0194 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 5 5 5)) 9 := by
  have htop : targetTop_0194 =
      topOfPattern (R := ℤ) (angle6 0 0 1 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0194

/-- Explicit target top block for canonical pattern `(0, 0, 1, 5, 5, 6)`. -/
def targetTop_0195 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0195 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 0, 1;
     1, 0, 1]

def columnPerm_0195 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0195 : BottomDetBound targetTop_0195 9 := by
  have hU : rowTransform_0195.det.natAbs = 1 := by
    have hdet : rowTransform_0195.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0195 hU
  have hcols := hrows.permuteColumns columnPerm_0195
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0195 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0195 = targetTop_0195 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0195 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 5 5 6)) 9 := by
  have htop : targetTop_0195 =
      topOfPattern (R := ℤ) (angle6 0 0 1 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0195

/-- Explicit target top block for canonical pattern `(0, 0, 1, 5, 5, 7)`. -/
def targetTop_0196 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0196 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 0, 1;
     1, 0, 1]

def columnPerm_0196 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0196 : BottomDetBound targetTop_0196 9 := by
  have hU : rowTransform_0196.det.natAbs = 1 := by
    have hdet : rowTransform_0196.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0196 hU
  have hcols := hrows.permuteColumns columnPerm_0196
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0196 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0196 = targetTop_0196 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0196 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 5 5 7)) 9 := by
  have htop : targetTop_0196 =
      topOfPattern (R := ℤ) (angle6 0 0 1 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0196

/-- Explicit target top block for canonical pattern `(0, 0, 1, 5, 6, 6)`. -/
def targetTop_0197 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0197 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 0;
     1, 0, 1]

def columnPerm_0197 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0197 : BottomDetBound targetTop_0197 9 := by
  have hU : rowTransform_0197.det.natAbs = 1 := by
    have hdet : rowTransform_0197.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0197 hU
  have hcols := hrows.permuteColumns columnPerm_0197
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0197 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0197 = targetTop_0197 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0197 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 5 6 6)) 9 := by
  have htop : targetTop_0197 =
      topOfPattern (R := ℤ) (angle6 0 0 1 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0197

/-- Explicit target top block for canonical pattern `(0, 0, 1, 5, 6, 7)`. -/
def targetTop_0198 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0198 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 0;
     0, 1, 1]

def columnPerm_0198 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0198 : BottomDetBound targetTop_0198 9 := by
  have hU : rowTransform_0198.det.natAbs = 1 := by
    have hdet : rowTransform_0198.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Aggregate.bottomBound.transformTopRows rowTransform_0198 hU
  have hcols := hrows.permuteColumns columnPerm_0198
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0198 MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Base.explicitTop)
          columnPerm_0198 = targetTop_0198 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0198 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 5 6 7)) 9 := by
  have htop : targetTop_0198 =
      topOfPattern (R := ℤ) (angle6 0 0 1 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0198

/-- Explicit target top block for canonical pattern `(0, 0, 1, 5, 7, 7)`. -/
def targetTop_0199 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0199 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     1, 0, 0;
     1, 0, 1]

def columnPerm_0199 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0199 : BottomDetBound targetTop_0199 9 := by
  have hU : rowTransform_0199.det.natAbs = 1 := by
    have hdet : rowTransform_0199.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0199 hU
  have hcols := hrows.permuteColumns columnPerm_0199
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0199 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0199 = targetTop_0199 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0199 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 5 7 7)) 9 := by
  have htop : targetTop_0199 =
      topOfPattern (R := ℤ) (angle6 0 0 1 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0199

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 1, 6, 6, 6)`. -/
def targetTop_0200 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0200 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0200 :
    TopRowRelation targetTop_0200 relationCoefficients_0200 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0200, relationCoefficients_0200, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0200 : BottomDetBound targetTop_0200 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0200

theorem canonicalBound_0200 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 6 6 6)) 9 := by
  have htop : targetTop_0200 =
      topOfPattern (R := ℤ) (angle6 0 0 1 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0200

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 1, 6, 6, 7)`. -/
def targetTop_0201 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0201 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0201 :
    TopRowRelation targetTop_0201 relationCoefficients_0201 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0201, relationCoefficients_0201, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0201 : BottomDetBound targetTop_0201 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0201

theorem canonicalBound_0201 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 6 6 7)) 9 := by
  have htop : targetTop_0201 =
      topOfPattern (R := ℤ) (angle6 0 0 1 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0201

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 1, 6, 7, 7)`. -/
def targetTop_0202 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0202 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0202 :
    TopRowRelation targetTop_0202 relationCoefficients_0202 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0202, relationCoefficients_0202, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0202 : BottomDetBound targetTop_0202 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0202

theorem canonicalBound_0202 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 6 7 7)) 9 := by
  have htop : targetTop_0202 =
      topOfPattern (R := ℤ) (angle6 0 0 1 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0202

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 1, 7, 7, 7)`. -/
def targetTop_0203 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0203 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0203 :
    TopRowRelation targetTop_0203 relationCoefficients_0203 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0203, relationCoefficients_0203, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0203 : BottomDetBound targetTop_0203 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0203

theorem canonicalBound_0203 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 7 7 7)) 9 := by
  have htop : targetTop_0203 =
      topOfPattern (R := ℤ) (angle6 0 0 1 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0203

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 2, 2, 2, 2)`. -/
def targetTop_0204 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0204 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0204 :
    TopRowRelation targetTop_0204 relationCoefficients_0204 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0204, relationCoefficients_0204, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0204 : BottomDetBound targetTop_0204 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0204

theorem canonicalBound_0204 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 2 2 2)) 9 := by
  have htop : targetTop_0204 =
      topOfPattern (R := ℤ) (angle6 0 0 2 2 2 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0204

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 2, 2, 2, 3)`. -/
def targetTop_0205 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0205 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0205 :
    TopRowRelation targetTop_0205 relationCoefficients_0205 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0205, relationCoefficients_0205, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0205 : BottomDetBound targetTop_0205 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0205

theorem canonicalBound_0205 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 2 2 3)) 9 := by
  have htop : targetTop_0205 =
      topOfPattern (R := ℤ) (angle6 0 0 2 2 2 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0205

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 2, 2, 2, 4)`. -/
def targetTop_0206 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0206 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0206 :
    TopRowRelation targetTop_0206 relationCoefficients_0206 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0206, relationCoefficients_0206, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0206 : BottomDetBound targetTop_0206 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0206

theorem canonicalBound_0206 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 2 2 4)) 9 := by
  have htop : targetTop_0206 =
      topOfPattern (R := ℤ) (angle6 0 0 2 2 2 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0206

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 2, 2, 2, 5)`. -/
def targetTop_0207 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0207 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0207 :
    TopRowRelation targetTop_0207 relationCoefficients_0207 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0207, relationCoefficients_0207, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0207 : BottomDetBound targetTop_0207 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0207

theorem canonicalBound_0207 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 2 2 5)) 9 := by
  have htop : targetTop_0207 =
      topOfPattern (R := ℤ) (angle6 0 0 2 2 2 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0207

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard012
