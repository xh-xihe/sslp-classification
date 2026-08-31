-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard075

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(1, 4, 4, 4, 4, 6)`. -/
def targetTop_1200 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1200 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 1]

def columnPerm_1200 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1200 : BottomDetBound targetTop_1200 9 := by
  have hU : rowTransform_1200.det.natAbs = 1 := by
    have hdet : rowTransform_1200.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1200 hU
  have hcols := hrows.permuteColumns columnPerm_1200
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1200 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1200 = targetTop_1200 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1200 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 4 4 4 6)) 9 := by
  have htop : targetTop_1200 =
      topOfPattern (R := ℤ) (angle6 1 4 4 4 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1200

/-- Explicit target top block for canonical pattern `(1, 4, 4, 4, 4, 7)`. -/
def targetTop_1201 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1201 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 0, 1;
     1, 0, 1]

def columnPerm_1201 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1201 : BottomDetBound targetTop_1201 9 := by
  have hU : rowTransform_1201.det.natAbs = 1 := by
    have hdet : rowTransform_1201.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1201 hU
  have hcols := hrows.permuteColumns columnPerm_1201
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1201 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1201 = targetTop_1201 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1201 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 4 4 4 7)) 9 := by
  have htop : targetTop_1201 =
      topOfPattern (R := ℤ) (angle6 1 4 4 4 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1201

/-- Explicit rank-deficient target for canonical pattern `(1, 4, 4, 4, 5, 5)`. -/
def targetTop_1202 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1202 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_1202 :
    TopRowRelation targetTop_1202 relationCoefficients_1202 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1202, relationCoefficients_1202, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1202 : BottomDetBound targetTop_1202 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1202

theorem canonicalBound_1202 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 4 4 5 5)) 9 := by
  have htop : targetTop_1202 =
      topOfPattern (R := ℤ) (angle6 1 4 4 4 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1202

/-- Explicit target top block for canonical pattern `(1, 4, 4, 4, 5, 6)`. -/
def targetTop_1203 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1203 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 1]

def columnPerm_1203 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1203 : BottomDetBound targetTop_1203 9 := by
  have hU : rowTransform_1203.det.natAbs = 1 := by
    have hdet : rowTransform_1203.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_1203 hU
  have hcols := hrows.permuteColumns columnPerm_1203
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1203 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_1203 = targetTop_1203 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1203 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 4 4 5 6)) 9 := by
  have htop : targetTop_1203 =
      topOfPattern (R := ℤ) (angle6 1 4 4 4 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1203

/-- Explicit target top block for canonical pattern `(1, 4, 4, 4, 5, 7)`. -/
def targetTop_1204 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1204 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 0, 1;
     1, 0, 1]

def columnPerm_1204 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1204 : BottomDetBound targetTop_1204 9 := by
  have hU : rowTransform_1204.det.natAbs = 1 := by
    have hdet : rowTransform_1204.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_1204 hU
  have hcols := hrows.permuteColumns columnPerm_1204
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1204 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_1204 = targetTop_1204 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1204 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 4 4 5 7)) 9 := by
  have htop : targetTop_1204 =
      topOfPattern (R := ℤ) (angle6 1 4 4 4 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1204

/-- Explicit target top block for canonical pattern `(1, 4, 4, 4, 6, 6)`. -/
def targetTop_1205 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1205 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 1, 0]

def columnPerm_1205 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1205 : BottomDetBound targetTop_1205 9 := by
  have hU : rowTransform_1205.det.natAbs = 1 := by
    have hdet : rowTransform_1205.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1205 hU
  have hcols := hrows.permuteColumns columnPerm_1205
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1205 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1205 = targetTop_1205 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1205 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 4 4 6 6)) 9 := by
  have htop : targetTop_1205 =
      topOfPattern (R := ℤ) (angle6 1 4 4 4 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1205

/-- Explicit target top block for canonical pattern `(1, 4, 4, 4, 6, 7)`. -/
def targetTop_1206 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1206 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 1]

def columnPerm_1206 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1206 : BottomDetBound targetTop_1206 9 := by
  have hU : rowTransform_1206.det.natAbs = 1 := by
    have hdet : rowTransform_1206.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate.bottomBound.transformTopRows rowTransform_1206 hU
  have hcols := hrows.permuteColumns columnPerm_1206
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1206 MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Base.explicitTop)
          columnPerm_1206 = targetTop_1206 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1206 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 4 4 6 7)) 9 := by
  have htop : targetTop_1206 =
      topOfPattern (R := ℤ) (angle6 1 4 4 4 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1206

/-- Explicit target top block for canonical pattern `(1, 4, 4, 4, 7, 7)`. -/
def targetTop_1207 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1207 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 1, 0;
     1, 1, 0]

def columnPerm_1207 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1207 : BottomDetBound targetTop_1207 9 := by
  have hU : rowTransform_1207.det.natAbs = 1 := by
    have hdet : rowTransform_1207.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1207 hU
  have hcols := hrows.permuteColumns columnPerm_1207
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1207 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1207 = targetTop_1207 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1207 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 4 4 7 7)) 9 := by
  have htop : targetTop_1207 =
      topOfPattern (R := ℤ) (angle6 1 4 4 4 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1207

/-- Explicit rank-deficient target for canonical pattern `(1, 4, 4, 5, 5, 5)`. -/
def targetTop_1208 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1208 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_1208 :
    TopRowRelation targetTop_1208 relationCoefficients_1208 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1208, relationCoefficients_1208, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1208 : BottomDetBound targetTop_1208 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1208

theorem canonicalBound_1208 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 4 5 5 5)) 9 := by
  have htop : targetTop_1208 =
      topOfPattern (R := ℤ) (angle6 1 4 4 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1208

/-- Explicit target top block for canonical pattern `(1, 4, 4, 5, 5, 6)`. -/
def targetTop_1209 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1209 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 1]

def columnPerm_1209 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1209 : BottomDetBound targetTop_1209 9 := by
  have hU : rowTransform_1209.det.natAbs = 1 := by
    have hdet : rowTransform_1209.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_1209 hU
  have hcols := hrows.permuteColumns columnPerm_1209
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1209 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_1209 = targetTop_1209 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1209 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 4 5 5 6)) 9 := by
  have htop : targetTop_1209 =
      topOfPattern (R := ℤ) (angle6 1 4 4 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1209

/-- Explicit target top block for canonical pattern `(1, 4, 4, 5, 5, 7)`. -/
def targetTop_1210 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1210 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 0, 1;
     1, 0, 1]

def columnPerm_1210 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1210 : BottomDetBound targetTop_1210 9 := by
  have hU : rowTransform_1210.det.natAbs = 1 := by
    have hdet : rowTransform_1210.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_1210 hU
  have hcols := hrows.permuteColumns columnPerm_1210
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1210 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_1210 = targetTop_1210 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1210 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 4 5 5 7)) 9 := by
  have htop : targetTop_1210 =
      topOfPattern (R := ℤ) (angle6 1 4 4 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1210

/-- Explicit target top block for canonical pattern `(1, 4, 4, 5, 6, 6)`. -/
def targetTop_1211 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1211 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 1, 0]

def columnPerm_1211 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 5, 2, 3]
  invFun := ![1, 2, 4, 5, 0, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1211 : BottomDetBound targetTop_1211 9 := by
  have hU : rowTransform_1211.det.natAbs = 1 := by
    have hdet : rowTransform_1211.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_1211 hU
  have hcols := hrows.permuteColumns columnPerm_1211
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1211 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_1211 = targetTop_1211 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1211 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 4 5 6 6)) 9 := by
  have htop : targetTop_1211 =
      topOfPattern (R := ℤ) (angle6 1 4 4 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1211

/-- Explicit target top block for canonical pattern `(1, 4, 4, 5, 6, 7)`. -/
def targetTop_1212 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1212 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 1]

def columnPerm_1212 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1212 : BottomDetBound targetTop_1212 9 := by
  have hU : rowTransform_1212.det.natAbs = 1 := by
    have hdet : rowTransform_1212.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Aggregate.bottomBound.transformTopRows rowTransform_1212 hU
  have hcols := hrows.permuteColumns columnPerm_1212
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1212 MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Base.explicitTop)
          columnPerm_1212 = targetTop_1212 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1212 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 4 5 6 7)) 9 := by
  have htop : targetTop_1212 =
      topOfPattern (R := ℤ) (angle6 1 4 4 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1212

/-- Explicit target top block for canonical pattern `(1, 4, 4, 5, 7, 7)`. -/
def targetTop_1213 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1213 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 1, 0;
     1, 1, 0]

def columnPerm_1213 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 5, 2, 3]
  invFun := ![1, 2, 4, 5, 0, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1213 : BottomDetBound targetTop_1213 9 := by
  have hU : rowTransform_1213.det.natAbs = 1 := by
    have hdet : rowTransform_1213.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_1213 hU
  have hcols := hrows.permuteColumns columnPerm_1213
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1213 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_1213 = targetTop_1213 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1213 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 4 5 7 7)) 9 := by
  have htop : targetTop_1213 =
      topOfPattern (R := ℤ) (angle6 1 4 4 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1213

/-- Explicit target top block for canonical pattern `(1, 4, 4, 6, 6, 6)`. -/
def targetTop_1214 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1214 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     1, 1, 0]

def columnPerm_1214 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1214 : BottomDetBound targetTop_1214 9 := by
  have hU : rowTransform_1214.det.natAbs = 1 := by
    have hdet : rowTransform_1214.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1214 hU
  have hcols := hrows.permuteColumns columnPerm_1214
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1214 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1214 = targetTop_1214 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1214 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 4 6 6 6)) 9 := by
  have htop : targetTop_1214 =
      topOfPattern (R := ℤ) (angle6 1 4 4 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1214

/-- Explicit target top block for canonical pattern `(1, 4, 4, 6, 6, 7)`. -/
def targetTop_1215 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1215 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     1, 1, 0]

def columnPerm_1215 : Equiv.Perm (Fin 6) where
  toFun := ![4, 2, 3, 0, 1, 5]
  invFun := ![3, 4, 1, 2, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1215 : BottomDetBound targetTop_1215 9 := by
  have hU : rowTransform_1215.det.natAbs = 1 := by
    have hdet : rowTransform_1215.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_1215 hU
  have hcols := hrows.permuteColumns columnPerm_1215
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1215 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_1215 = targetTop_1215 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1215 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 4 6 6 7)) 9 := by
  have htop : targetTop_1215 =
      topOfPattern (R := ℤ) (angle6 1 4 4 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1215

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard075
