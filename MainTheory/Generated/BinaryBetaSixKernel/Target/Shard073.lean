-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R042.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R045.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R050.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R057.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R061.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R062.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R064.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard073

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(1, 3, 4, 4, 5, 6)`. -/
def targetTop_1168 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 1, 0;
     0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1168 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1168 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 0, 1, 3, 4]
  invFun := ![2, 3, 0, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1168 : BottomDetBound targetTop_1168 9 := by
  have hU : rowTransform_1168.det.natAbs = 1 := by
    have hdet : rowTransform_1168.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R045.Aggregate.bottomBound.transformTopRows rowTransform_1168 hU
  have hcols := hrows.permuteColumns columnPerm_1168
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1168 MainTheory.Generated.BinaryBetaSixKernel.Representative.R045.Base.explicitTop)
          columnPerm_1168 = targetTop_1168 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1168 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 4 4 5 6)) 9 := by
  have htop : targetTop_1168 =
      topOfPattern (R := ℤ) (angle6 1 3 4 4 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1168

/-- Explicit target top block for canonical pattern `(1, 3, 4, 4, 5, 7)`. -/
def targetTop_1169 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 1, 1;
     0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1169 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1169 : Equiv.Perm (Fin 6) where
  toFun := ![2, 4, 0, 1, 3, 5]
  invFun := ![2, 3, 0, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1169 : BottomDetBound targetTop_1169 9 := by
  have hU : rowTransform_1169.det.natAbs = 1 := by
    have hdet : rowTransform_1169.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R042.Aggregate.bottomBound.transformTopRows rowTransform_1169 hU
  have hcols := hrows.permuteColumns columnPerm_1169
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1169 MainTheory.Generated.BinaryBetaSixKernel.Representative.R042.Base.explicitTop)
          columnPerm_1169 = targetTop_1169 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1169 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 4 4 5 7)) 9 := by
  have htop : targetTop_1169 =
      topOfPattern (R := ℤ) (angle6 1 3 4 4 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1169

/-- Explicit target top block for canonical pattern `(1, 3, 4, 4, 6, 6)`. -/
def targetTop_1170 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 0;
     0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1170 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 1, (-1)]

def columnPerm_1170 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1170 : BottomDetBound targetTop_1170 9 := by
  have hU : rowTransform_1170.det.natAbs = 1 := by
    have hdet : rowTransform_1170.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate.bottomBound.transformTopRows rowTransform_1170 hU
  have hcols := hrows.permuteColumns columnPerm_1170
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1170 MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Base.explicitTop)
          columnPerm_1170 = targetTop_1170 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1170 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 4 4 6 6)) 9 := by
  have htop : targetTop_1170 =
      topOfPattern (R := ℤ) (angle6 1 3 4 4 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1170

/-- Explicit target top block for canonical pattern `(1, 3, 4, 4, 6, 7)`. -/
def targetTop_1171 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 1;
     0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1171 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1171 : Equiv.Perm (Fin 6) where
  toFun := ![2, 4, 0, 1, 3, 5]
  invFun := ![2, 3, 0, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1171 : BottomDetBound targetTop_1171 9 := by
  have hU : rowTransform_1171.det.natAbs = 1 := by
    have hdet : rowTransform_1171.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R050.Aggregate.bottomBound.transformTopRows rowTransform_1171 hU
  have hcols := hrows.permuteColumns columnPerm_1171
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1171 MainTheory.Generated.BinaryBetaSixKernel.Representative.R050.Base.explicitTop)
          columnPerm_1171 = targetTop_1171 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1171 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 4 4 6 7)) 9 := by
  have htop : targetTop_1171 =
      topOfPattern (R := ℤ) (angle6 1 3 4 4 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1171

/-- Explicit target top block for canonical pattern `(1, 3, 4, 4, 7, 7)`. -/
def targetTop_1172 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 1, 1;
     0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1172 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 1, 0;
     1, 0, 0]

def columnPerm_1172 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 0, 1, 3, 4]
  invFun := ![2, 3, 1, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1172 : BottomDetBound targetTop_1172 9 := by
  have hU : rowTransform_1172.det.natAbs = 1 := by
    have hdet : rowTransform_1172.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_1172 hU
  have hcols := hrows.permuteColumns columnPerm_1172
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1172 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_1172 = targetTop_1172 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1172 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 4 4 7 7)) 9 := by
  have htop : targetTop_1172 =
      topOfPattern (R := ℤ) (angle6 1 3 4 4 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1172

/-- Explicit target top block for canonical pattern `(1, 3, 4, 5, 5, 5)`. -/
def targetTop_1173 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 1, 1;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1173 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 0, 1;
     0, 1, 0]

def columnPerm_1173 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1173 : BottomDetBound targetTop_1173 9 := by
  have hU : rowTransform_1173.det.natAbs = 1 := by
    have hdet : rowTransform_1173.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Aggregate.bottomBound.transformTopRows rowTransform_1173 hU
  have hcols := hrows.permuteColumns columnPerm_1173
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1173 MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Base.explicitTop)
          columnPerm_1173 = targetTop_1173 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1173 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 4 5 5 5)) 9 := by
  have htop : targetTop_1173 =
      topOfPattern (R := ℤ) (angle6 1 3 4 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1173

/-- Explicit target top block for canonical pattern `(1, 3, 4, 5, 5, 6)`. -/
def targetTop_1174 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 1, 0;
     0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1174 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_1174 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 3, 5]
  invFun := ![0, 2, 3, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1174 : BottomDetBound targetTop_1174 9 := by
  have hU : rowTransform_1174.det.natAbs = 1 := by
    have hdet : rowTransform_1174.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R057.Aggregate.bottomBound.transformTopRows rowTransform_1174 hU
  have hcols := hrows.permuteColumns columnPerm_1174
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1174 MainTheory.Generated.BinaryBetaSixKernel.Representative.R057.Base.explicitTop)
          columnPerm_1174 = targetTop_1174 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1174 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 4 5 5 6)) 9 := by
  have htop : targetTop_1174 =
      topOfPattern (R := ℤ) (angle6 1 3 4 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1174

/-- Explicit target top block for canonical pattern `(1, 3, 4, 5, 5, 7)`. -/
def targetTop_1175 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 1, 1;
     0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1175 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1175 : Equiv.Perm (Fin 6) where
  toFun := ![1, 4, 0, 2, 3, 5]
  invFun := ![2, 0, 3, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1175 : BottomDetBound targetTop_1175 9 := by
  have hU : rowTransform_1175.det.natAbs = 1 := by
    have hdet : rowTransform_1175.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Aggregate.bottomBound.transformTopRows rowTransform_1175 hU
  have hcols := hrows.permuteColumns columnPerm_1175
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1175 MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Base.explicitTop)
          columnPerm_1175 = targetTop_1175 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1175 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 4 5 5 7)) 9 := by
  have htop : targetTop_1175 =
      topOfPattern (R := ℤ) (angle6 1 3 4 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1175

/-- Explicit target top block for canonical pattern `(1, 3, 4, 5, 6, 6)`. -/
def targetTop_1176 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 0, 0;
     0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1176 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1176 : Equiv.Perm (Fin 6) where
  toFun := ![1, 5, 0, 2, 3, 4]
  invFun := ![2, 0, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1176 : BottomDetBound targetTop_1176 9 := by
  have hU : rowTransform_1176.det.natAbs = 1 := by
    have hdet : rowTransform_1176.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R061.Aggregate.bottomBound.transformTopRows rowTransform_1176 hU
  have hcols := hrows.permuteColumns columnPerm_1176
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1176 MainTheory.Generated.BinaryBetaSixKernel.Representative.R061.Base.explicitTop)
          columnPerm_1176 = targetTop_1176 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1176 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 4 5 6 6)) 9 := by
  have htop : targetTop_1176 =
      topOfPattern (R := ℤ) (angle6 1 3 4 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1176

/-- Explicit target top block for canonical pattern `(1, 3, 4, 5, 6, 7)`. -/
def targetTop_1177 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 0, 1;
     0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1177 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_1177 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 4, 5]
  invFun := ![0, 2, 3, 1, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1177 : BottomDetBound targetTop_1177 9 := by
  have hU : rowTransform_1177.det.natAbs = 1 := by
    have hdet : rowTransform_1177.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R062.Aggregate.bottomBound.transformTopRows rowTransform_1177 hU
  have hcols := hrows.permuteColumns columnPerm_1177
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1177 MainTheory.Generated.BinaryBetaSixKernel.Representative.R062.Base.explicitTop)
          columnPerm_1177 = targetTop_1177 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1177 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 4 5 6 7)) 9 := by
  have htop : targetTop_1177 =
      topOfPattern (R := ℤ) (angle6 1 3 4 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1177

/-- Explicit target top block for canonical pattern `(1, 3, 4, 5, 7, 7)`. -/
def targetTop_1178 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 1, 1;
     0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1178 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 1, 0;
     1, 0, 0]

def columnPerm_1178 : Equiv.Perm (Fin 6) where
  toFun := ![4, 1, 0, 5, 2, 3]
  invFun := ![2, 1, 4, 5, 0, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1178 : BottomDetBound targetTop_1178 9 := by
  have hU : rowTransform_1178.det.natAbs = 1 := by
    have hdet : rowTransform_1178.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Aggregate.bottomBound.transformTopRows rowTransform_1178 hU
  have hcols := hrows.permuteColumns columnPerm_1178
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1178 MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Base.explicitTop)
          columnPerm_1178 = targetTop_1178 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1178 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 4 5 7 7)) 9 := by
  have htop : targetTop_1178 =
      topOfPattern (R := ℤ) (angle6 1 3 4 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1178

/-- Explicit target top block for canonical pattern `(1, 3, 4, 6, 6, 6)`. -/
def targetTop_1179 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 0;
     0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1179 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, (-1);
     1, 0, 0]

def columnPerm_1179 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1179 : BottomDetBound targetTop_1179 9 := by
  have hU : rowTransform_1179.det.natAbs = 1 := by
    have hdet : rowTransform_1179.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate.bottomBound.transformTopRows rowTransform_1179 hU
  have hcols := hrows.permuteColumns columnPerm_1179
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1179 MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Base.explicitTop)
          columnPerm_1179 = targetTop_1179 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1179 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 4 6 6 6)) 9 := by
  have htop : targetTop_1179 =
      topOfPattern (R := ℤ) (angle6 1 3 4 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1179

/-- Explicit target top block for canonical pattern `(1, 3, 4, 6, 6, 7)`. -/
def targetTop_1180 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 1;
     0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1180 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, (-1);
     1, 0, 0]

def columnPerm_1180 : Equiv.Perm (Fin 6) where
  toFun := ![4, 2, 3, 0, 1, 5]
  invFun := ![3, 4, 1, 2, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1180 : BottomDetBound targetTop_1180 9 := by
  have hU : rowTransform_1180.det.natAbs = 1 := by
    have hdet : rowTransform_1180.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R050.Aggregate.bottomBound.transformTopRows rowTransform_1180 hU
  have hcols := hrows.permuteColumns columnPerm_1180
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1180 MainTheory.Generated.BinaryBetaSixKernel.Representative.R050.Base.explicitTop)
          columnPerm_1180 = targetTop_1180 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1180 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 4 6 6 7)) 9 := by
  have htop : targetTop_1180 =
      topOfPattern (R := ℤ) (angle6 1 3 4 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1180

/-- Explicit target top block for canonical pattern `(1, 3, 4, 6, 7, 7)`. -/
def targetTop_1181 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 1, 1;
     0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1181 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, (-1);
     0, 1, 0;
     0, 0, 1]

def columnPerm_1181 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1181 : BottomDetBound targetTop_1181 9 := by
  have hU : rowTransform_1181.det.natAbs = 1 := by
    have hdet : rowTransform_1181.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R064.Aggregate.bottomBound.transformTopRows rowTransform_1181 hU
  have hcols := hrows.permuteColumns columnPerm_1181
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1181 MainTheory.Generated.BinaryBetaSixKernel.Representative.R064.Base.explicitTop)
          columnPerm_1181 = targetTop_1181 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1181 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 4 6 7 7)) 9 := by
  have htop : targetTop_1181 =
      topOfPattern (R := ℤ) (angle6 1 3 4 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1181

/-- Explicit target top block for canonical pattern `(1, 3, 4, 7, 7, 7)`. -/
def targetTop_1182 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 1, 1;
     0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1182 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1182 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1182 : BottomDetBound targetTop_1182 9 := by
  have hU : rowTransform_1182.det.natAbs = 1 := by
    have hdet : rowTransform_1182.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Aggregate.bottomBound.transformTopRows rowTransform_1182 hU
  have hcols := hrows.permuteColumns columnPerm_1182
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1182 MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Base.explicitTop)
          columnPerm_1182 = targetTop_1182 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1182 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 4 7 7 7)) 9 := by
  have htop : targetTop_1182 =
      topOfPattern (R := ℤ) (angle6 1 3 4 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1182

/-- Explicit target top block for canonical pattern `(1, 3, 5, 5, 5, 5)`. -/
def targetTop_1183 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1183 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1183 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1183 : BottomDetBound targetTop_1183 9 := by
  have hU : rowTransform_1183.det.natAbs = 1 := by
    have hdet : rowTransform_1183.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1183 hU
  have hcols := hrows.permuteColumns columnPerm_1183
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1183 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1183 = targetTop_1183 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1183 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 5 5 5 5)) 9 := by
  have htop : targetTop_1183 =
      topOfPattern (R := ℤ) (angle6 1 3 5 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1183

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard073
