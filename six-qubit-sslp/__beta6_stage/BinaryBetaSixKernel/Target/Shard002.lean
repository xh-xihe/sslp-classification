-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard002

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 0, 5, 7)`. -/
def targetTop_0032 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0032 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0032 :
    TopRowRelation targetTop_0032 relationCoefficients_0032 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0032, relationCoefficients_0032, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0032 : BottomDetBound targetTop_0032 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0032

theorem canonicalBound_0032 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 5 7)) 9 := by
  have htop : targetTop_0032 =
      topOfPattern (R := ℤ) (angle6 0 0 0 0 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0032

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 0, 6, 6)`. -/
def targetTop_0033 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0033 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0033 :
    TopRowRelation targetTop_0033 relationCoefficients_0033 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0033, relationCoefficients_0033, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0033 : BottomDetBound targetTop_0033 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0033

theorem canonicalBound_0033 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 6 6)) 9 := by
  have htop : targetTop_0033 =
      topOfPattern (R := ℤ) (angle6 0 0 0 0 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0033

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 0, 6, 7)`. -/
def targetTop_0034 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0034 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0034 :
    TopRowRelation targetTop_0034 relationCoefficients_0034 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0034, relationCoefficients_0034, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0034 : BottomDetBound targetTop_0034 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0034

theorem canonicalBound_0034 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 6 7)) 9 := by
  have htop : targetTop_0034 =
      topOfPattern (R := ℤ) (angle6 0 0 0 0 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0034

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 0, 7, 7)`. -/
def targetTop_0035 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0035 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0035 :
    TopRowRelation targetTop_0035 relationCoefficients_0035 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0035, relationCoefficients_0035, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0035 : BottomDetBound targetTop_0035 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0035

theorem canonicalBound_0035 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 7 7)) 9 := by
  have htop : targetTop_0035 =
      topOfPattern (R := ℤ) (angle6 0 0 0 0 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0035

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 1, 1, 1)`. -/
def targetTop_0036 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0036 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0036 :
    TopRowRelation targetTop_0036 relationCoefficients_0036 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0036, relationCoefficients_0036, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0036 : BottomDetBound targetTop_0036 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0036

theorem canonicalBound_0036 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 1 1 1)) 9 := by
  have htop : targetTop_0036 =
      topOfPattern (R := ℤ) (angle6 0 0 0 1 1 1) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0036

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 1, 1, 2)`. -/
def targetTop_0037 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0037 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0037 :
    TopRowRelation targetTop_0037 relationCoefficients_0037 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0037, relationCoefficients_0037, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0037 : BottomDetBound targetTop_0037 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0037

theorem canonicalBound_0037 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 1 1 2)) 9 := by
  have htop : targetTop_0037 =
      topOfPattern (R := ℤ) (angle6 0 0 0 1 1 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0037

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 1, 1, 3)`. -/
def targetTop_0038 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0038 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0038 :
    TopRowRelation targetTop_0038 relationCoefficients_0038 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0038, relationCoefficients_0038, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0038 : BottomDetBound targetTop_0038 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0038

theorem canonicalBound_0038 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 1 1 3)) 9 := by
  have htop : targetTop_0038 =
      topOfPattern (R := ℤ) (angle6 0 0 0 1 1 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0038

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 1, 1, 4)`. -/
def targetTop_0039 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0039 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0039 :
    TopRowRelation targetTop_0039 relationCoefficients_0039 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0039, relationCoefficients_0039, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0039 : BottomDetBound targetTop_0039 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0039

theorem canonicalBound_0039 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 1 1 4)) 9 := by
  have htop : targetTop_0039 =
      topOfPattern (R := ℤ) (angle6 0 0 0 1 1 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0039

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 1, 1, 5)`. -/
def targetTop_0040 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0040 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0040 :
    TopRowRelation targetTop_0040 relationCoefficients_0040 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0040, relationCoefficients_0040, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0040 : BottomDetBound targetTop_0040 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0040

theorem canonicalBound_0040 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 1 1 5)) 9 := by
  have htop : targetTop_0040 =
      topOfPattern (R := ℤ) (angle6 0 0 0 1 1 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0040

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 1, 1, 6)`. -/
def targetTop_0041 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0041 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0041 :
    TopRowRelation targetTop_0041 relationCoefficients_0041 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0041, relationCoefficients_0041, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0041 : BottomDetBound targetTop_0041 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0041

theorem canonicalBound_0041 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 1 1 6)) 9 := by
  have htop : targetTop_0041 =
      topOfPattern (R := ℤ) (angle6 0 0 0 1 1 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0041

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 1, 1, 7)`. -/
def targetTop_0042 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0042 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0042 :
    TopRowRelation targetTop_0042 relationCoefficients_0042 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0042, relationCoefficients_0042, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0042 : BottomDetBound targetTop_0042 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0042

theorem canonicalBound_0042 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 1 1 7)) 9 := by
  have htop : targetTop_0042 =
      topOfPattern (R := ℤ) (angle6 0 0 0 1 1 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0042

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 1, 2, 2)`. -/
def targetTop_0043 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0043 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0043 :
    TopRowRelation targetTop_0043 relationCoefficients_0043 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0043, relationCoefficients_0043, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0043 : BottomDetBound targetTop_0043 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0043

theorem canonicalBound_0043 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 1 2 2)) 9 := by
  have htop : targetTop_0043 =
      topOfPattern (R := ℤ) (angle6 0 0 0 1 2 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0043

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 1, 2, 3)`. -/
def targetTop_0044 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0044 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0044 :
    TopRowRelation targetTop_0044 relationCoefficients_0044 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0044, relationCoefficients_0044, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0044 : BottomDetBound targetTop_0044 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0044

theorem canonicalBound_0044 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 1 2 3)) 9 := by
  have htop : targetTop_0044 =
      topOfPattern (R := ℤ) (angle6 0 0 0 1 2 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0044

/-- Explicit target top block for canonical pattern `(0, 0, 0, 1, 2, 4)`. -/
def targetTop_0045 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0045 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0045 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0045 : BottomDetBound targetTop_0045 9 := by
  have hU : rowTransform_0045.det.natAbs = 1 := by
    have hdet : rowTransform_0045.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Aggregate.bottomBound.transformTopRows rowTransform_0045 hU
  have hcols := hrows.permuteColumns columnPerm_0045
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0045 MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Base.explicitTop)
          columnPerm_0045 = targetTop_0045 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0045 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 1 2 4)) 9 := by
  have htop : targetTop_0045 =
      topOfPattern (R := ℤ) (angle6 0 0 0 1 2 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0045

/-- Explicit target top block for canonical pattern `(0, 0, 0, 1, 2, 5)`. -/
def targetTop_0046 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0046 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0046 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0046 : BottomDetBound targetTop_0046 9 := by
  have hU : rowTransform_0046.det.natAbs = 1 := by
    have hdet : rowTransform_0046.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Aggregate.bottomBound.transformTopRows rowTransform_0046 hU
  have hcols := hrows.permuteColumns columnPerm_0046
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0046 MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Base.explicitTop)
          columnPerm_0046 = targetTop_0046 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0046 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 1 2 5)) 9 := by
  have htop : targetTop_0046 =
      topOfPattern (R := ℤ) (angle6 0 0 0 1 2 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0046

/-- Explicit target top block for canonical pattern `(0, 0, 0, 1, 2, 6)`. -/
def targetTop_0047 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0047 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0047 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0047 : BottomDetBound targetTop_0047 9 := by
  have hU : rowTransform_0047.det.natAbs = 1 := by
    have hdet : rowTransform_0047.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Aggregate.bottomBound.transformTopRows rowTransform_0047 hU
  have hcols := hrows.permuteColumns columnPerm_0047
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0047 MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Base.explicitTop)
          columnPerm_0047 = targetTop_0047 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0047 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 1 2 6)) 9 := by
  have htop : targetTop_0047 =
      topOfPattern (R := ℤ) (angle6 0 0 0 1 2 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0047

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard002
