-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard007

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 5, 5, 7)`. -/
def targetTop_0112 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0112 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0112 :
    TopRowRelation targetTop_0112 relationCoefficients_0112 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0112, relationCoefficients_0112, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0112 : BottomDetBound targetTop_0112 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0112

theorem canonicalBound_0112 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 5 5 7)) 9 := by
  have htop : targetTop_0112 =
      topOfPattern (R := ℤ) (angle6 0 0 0 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0112

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 5, 6, 6)`. -/
def targetTop_0113 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0113 : Fin 3 → ℤ :=
  ![1, 1, (-1)]

theorem topRelation_0113 :
    TopRowRelation targetTop_0113 relationCoefficients_0113 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0113, relationCoefficients_0113, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0113 : BottomDetBound targetTop_0113 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0113

theorem canonicalBound_0113 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 5 6 6)) 9 := by
  have htop : targetTop_0113 =
      topOfPattern (R := ℤ) (angle6 0 0 0 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0113

/-- Explicit target top block for canonical pattern `(0, 0, 0, 5, 6, 7)`. -/
def targetTop_0114 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0114 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 1;
     1, 1, 1]

def columnPerm_0114 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0114 : BottomDetBound targetTop_0114 9 := by
  have hU : rowTransform_0114.det.natAbs = 1 := by
    have hdet : rowTransform_0114.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Aggregate.bottomBound.transformTopRows rowTransform_0114 hU
  have hcols := hrows.permuteColumns columnPerm_0114
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0114 MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Base.explicitTop)
          columnPerm_0114 = targetTop_0114 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0114 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 5 6 7)) 9 := by
  have htop : targetTop_0114 =
      topOfPattern (R := ℤ) (angle6 0 0 0 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0114

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 5, 7, 7)`. -/
def targetTop_0115 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0115 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0115 :
    TopRowRelation targetTop_0115 relationCoefficients_0115 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0115, relationCoefficients_0115, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0115 : BottomDetBound targetTop_0115 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0115

theorem canonicalBound_0115 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 5 7 7)) 9 := by
  have htop : targetTop_0115 =
      topOfPattern (R := ℤ) (angle6 0 0 0 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0115

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 6, 6, 6)`. -/
def targetTop_0116 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0116 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0116 :
    TopRowRelation targetTop_0116 relationCoefficients_0116 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0116, relationCoefficients_0116, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0116 : BottomDetBound targetTop_0116 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0116

theorem canonicalBound_0116 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 6 6 6)) 9 := by
  have htop : targetTop_0116 =
      topOfPattern (R := ℤ) (angle6 0 0 0 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0116

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 6, 6, 7)`. -/
def targetTop_0117 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0117 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0117 :
    TopRowRelation targetTop_0117 relationCoefficients_0117 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0117, relationCoefficients_0117, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0117 : BottomDetBound targetTop_0117 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0117

theorem canonicalBound_0117 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 6 6 7)) 9 := by
  have htop : targetTop_0117 =
      topOfPattern (R := ℤ) (angle6 0 0 0 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0117

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 6, 7, 7)`. -/
def targetTop_0118 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0118 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0118 :
    TopRowRelation targetTop_0118 relationCoefficients_0118 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0118, relationCoefficients_0118, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0118 : BottomDetBound targetTop_0118 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0118

theorem canonicalBound_0118 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 6 7 7)) 9 := by
  have htop : targetTop_0118 =
      topOfPattern (R := ℤ) (angle6 0 0 0 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0118

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 7, 7, 7)`. -/
def targetTop_0119 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0119 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0119 :
    TopRowRelation targetTop_0119 relationCoefficients_0119 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0119, relationCoefficients_0119, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0119 : BottomDetBound targetTop_0119 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0119

theorem canonicalBound_0119 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 7 7 7)) 9 := by
  have htop : targetTop_0119 =
      topOfPattern (R := ℤ) (angle6 0 0 0 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0119

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 1, 1, 1, 1)`. -/
def targetTop_0120 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0120 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0120 :
    TopRowRelation targetTop_0120 relationCoefficients_0120 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0120, relationCoefficients_0120, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0120 : BottomDetBound targetTop_0120 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0120

theorem canonicalBound_0120 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 1 1)) 9 := by
  have htop : targetTop_0120 =
      topOfPattern (R := ℤ) (angle6 0 0 1 1 1 1) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0120

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 1, 1, 1, 2)`. -/
def targetTop_0121 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0121 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0121 :
    TopRowRelation targetTop_0121 relationCoefficients_0121 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0121, relationCoefficients_0121, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0121 : BottomDetBound targetTop_0121 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0121

theorem canonicalBound_0121 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 1 2)) 9 := by
  have htop : targetTop_0121 =
      topOfPattern (R := ℤ) (angle6 0 0 1 1 1 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0121

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 1, 1, 1, 3)`. -/
def targetTop_0122 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0122 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0122 :
    TopRowRelation targetTop_0122 relationCoefficients_0122 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0122, relationCoefficients_0122, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0122 : BottomDetBound targetTop_0122 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0122

theorem canonicalBound_0122 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 1 3)) 9 := by
  have htop : targetTop_0122 =
      topOfPattern (R := ℤ) (angle6 0 0 1 1 1 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0122

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 1, 1, 1, 4)`. -/
def targetTop_0123 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0123 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0123 :
    TopRowRelation targetTop_0123 relationCoefficients_0123 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0123, relationCoefficients_0123, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0123 : BottomDetBound targetTop_0123 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0123

theorem canonicalBound_0123 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 1 4)) 9 := by
  have htop : targetTop_0123 =
      topOfPattern (R := ℤ) (angle6 0 0 1 1 1 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0123

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 1, 1, 1, 5)`. -/
def targetTop_0124 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0124 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0124 :
    TopRowRelation targetTop_0124 relationCoefficients_0124 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0124, relationCoefficients_0124, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0124 : BottomDetBound targetTop_0124 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0124

theorem canonicalBound_0124 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 1 5)) 9 := by
  have htop : targetTop_0124 =
      topOfPattern (R := ℤ) (angle6 0 0 1 1 1 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0124

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 1, 1, 1, 6)`. -/
def targetTop_0125 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0125 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0125 :
    TopRowRelation targetTop_0125 relationCoefficients_0125 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0125, relationCoefficients_0125, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0125 : BottomDetBound targetTop_0125 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0125

theorem canonicalBound_0125 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 1 6)) 9 := by
  have htop : targetTop_0125 =
      topOfPattern (R := ℤ) (angle6 0 0 1 1 1 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0125

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 1, 1, 1, 7)`. -/
def targetTop_0126 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0126 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0126 :
    TopRowRelation targetTop_0126 relationCoefficients_0126 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0126, relationCoefficients_0126, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0126 : BottomDetBound targetTop_0126 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0126

theorem canonicalBound_0126 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 1 7)) 9 := by
  have htop : targetTop_0126 =
      topOfPattern (R := ℤ) (angle6 0 0 1 1 1 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0126

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 1, 1, 2, 2)`. -/
def targetTop_0127 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0127 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0127 :
    TopRowRelation targetTop_0127 relationCoefficients_0127 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0127, relationCoefficients_0127, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0127 : BottomDetBound targetTop_0127 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0127

theorem canonicalBound_0127 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 2 2)) 9 := by
  have htop : targetTop_0127 =
      topOfPattern (R := ℤ) (angle6 0 0 1 1 2 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0127

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard007
