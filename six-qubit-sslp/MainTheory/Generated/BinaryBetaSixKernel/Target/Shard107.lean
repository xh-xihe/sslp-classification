-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical


namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard107

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit rank-deficient target for canonical pattern `(6, 6, 6, 7, 7, 7)`. -/
def targetTop_1712 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     1, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1712 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_1712 :
    TopRowRelation targetTop_1712 relationCoefficients_1712 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1712, relationCoefficients_1712, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1712 : BottomDetBound targetTop_1712 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1712

theorem canonicalBound_1712 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 6 6 6 7 7 7)) 9 := by
  have htop : targetTop_1712 =
      topOfPattern (R := ℤ) (angle6 6 6 6 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1712

/-- Explicit rank-deficient target for canonical pattern `(6, 6, 7, 7, 7, 7)`. -/
def targetTop_1713 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1713 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_1713 :
    TopRowRelation targetTop_1713 relationCoefficients_1713 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1713, relationCoefficients_1713, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1713 : BottomDetBound targetTop_1713 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1713

theorem canonicalBound_1713 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 6 6 7 7 7 7)) 9 := by
  have htop : targetTop_1713 =
      topOfPattern (R := ℤ) (angle6 6 6 7 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1713

/-- Explicit rank-deficient target for canonical pattern `(6, 7, 7, 7, 7, 7)`. -/
def targetTop_1714 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1714 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_1714 :
    TopRowRelation targetTop_1714 relationCoefficients_1714 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1714, relationCoefficients_1714, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1714 : BottomDetBound targetTop_1714 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1714

theorem canonicalBound_1714 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 6 7 7 7 7 7)) 9 := by
  have htop : targetTop_1714 =
      topOfPattern (R := ℤ) (angle6 6 7 7 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1714

/-- Explicit rank-deficient target for canonical pattern `(7, 7, 7, 7, 7, 7)`. -/
def targetTop_1715 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1715 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_1715 :
    TopRowRelation targetTop_1715 relationCoefficients_1715 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1715, relationCoefficients_1715, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1715 : BottomDetBound targetTop_1715 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1715

theorem canonicalBound_1715 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 7 7 7 7 7 7)) 9 := by
  have htop : targetTop_1715 =
      topOfPattern (R := ℤ) (angle6 7 7 7 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1715

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard107
