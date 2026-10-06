-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical


namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard001

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 0, 2, 3)`. -/
def targetTop_0016 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0016 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0016 :
    TopRowRelation targetTop_0016 relationCoefficients_0016 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0016, relationCoefficients_0016, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0016 : BottomDetBound targetTop_0016 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0016

theorem canonicalBound_0016 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 2 3)) 9 := by
  have htop : targetTop_0016 =
      topOfPattern (R := ℤ) (angle6 0 0 0 0 2 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0016

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 0, 2, 4)`. -/
def targetTop_0017 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0017 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0017 :
    TopRowRelation targetTop_0017 relationCoefficients_0017 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0017, relationCoefficients_0017, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0017 : BottomDetBound targetTop_0017 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0017

theorem canonicalBound_0017 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 2 4)) 9 := by
  have htop : targetTop_0017 =
      topOfPattern (R := ℤ) (angle6 0 0 0 0 2 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0017

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 0, 2, 5)`. -/
def targetTop_0018 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0018 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0018 :
    TopRowRelation targetTop_0018 relationCoefficients_0018 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0018, relationCoefficients_0018, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0018 : BottomDetBound targetTop_0018 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0018

theorem canonicalBound_0018 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 2 5)) 9 := by
  have htop : targetTop_0018 =
      topOfPattern (R := ℤ) (angle6 0 0 0 0 2 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0018

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 0, 2, 6)`. -/
def targetTop_0019 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0019 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0019 :
    TopRowRelation targetTop_0019 relationCoefficients_0019 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0019, relationCoefficients_0019, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0019 : BottomDetBound targetTop_0019 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0019

theorem canonicalBound_0019 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 2 6)) 9 := by
  have htop : targetTop_0019 =
      topOfPattern (R := ℤ) (angle6 0 0 0 0 2 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0019

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 0, 2, 7)`. -/
def targetTop_0020 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0020 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0020 :
    TopRowRelation targetTop_0020 relationCoefficients_0020 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0020, relationCoefficients_0020, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0020 : BottomDetBound targetTop_0020 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0020

theorem canonicalBound_0020 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 2 7)) 9 := by
  have htop : targetTop_0020 =
      topOfPattern (R := ℤ) (angle6 0 0 0 0 2 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0020

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 0, 3, 3)`. -/
def targetTop_0021 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0021 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0021 :
    TopRowRelation targetTop_0021 relationCoefficients_0021 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0021, relationCoefficients_0021, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0021 : BottomDetBound targetTop_0021 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0021

theorem canonicalBound_0021 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 3 3)) 9 := by
  have htop : targetTop_0021 =
      topOfPattern (R := ℤ) (angle6 0 0 0 0 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0021

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 0, 3, 4)`. -/
def targetTop_0022 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0022 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0022 :
    TopRowRelation targetTop_0022 relationCoefficients_0022 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0022, relationCoefficients_0022, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0022 : BottomDetBound targetTop_0022 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0022

theorem canonicalBound_0022 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 3 4)) 9 := by
  have htop : targetTop_0022 =
      topOfPattern (R := ℤ) (angle6 0 0 0 0 3 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0022

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 0, 3, 5)`. -/
def targetTop_0023 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0023 : Fin 3 → ℤ :=
  ![1, (-1), (-1)]

theorem topRelation_0023 :
    TopRowRelation targetTop_0023 relationCoefficients_0023 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0023, relationCoefficients_0023, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0023 : BottomDetBound targetTop_0023 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0023

theorem canonicalBound_0023 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 3 5)) 9 := by
  have htop : targetTop_0023 =
      topOfPattern (R := ℤ) (angle6 0 0 0 0 3 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0023

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 0, 3, 6)`. -/
def targetTop_0024 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0024 : Fin 3 → ℤ :=
  ![1, (-1), 1]

theorem topRelation_0024 :
    TopRowRelation targetTop_0024 relationCoefficients_0024 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0024, relationCoefficients_0024, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0024 : BottomDetBound targetTop_0024 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0024

theorem canonicalBound_0024 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 3 6)) 9 := by
  have htop : targetTop_0024 =
      topOfPattern (R := ℤ) (angle6 0 0 0 0 3 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0024

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 0, 3, 7)`. -/
def targetTop_0025 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0025 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0025 :
    TopRowRelation targetTop_0025 relationCoefficients_0025 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0025, relationCoefficients_0025, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0025 : BottomDetBound targetTop_0025 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0025

theorem canonicalBound_0025 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 3 7)) 9 := by
  have htop : targetTop_0025 =
      topOfPattern (R := ℤ) (angle6 0 0 0 0 3 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0025

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 0, 4, 4)`. -/
def targetTop_0026 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0026 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0026 :
    TopRowRelation targetTop_0026 relationCoefficients_0026 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0026, relationCoefficients_0026, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0026 : BottomDetBound targetTop_0026 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0026

theorem canonicalBound_0026 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 4 4)) 9 := by
  have htop : targetTop_0026 =
      topOfPattern (R := ℤ) (angle6 0 0 0 0 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0026

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 0, 4, 5)`. -/
def targetTop_0027 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0027 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0027 :
    TopRowRelation targetTop_0027 relationCoefficients_0027 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0027, relationCoefficients_0027, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0027 : BottomDetBound targetTop_0027 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0027

theorem canonicalBound_0027 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 4 5)) 9 := by
  have htop : targetTop_0027 =
      topOfPattern (R := ℤ) (angle6 0 0 0 0 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0027

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 0, 4, 6)`. -/
def targetTop_0028 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0028 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0028 :
    TopRowRelation targetTop_0028 relationCoefficients_0028 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0028, relationCoefficients_0028, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0028 : BottomDetBound targetTop_0028 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0028

theorem canonicalBound_0028 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 4 6)) 9 := by
  have htop : targetTop_0028 =
      topOfPattern (R := ℤ) (angle6 0 0 0 0 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0028

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 0, 4, 7)`. -/
def targetTop_0029 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0029 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0029 :
    TopRowRelation targetTop_0029 relationCoefficients_0029 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0029, relationCoefficients_0029, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0029 : BottomDetBound targetTop_0029 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0029

theorem canonicalBound_0029 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 4 7)) 9 := by
  have htop : targetTop_0029 =
      topOfPattern (R := ℤ) (angle6 0 0 0 0 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0029

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 0, 5, 5)`. -/
def targetTop_0030 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0030 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0030 :
    TopRowRelation targetTop_0030 relationCoefficients_0030 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0030, relationCoefficients_0030, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0030 : BottomDetBound targetTop_0030 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0030

theorem canonicalBound_0030 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 5 5)) 9 := by
  have htop : targetTop_0030 =
      topOfPattern (R := ℤ) (angle6 0 0 0 0 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0030

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 0, 5, 6)`. -/
def targetTop_0031 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0031 : Fin 3 → ℤ :=
  ![1, 1, (-1)]

theorem topRelation_0031 :
    TopRowRelation targetTop_0031 relationCoefficients_0031 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0031, relationCoefficients_0031, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0031 : BottomDetBound targetTop_0031 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0031

theorem canonicalBound_0031 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 5 6)) 9 := by
  have htop : targetTop_0031 =
      topOfPattern (R := ℤ) (angle6 0 0 0 0 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0031

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard001
