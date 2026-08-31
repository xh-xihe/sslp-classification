-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical


namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 0, 0, 0)`. -/
def targetTop_0000 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0000 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0000 :
    TopRowRelation targetTop_0000 relationCoefficients_0000 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0000, relationCoefficients_0000, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0000 : BottomDetBound targetTop_0000 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0000

theorem canonicalBound_0000 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 0 0)) 9 := by
  have htop : targetTop_0000 =
      topOfPattern (R := ℤ) (angle6 0 0 0 0 0 0) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0000

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 0, 0, 1)`. -/
def targetTop_0001 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0001 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0001 :
    TopRowRelation targetTop_0001 relationCoefficients_0001 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0001, relationCoefficients_0001, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0001 : BottomDetBound targetTop_0001 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0001

theorem canonicalBound_0001 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 0 1)) 9 := by
  have htop : targetTop_0001 =
      topOfPattern (R := ℤ) (angle6 0 0 0 0 0 1) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0001

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 0, 0, 2)`. -/
def targetTop_0002 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0002 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0002 :
    TopRowRelation targetTop_0002 relationCoefficients_0002 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0002, relationCoefficients_0002, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0002 : BottomDetBound targetTop_0002 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0002

theorem canonicalBound_0002 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 0 2)) 9 := by
  have htop : targetTop_0002 =
      topOfPattern (R := ℤ) (angle6 0 0 0 0 0 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0002

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 0, 0, 3)`. -/
def targetTop_0003 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0003 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0003 :
    TopRowRelation targetTop_0003 relationCoefficients_0003 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0003, relationCoefficients_0003, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0003 : BottomDetBound targetTop_0003 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0003

theorem canonicalBound_0003 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 0 3)) 9 := by
  have htop : targetTop_0003 =
      topOfPattern (R := ℤ) (angle6 0 0 0 0 0 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0003

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 0, 0, 4)`. -/
def targetTop_0004 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0004 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0004 :
    TopRowRelation targetTop_0004 relationCoefficients_0004 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0004, relationCoefficients_0004, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0004 : BottomDetBound targetTop_0004 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0004

theorem canonicalBound_0004 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 0 4)) 9 := by
  have htop : targetTop_0004 =
      topOfPattern (R := ℤ) (angle6 0 0 0 0 0 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0004

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 0, 0, 5)`. -/
def targetTop_0005 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0005 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0005 :
    TopRowRelation targetTop_0005 relationCoefficients_0005 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0005, relationCoefficients_0005, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0005 : BottomDetBound targetTop_0005 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0005

theorem canonicalBound_0005 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 0 5)) 9 := by
  have htop : targetTop_0005 =
      topOfPattern (R := ℤ) (angle6 0 0 0 0 0 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0005

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 0, 0, 6)`. -/
def targetTop_0006 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0006 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0006 :
    TopRowRelation targetTop_0006 relationCoefficients_0006 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0006, relationCoefficients_0006, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0006 : BottomDetBound targetTop_0006 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0006

theorem canonicalBound_0006 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 0 6)) 9 := by
  have htop : targetTop_0006 =
      topOfPattern (R := ℤ) (angle6 0 0 0 0 0 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0006

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 0, 0, 7)`. -/
def targetTop_0007 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0007 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0007 :
    TopRowRelation targetTop_0007 relationCoefficients_0007 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0007, relationCoefficients_0007, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0007 : BottomDetBound targetTop_0007 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0007

theorem canonicalBound_0007 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 0 7)) 9 := by
  have htop : targetTop_0007 =
      topOfPattern (R := ℤ) (angle6 0 0 0 0 0 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0007

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 0, 1, 1)`. -/
def targetTop_0008 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0008 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0008 :
    TopRowRelation targetTop_0008 relationCoefficients_0008 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0008, relationCoefficients_0008, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0008 : BottomDetBound targetTop_0008 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0008

theorem canonicalBound_0008 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 1 1)) 9 := by
  have htop : targetTop_0008 =
      topOfPattern (R := ℤ) (angle6 0 0 0 0 1 1) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0008

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 0, 1, 2)`. -/
def targetTop_0009 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0009 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0009 :
    TopRowRelation targetTop_0009 relationCoefficients_0009 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0009, relationCoefficients_0009, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0009 : BottomDetBound targetTop_0009 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0009

theorem canonicalBound_0009 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 1 2)) 9 := by
  have htop : targetTop_0009 =
      topOfPattern (R := ℤ) (angle6 0 0 0 0 1 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0009

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 0, 1, 3)`. -/
def targetTop_0010 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0010 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0010 :
    TopRowRelation targetTop_0010 relationCoefficients_0010 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0010, relationCoefficients_0010, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0010 : BottomDetBound targetTop_0010 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0010

theorem canonicalBound_0010 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 1 3)) 9 := by
  have htop : targetTop_0010 =
      topOfPattern (R := ℤ) (angle6 0 0 0 0 1 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0010

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 0, 1, 4)`. -/
def targetTop_0011 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0011 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0011 :
    TopRowRelation targetTop_0011 relationCoefficients_0011 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0011, relationCoefficients_0011, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0011 : BottomDetBound targetTop_0011 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0011

theorem canonicalBound_0011 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 1 4)) 9 := by
  have htop : targetTop_0011 =
      topOfPattern (R := ℤ) (angle6 0 0 0 0 1 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0011

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 0, 1, 5)`. -/
def targetTop_0012 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0012 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0012 :
    TopRowRelation targetTop_0012 relationCoefficients_0012 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0012, relationCoefficients_0012, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0012 : BottomDetBound targetTop_0012 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0012

theorem canonicalBound_0012 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 1 5)) 9 := by
  have htop : targetTop_0012 =
      topOfPattern (R := ℤ) (angle6 0 0 0 0 1 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0012

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 0, 1, 6)`. -/
def targetTop_0013 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0013 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0013 :
    TopRowRelation targetTop_0013 relationCoefficients_0013 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0013, relationCoefficients_0013, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0013 : BottomDetBound targetTop_0013 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0013

theorem canonicalBound_0013 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 1 6)) 9 := by
  have htop : targetTop_0013 =
      topOfPattern (R := ℤ) (angle6 0 0 0 0 1 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0013

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 0, 1, 7)`. -/
def targetTop_0014 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0014 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0014 :
    TopRowRelation targetTop_0014 relationCoefficients_0014 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0014, relationCoefficients_0014, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0014 : BottomDetBound targetTop_0014 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0014

theorem canonicalBound_0014 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 1 7)) 9 := by
  have htop : targetTop_0014 =
      topOfPattern (R := ℤ) (angle6 0 0 0 0 1 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0014

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 0, 2, 2)`. -/
def targetTop_0015 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0015 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0015 :
    TopRowRelation targetTop_0015 relationCoefficients_0015 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0015, relationCoefficients_0015, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0015 : BottomDetBound targetTop_0015 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0015

theorem canonicalBound_0015 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 2 2)) 9 := by
  have htop : targetTop_0015 =
      topOfPattern (R := ℤ) (angle6 0 0 0 0 2 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0015

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000
