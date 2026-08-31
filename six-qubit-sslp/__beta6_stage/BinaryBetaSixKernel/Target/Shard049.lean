-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard049

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(0, 5, 6, 7, 7, 7)`. -/
def targetTop_0784 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0784 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 1;
     1, 1, 1]

def columnPerm_0784 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0784 : BottomDetBound targetTop_0784 9 := by
  have hU : rowTransform_0784.det.natAbs = 1 := by
    have hdet : rowTransform_0784.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0784 hU
  have hcols := hrows.permuteColumns columnPerm_0784
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0784 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0784 = targetTop_0784 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0784 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 5 6 7 7 7)) 9 := by
  have htop : targetTop_0784 =
      topOfPattern (R := ℤ) (angle6 0 5 6 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0784

/-- Explicit rank-deficient target for canonical pattern `(0, 5, 7, 7, 7, 7)`. -/
def targetTop_0785 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0785 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0785 :
    TopRowRelation targetTop_0785 relationCoefficients_0785 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0785, relationCoefficients_0785, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0785 : BottomDetBound targetTop_0785 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0785

theorem canonicalBound_0785 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 5 7 7 7 7)) 9 := by
  have htop : targetTop_0785 =
      topOfPattern (R := ℤ) (angle6 0 5 7 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0785

/-- Explicit rank-deficient target for canonical pattern `(0, 6, 6, 6, 6, 6)`. -/
def targetTop_0786 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0786 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0786 :
    TopRowRelation targetTop_0786 relationCoefficients_0786 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0786, relationCoefficients_0786, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0786 : BottomDetBound targetTop_0786 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0786

theorem canonicalBound_0786 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 6 6 6 6 6)) 9 := by
  have htop : targetTop_0786 =
      topOfPattern (R := ℤ) (angle6 0 6 6 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0786

/-- Explicit rank-deficient target for canonical pattern `(0, 6, 6, 6, 6, 7)`. -/
def targetTop_0787 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0787 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0787 :
    TopRowRelation targetTop_0787 relationCoefficients_0787 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0787, relationCoefficients_0787, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0787 : BottomDetBound targetTop_0787 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0787

theorem canonicalBound_0787 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 6 6 6 6 7)) 9 := by
  have htop : targetTop_0787 =
      topOfPattern (R := ℤ) (angle6 0 6 6 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0787

/-- Explicit rank-deficient target for canonical pattern `(0, 6, 6, 6, 7, 7)`. -/
def targetTop_0788 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0788 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0788 :
    TopRowRelation targetTop_0788 relationCoefficients_0788 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0788, relationCoefficients_0788, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0788 : BottomDetBound targetTop_0788 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0788

theorem canonicalBound_0788 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 6 6 6 7 7)) 9 := by
  have htop : targetTop_0788 =
      topOfPattern (R := ℤ) (angle6 0 6 6 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0788

/-- Explicit rank-deficient target for canonical pattern `(0, 6, 6, 7, 7, 7)`. -/
def targetTop_0789 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0789 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0789 :
    TopRowRelation targetTop_0789 relationCoefficients_0789 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0789, relationCoefficients_0789, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0789 : BottomDetBound targetTop_0789 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0789

theorem canonicalBound_0789 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 6 6 7 7 7)) 9 := by
  have htop : targetTop_0789 =
      topOfPattern (R := ℤ) (angle6 0 6 6 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0789

/-- Explicit rank-deficient target for canonical pattern `(0, 6, 7, 7, 7, 7)`. -/
def targetTop_0790 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0790 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0790 :
    TopRowRelation targetTop_0790 relationCoefficients_0790 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0790, relationCoefficients_0790, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0790 : BottomDetBound targetTop_0790 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0790

theorem canonicalBound_0790 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 6 7 7 7 7)) 9 := by
  have htop : targetTop_0790 =
      topOfPattern (R := ℤ) (angle6 0 6 7 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0790

/-- Explicit rank-deficient target for canonical pattern `(0, 7, 7, 7, 7, 7)`. -/
def targetTop_0791 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0791 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0791 :
    TopRowRelation targetTop_0791 relationCoefficients_0791 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0791, relationCoefficients_0791, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0791 : BottomDetBound targetTop_0791 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0791

theorem canonicalBound_0791 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 7 7 7 7 7)) 9 := by
  have htop : targetTop_0791 =
      topOfPattern (R := ℤ) (angle6 0 7 7 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0791

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 1, 1, 1, 1)`. -/
def targetTop_0792 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0792 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0792 :
    TopRowRelation targetTop_0792 relationCoefficients_0792 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0792, relationCoefficients_0792, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0792 : BottomDetBound targetTop_0792 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0792

theorem canonicalBound_0792 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 1 1 1)) 9 := by
  have htop : targetTop_0792 =
      topOfPattern (R := ℤ) (angle6 1 1 1 1 1 1) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0792

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 1, 1, 1, 2)`. -/
def targetTop_0793 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0793 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0793 :
    TopRowRelation targetTop_0793 relationCoefficients_0793 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0793, relationCoefficients_0793, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0793 : BottomDetBound targetTop_0793 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0793

theorem canonicalBound_0793 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 1 1 2)) 9 := by
  have htop : targetTop_0793 =
      topOfPattern (R := ℤ) (angle6 1 1 1 1 1 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0793

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 1, 1, 1, 3)`. -/
def targetTop_0794 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0794 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0794 :
    TopRowRelation targetTop_0794 relationCoefficients_0794 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0794, relationCoefficients_0794, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0794 : BottomDetBound targetTop_0794 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0794

theorem canonicalBound_0794 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 1 1 3)) 9 := by
  have htop : targetTop_0794 =
      topOfPattern (R := ℤ) (angle6 1 1 1 1 1 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0794

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 1, 1, 1, 4)`. -/
def targetTop_0795 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0795 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0795 :
    TopRowRelation targetTop_0795 relationCoefficients_0795 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0795, relationCoefficients_0795, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0795 : BottomDetBound targetTop_0795 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0795

theorem canonicalBound_0795 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 1 1 4)) 9 := by
  have htop : targetTop_0795 =
      topOfPattern (R := ℤ) (angle6 1 1 1 1 1 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0795

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 1, 1, 1, 5)`. -/
def targetTop_0796 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0796 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0796 :
    TopRowRelation targetTop_0796 relationCoefficients_0796 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0796, relationCoefficients_0796, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0796 : BottomDetBound targetTop_0796 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0796

theorem canonicalBound_0796 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 1 1 5)) 9 := by
  have htop : targetTop_0796 =
      topOfPattern (R := ℤ) (angle6 1 1 1 1 1 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0796

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 1, 1, 1, 6)`. -/
def targetTop_0797 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0797 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0797 :
    TopRowRelation targetTop_0797 relationCoefficients_0797 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0797, relationCoefficients_0797, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0797 : BottomDetBound targetTop_0797 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0797

theorem canonicalBound_0797 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 1 1 6)) 9 := by
  have htop : targetTop_0797 =
      topOfPattern (R := ℤ) (angle6 1 1 1 1 1 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0797

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 1, 1, 1, 7)`. -/
def targetTop_0798 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0798 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0798 :
    TopRowRelation targetTop_0798 relationCoefficients_0798 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0798, relationCoefficients_0798, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0798 : BottomDetBound targetTop_0798 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0798

theorem canonicalBound_0798 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 1 1 7)) 9 := by
  have htop : targetTop_0798 =
      topOfPattern (R := ℤ) (angle6 1 1 1 1 1 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0798

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 1, 1, 2, 2)`. -/
def targetTop_0799 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0799 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0799 :
    TopRowRelation targetTop_0799 relationCoefficients_0799 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0799, relationCoefficients_0799, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0799 : BottomDetBound targetTop_0799 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0799

theorem canonicalBound_0799 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 1 2 2)) 9 := by
  have htop : targetTop_0799 =
      topOfPattern (R := ℤ) (angle6 1 1 1 1 2 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0799

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard049
