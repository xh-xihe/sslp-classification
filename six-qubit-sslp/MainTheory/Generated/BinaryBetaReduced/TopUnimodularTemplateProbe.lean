-- Low-resource template probe for the generated beta-six transport layer.
-- This file contains no numerical table; its hypotheses isolate the direct
-- GL(3,Z), genuine column-equivalence, and singular-relation proof shapes.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical

namespace MainTheory.Generated.BinaryBetaReduced.TopUnimodularTemplateProbe

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

def representativeTop : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 0, 1;
     0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

def targetTop : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 0, 0;
     0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

def rowTransform : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 5, 2, 3]
  invFun := ![0, 2, 4, 5, 1, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

/-- Exact proof shape emitted for every full-rank target. -/
theorem transportTemplate (h : BottomDetBound representativeTop 9) :
    BottomDetBound targetTop 9 := by
  have hU : rowTransform.det.natAbs = 1 := by
    have hdet : rowTransform.det = 1 := by decide
    simp [hdet]
  have hrows := h.transformTopRows rowTransform hU
  have hcols := hrows.permuteColumns columnPerm
  have htop :
      permuteTopColumns (transformTopRows rowTransform representativeTop)
          columnPerm = targetTop := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalTemplate (h : BottomDetBound representativeTop 9) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 3 4 6)) 9 := by
  have htop : targetTop =
      topOfPattern (R := ℤ) (angle6 0 1 2 3 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact transportTemplate h

def singularTop : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

def relationCoefficients : Fin 3 → ℤ := ![1, 1, -1]

/-- Exact proof shape emitted for every rank-deficient target. -/
theorem singularRelation :
    TopRowRelation singularTop relationCoefficients := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [singularTop, relationCoefficients, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem singularTemplate : BottomDetBound singularTop 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) singularRelation

end MainTheory.Generated.BinaryBetaReduced.TopUnimodularTemplateProbe
