import SixQubit.Orbit7Spinor

/-!
# Orbit 7: the five-vertex pair-sum lemma

This is the finite linear-algebra certificate behind the pair-sum
collinearity step in the full-support branch.  The proof does not appeal to
dimension counting: fifteen concrete four-vertex equations are combined in
the kernel to kill every one of the ten two-by-two minors.
-/

namespace SixQubit.Orbit7Universal

noncomputable section

/-- Determinant of the two column vectors `(h i, delta i)` and
`(h j, delta j)`. -/
def pairDet (h delta : Fin 5 → ℂ) (i j : Fin 5) : ℂ :=
  h i * delta j - delta i * h j

/-- The manuscript's disjoint-pair condition, written without division. -/
def PairSumCondition (h delta : Fin 5 → ℂ) : Prop :=
  ∀ i j k l, i ≠ j → i ≠ k → i ≠ l →
    j ≠ k → j ≠ l → k ≠ l →
      (h i + h j) * (delta k + delta l) -
        (delta i + delta j) * (h k + h l) = 0

/-- All ten minors vanish.  Equivalently, the five vectors
`(h i, delta i)` are collinear (with the all-zero family allowed). -/
theorem pairSum_collinear (h delta : Fin 5 → ℂ)
    (hp : PairSumCondition h delta) :
    ∀ i j, pairDet h delta i j = 0 := by
  have e0123 := hp 0 1 2 3 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have e0213 := hp 0 2 1 3 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have e0312 := hp 0 3 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have e0124 := hp 0 1 2 4 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have e0214 := hp 0 2 1 4 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have e0412 := hp 0 4 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have e0134 := hp 0 1 3 4 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have e0314 := hp 0 3 1 4 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have e0413 := hp 0 4 1 3 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have e0234 := hp 0 2 3 4 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h01 : pairDet h delta 0 1 = 0 := by
    unfold pairDet
    linear_combination
      (1 / 2 : ℂ) * e0123 + (1 / 2 : ℂ) * e0213 -
      (1 / 2 : ℂ) * e0312 + (1 / 2 : ℂ) * e0124 +
      (1 / 2 : ℂ) * e0214 - (1 / 2 : ℂ) * e0412 -
      (1 / 2 : ℂ) * e0134 + (1 / 2 : ℂ) * e0314 +
      (1 / 2 : ℂ) * e0413 - e0234
  have h02 : pairDet h delta 0 2 = 0 := by
    unfold pairDet
    linear_combination
      (1 / 2 : ℂ) * e0312 + (1 / 2 : ℂ) * e0412 -
      (1 / 2 : ℂ) * e0314 - (1 / 2 : ℂ) * e0413 +
      (1 / 2 : ℂ) * e0234
  have h03 : pairDet h delta 0 3 = 0 := by
    unfold pairDet
    linear_combination
      (1 / 2 : ℂ) * e0312 - (1 / 2 : ℂ) * e0124 -
      (1 / 2 : ℂ) * e0214 + (1 / 2 : ℂ) * e0134 +
      (1 / 2 : ℂ) * e0234
  have h04 : pairDet h delta 0 4 = 0 := by
    unfold pairDet
    linear_combination
      -(1 / 2 : ℂ) * e0123 - (1 / 2 : ℂ) * e0213 +
      (1 / 2 : ℂ) * e0412 + (1 / 2 : ℂ) * e0134 +
      (1 / 2 : ℂ) * e0234
  have h12 : pairDet h delta 1 2 = 0 := by
    unfold pairDet
    linear_combination
      (1 / 2 : ℂ) * e0123 - (1 / 2 : ℂ) * e0312 +
      (1 / 2 : ℂ) * e0124 - (1 / 2 : ℂ) * e0412 -
      (1 / 2 : ℂ) * e0134 + (1 / 2 : ℂ) * e0314 +
      (1 / 2 : ℂ) * e0413 - (1 / 2 : ℂ) * e0234
  have h13 : pairDet h delta 1 3 = 0 := by
    unfold pairDet
    linear_combination
      (1 / 2 : ℂ) * e0123 - (1 / 2 : ℂ) * e0312 +
      (1 / 2 : ℂ) * e0214 - (1 / 2 : ℂ) * e0234
  have h14 : pairDet h delta 1 4 = 0 := by
    unfold pairDet
    linear_combination
      (1 / 2 : ℂ) * e0213 + (1 / 2 : ℂ) * e0124 -
      (1 / 2 : ℂ) * e0412 - (1 / 2 : ℂ) * e0234
  have h23 : pairDet h delta 2 3 = 0 := by
    unfold pairDet
    linear_combination
      (1 / 2 : ℂ) * e0213 - (1 / 2 : ℂ) * e0312 +
      (1 / 2 : ℂ) * e0124 - (1 / 2 : ℂ) * e0134
  have h24 : pairDet h delta 2 4 = 0 := by
    unfold pairDet
    linear_combination
      (1 / 2 : ℂ) * e0123 + (1 / 2 : ℂ) * e0214 -
      (1 / 2 : ℂ) * e0412 - (1 / 2 : ℂ) * e0134
  have h34 : pairDet h delta 3 4 = 0 := by
    unfold pairDet
    linear_combination
      (1 / 2 : ℂ) * e0123 - (1 / 2 : ℂ) * e0124 +
      (1 / 2 : ℂ) * e0314 - (1 / 2 : ℂ) * e0413
  have hrev (i j : Fin 5) (hz : pairDet h delta i j = 0) :
      pairDet h delta j i = 0 := by
    unfold pairDet at hz ⊢
    linear_combination -hz
  intro i j
  fin_cases i <;> fin_cases j
  · unfold pairDet; ring
  · exact h01
  · exact h02
  · exact h03
  · exact h04
  · exact hrev 0 1 h01
  · unfold pairDet; ring
  · exact h12
  · exact h13
  · exact h14
  · exact hrev 0 2 h02
  · exact hrev 1 2 h12
  · unfold pairDet; ring
  · exact h23
  · exact h24
  · exact hrev 0 3 h03
  · exact hrev 1 3 h13
  · exact hrev 2 3 h23
  · unfold pairDet; ring
  · exact h34
  · exact hrev 0 4 h04
  · exact hrev 1 4 h14
  · exact hrev 2 4 h24
  · exact hrev 3 4 h34
  · unfold pairDet; ring

/-- If one first coordinate is nonzero, collinearity has the affine form
`delta i = lambda * h i` used in the manuscript. -/
theorem pairSum_affine (h delta : Fin 5 → ℂ)
    (hp : PairSumCondition h delta) (s : Fin 5) (hs : h s ≠ 0) :
    ∃ lambda : ℂ, ∀ i, delta i = lambda * h i := by
  refine ⟨delta s / h s, ?_⟩
  intro i
  have hz := pairSum_collinear h delta hp s i
  unfold pairDet at hz
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hs).2
  linear_combination hz

end

end SixQubit.Orbit7Universal
