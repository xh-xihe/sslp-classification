import MainTheory.MomentPolytope
import Mathlib.Analysis.Convex.Combination

/-!
# `six:eq:convintersection`: the moment programme as a convex-hull intersection

`six:eq:phi` sets `phi(x) = (x_1, ..., x_6, x_1x_2, ..., x_5x_6) in Z^21`, and
after the three displayed families of constraints -- `six:eq:lpnormal`,
`six:eq:lpmom`, `six:eq:lppos` -- the paper writes "Equivalently,
`conv phi(S_0) cap conv phi(S_delta) != varnothing`".

`MomentPolytope.Feasible` is the constraint system in coordinates, and
`momentPolytope_convex` proves the solution set convex, but no convex hull is
ever formed here: `convexHull` does not occur anywhere in `MainTheory/`,
`SixQubit/` or `SS/`, so the geometric reading of the programme -- the one that
makes a separating functional a *separating hyperplane* -- had no statement.

This file supplies it.  `momentVec` is `phi`, `momentSet` is the set of
attainable moment vectors of one colour, and

* `momentSet_eq_convexHull` -- that set is exactly `conv phi(S)`, and
* `exists_feasible_iff_momentSet_inter` / `exists_feasible_iff_convexHull_inter`
  -- the programme is feasible exactly when the two hulls meet.

The `21` of `six:eq:phi` is `6 + 15`: `Fin 6` first moments and `Pair6`
square-free second moments, which is the index type below.
-/

namespace MainTheory.MomentConvexHull

open MainTheory.MomentPolytope

/-- The index set of `six:eq:phi`: six first moments and fifteen square-free
second moments, `21` coordinates in all. -/
abbrev MomentIndex := Fin 6 ⊕ Pair6

/-- **`phi` of `six:eq:phi`.** -/
def momentVec (x : BitPoint6) : MomentIndex → ℝ
  | Sum.inl j => coord x j
  | Sum.inr jk => coord x jk.1.1 * coord x jk.1.2

variable {I : Type*} [Fintype I]

/-- The attainable degree-`<= 2` moment vectors of one colour: the images of
the probability simplex under `phi`. -/
def momentSet (x : I → BitPoint6) : Set (MomentIndex → ℝ) :=
  {v | ∃ w : I → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • momentVec (x i) = v}

/-- **The attainable moment vectors are exactly `conv phi(S)`.** -/
theorem momentSet_eq_convexHull (x : I → BitPoint6) :
    momentSet x = convexHull ℝ (Set.range fun i => momentVec (x i)) := by
  classical
  ext v
  constructor
  · rintro ⟨w, hw0, hw1, rfl⟩
    have := Finset.centerMass_mem_convexHull (R := ℝ) (Finset.univ : Finset I)
      (w := w) (z := fun i => momentVec (x i)) (fun i _ => hw0 i)
      (by rw [hw1]; norm_num) (fun i _ => Set.mem_range_self i)
    rwa [Finset.centerMass_eq_of_sum_1 _ _ hw1] at this
  · intro hv
    rw [convexHull_range_eq_exists_affineCombination] at hv
    obtain ⟨s, w, hw0, hw1, rfl⟩ := hv
    refine ⟨fun i => if i ∈ s then w i else 0, ?_, ?_, ?_⟩
    · intro i
      by_cases hi : i ∈ s
      · simpa [hi] using hw0 i hi
      · simp [hi]
    · rw [Finset.sum_ite_mem, Finset.univ_inter, hw1]
    · rw [affineCombination_eq_centerMass hw1,
        Finset.centerMass_eq_of_sum_1 _ _ hw1]
      rw [← Finset.sum_subset (Finset.subset_univ s)]
      · refine Finset.sum_congr rfl fun i hi => ?_
        simp [hi]
      · intro i _ hi
        simp [hi]

variable {I₀ I₁ : Type*} [Fintype I₀] [Fintype I₁]

/-- **The programme is feasible exactly when the two moment sets meet.**

Splitting `p` into its two colour blocks turns `norm0`/`norm1` into the two
simplex conditions and `firstMoment`/`secondMoment` into equality of the two
moment vectors, coordinate by coordinate. -/
theorem exists_feasible_iff_momentSet_inter
    (x₀ : I₀ → BitPoint6) (x₁ : I₁ → BitPoint6) :
    (∃ p : Sum I₀ I₁ → ℝ, Feasible x₀ x₁ p) ↔
      (momentSet x₀ ∩ momentSet x₁).Nonempty := by
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨∑ i : I₀, p (Sum.inl i) • momentVec (x₀ i), ?_, ?_⟩
    · exact ⟨fun i => p (Sum.inl i), fun i => hp.nonneg _, hp.norm0, rfl⟩
    · refine ⟨fun i => p (Sum.inr i), fun i => hp.nonneg _, hp.norm1, ?_⟩
      funext c
      cases c with
      | inl j =>
          have h := hp.firstMoment j
          simpa [momentVec, mean0, mean1, Finset.sum_apply, smul_eq_mul] using h.symm
      | inr jk =>
          have h := hp.secondMoment jk
          simpa [momentVec, second0, second1, Finset.sum_apply, smul_eq_mul,
            mul_assoc] using h.symm
  · rintro ⟨v, ⟨w₀, hw₀0, hw₀1, hv₀⟩, ⟨w₁, hw₁0, hw₁1, hv₁⟩⟩
    refine ⟨Sum.elim w₀ w₁, ?_, ?_, ?_, ?_, ?_⟩
    · rintro (i | i) <;> simp [hw₀0, hw₁0]
    · simpa using hw₀1
    · simpa using hw₁1
    · intro j
      have h := congrFun (hv₀.trans hv₁.symm) (Sum.inl j)
      simpa [momentVec, mean0, mean1, Finset.sum_apply, smul_eq_mul] using h
    · intro jk
      have h := congrFun (hv₀.trans hv₁.symm) (Sum.inr jk)
      simpa [momentVec, second0, second1, Finset.sum_apply, smul_eq_mul,
        mul_assoc] using h

/-- **`six:eq:convintersection`.** -/
theorem exists_feasible_iff_convexHull_inter
    (x₀ : I₀ → BitPoint6) (x₁ : I₁ → BitPoint6) :
    (∃ p : Sum I₀ I₁ → ℝ, Feasible x₀ x₁ p) ↔
      (convexHull ℝ (Set.range fun i => momentVec (x₀ i)) ∩
        convexHull ℝ (Set.range fun i => momentVec (x₁ i))).Nonempty := by
  rw [← momentSet_eq_convexHull, ← momentSet_eq_convexHull]
  exact exists_feasible_iff_momentSet_inter x₀ x₁

end MainTheory.MomentConvexHull
