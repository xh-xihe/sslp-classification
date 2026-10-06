import MainTheory.ParityFourMoments

/-!
The positive parity support graph and every fixed-coordinate slice.  The graph
uses the actual probabilities from the moment normal form and Hamming-one edges.
-/

namespace MainTheory.ParityFour

open scoped BigOperators

noncomputable section

def positiveGraph (a : Fin 4 → ℝ) : SimpleGraph {x : Cube //
    BooleanCube.slice ∅ (fun _ => false) x ∧ 0 < probability a x} :=
  BooleanCube.supportGraph (BooleanCube.slice ∅ (fun _ => false)) (probability a)

def positiveSliceGraph (a : Fin 4 → ℝ) (i : Fin 4) (b : Bool) :=
  BooleanCube.supportGraph (BooleanCube.slice {i} (fun _ => b)) (probability a)

theorem probability_eq_score (a : Fin 4 → ℝ) :
    probability a = BooleanCube.score (fun i => a i / 8) (1 / 8) := by
  funext x
  simp only [probability, BooleanCube.score]
  rw [add_div, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- This applies also at every boundary face and vertex of the cross-polytope. -/
theorem positiveGraph_connected (a : Fin 4 → ℝ) : (positiveGraph a).Connected := by
  unfold positiveGraph
  rw [probability_eq_score]
  exact BooleanCube.positive_support_connected _ _ (by norm_num)

theorem positiveSliceGraph_empty_or_connected (a : Fin 4 → ℝ) (i : Fin 4) (b : Bool) :
    IsEmpty {x : Cube // BooleanCube.slice {i} (fun _ => b) x ∧ 0 < probability a x} ∨
      (positiveSliceGraph a i b).Connected := by
  unfold positiveSliceGraph
  rw [probability_eq_score]
  exact BooleanCube.positive_slice_empty_or_connected _ _ _ _

theorem single_coordinate_iff_hamming_one (x y : Cube) :
    (∃ i, x i ≠ y i ∧ ∀ j, j ≠ i → x j = y j) ↔ SS.hammingWt (SS.bxor x y) = 1 := by
  have h : ∀ x y : Cube,
      (∃ i, x i ≠ y i ∧ ∀ j, j ≠ i → x j = y j) ↔ SS.hammingWt (SS.bxor x y) = 1 := by
    decide
  exact h x y

theorem hamming_one_changes_parity (x y : Cube) (h : SS.hammingWt (SS.bxor x y) = 1) :
    parity x ≠ parity y := by
  have hp : ∀ x y : Cube, SS.hammingWt (SS.bxor x y) = 1 → parity x ≠ parity y := by decide
  exact hp x y h

theorem positiveGraph_adj_iff_hamming_one (a : Fin 4 → ℝ)
    (x y : {x : Cube // BooleanCube.slice ∅ (fun _ => false) x ∧ 0 < probability a x}) :
    (positiveGraph a).Adj x y ↔ SS.hammingWt (SS.bxor x.val y.val) = 1 :=
  single_coordinate_iff_hamming_one _ _

theorem positiveSliceGraph_adj_iff (a : Fin 4 → ℝ) (i : Fin 4) (b : Bool)
    (x y : {x : Cube // BooleanCube.slice {i} (fun _ => b) x ∧ 0 < probability a x}) :
    (positiveSliceGraph a i b).Adj x y ↔
      ∃ j, j ≠ i ∧ x.val j ≠ y.val j ∧ ∀ k, k ≠ j → x.val k = y.val k := by
  constructor
  · rintro ⟨j, hj, h⟩
    refine ⟨j, ?_, hj, h⟩
    intro heq
    subst j
    have hx := x.property.1 i (by simp)
    have hy := y.property.1 i (by simp)
    exact hj (hx.trans hy.symm)
  · rintro ⟨j, _, hj, h⟩
    exact ⟨j, hj, h⟩

end
end MainTheory.ParityFour
