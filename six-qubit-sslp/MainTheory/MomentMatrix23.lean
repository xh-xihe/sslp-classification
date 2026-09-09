import MainTheory.FiniteMomentLP

namespace MainTheory.MomentMatrix23

open MainTheory.FinitePipeline MainTheory.FiniteMomentMatrix

variable {I J : Type*} [Fintype I] [Fintype J]

def column (left : I → Word6) (right : J → Word6) : Sum I J → LabeledWord :=
  Sum.elim (fun i => (false, left i)) (fun j => (true, right j))

def matrixQ (left : I → Word6) (right : J → Word6) : Matrix (Fin 23) (Sum I J) ℚ :=
  (matrixZ (column left right)).map (Int.castRingHom ℚ)

theorem row_zero (left : I → Word6) (right : J → Word6) (p : Sum I J → ℚ) :
    (matrixQ left right).mulVec p 0 = ∑ i, p (.inl i) := by
  simp [matrixQ, matrixZ, column, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, entryZ_norm_zero]

theorem row_one (left : I → Word6) (right : J → Word6) (p : Sum I J → ℚ) :
    (matrixQ left right).mulVec p 1 = ∑ j, p (.inr j) := by
  simp [matrixQ, matrixZ, column, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, entryZ_norm_one]

theorem row_moment (left : I → Word6) (right : J → Word6)
    (p : Sum I J → ℚ) (i : Fin 21) :
    (matrixQ left right).mulVec p (Fin.natAdd 2 i) =
      (∑ x, p (.inl x) * feature (left x) i) -
        ∑ y, p (.inr y) * feature (right y) i := by
  simp [matrixQ, matrixZ, column, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    entryZ_moment, featureZ_eq_feature, mul_comm, sub_eq_add_neg]

theorem feasible_iff (left : I → Word6) (right : J → Word6) (p : Sum I J → ℚ) :
    MainTheory.ExactLP.Feasible (matrixQ left right) rhsQ p ↔
      (∀ z, 0 ≤ p z) ∧ (∑ i, p (.inl i)) = 1 ∧ (∑ j, p (.inr j)) = 1 ∧
        ∀ i : Fin 21, (∑ x, p (.inl x) * feature (left x) i) =
          ∑ y, p (.inr y) * feature (right y) i := by
  constructor
  · rintro ⟨he, hn⟩
    refine ⟨hn, ?_, ?_, ?_⟩
    · exact (row_zero left right p).symm.trans (congrFun he 0)
    · exact (row_one left right p).symm.trans (congrFun he 1)
    · intro i
      have h := congrFun he (Fin.natAdd 2 i)
      rw [row_moment] at h
      apply sub_eq_zero.mp
      simpa [rhsQ, Fin.append_right] using h
  · rintro ⟨hn, h0, h1, hm⟩
    refine ⟨?_, hn⟩
    funext r
    refine Fin.addCases (m := 2) (n := 21) ?_ ?_ r
    · intro i
      fin_cases i
      · exact (row_zero left right p).trans h0
      · exact (row_one left right p).trans h1
    · intro i
      rw [row_moment]
      simpa [rhsQ, Fin.append_right] using sub_eq_zero.mpr (hm i)

theorem exact_rational_iff_real (left : I → Word6) (right : J → Word6) :
    (∃ p, MainTheory.ExactLP.Feasible (matrixQ left right) rhsQ p) ↔
      ∃ p, MainTheory.ExactLP.RealFeasible (matrixQ left right) rhsQ p :=
  MainTheory.ExactLP.rational_feasible_iff_real _ _

end MainTheory.MomentMatrix23
