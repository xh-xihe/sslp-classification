import SixQubit.Orbit31MomentRank
import MainTheory.LPDimension

/-! The orbit-31 matrix is the actual full-fiber moment polytope.  Its
strictly positive uniform point makes the affine dimension exactly nine. -/

namespace SixQubit.Orbit31
open scoped BigOperators Matrix
noncomputable section

set_option maxHeartbeats 4000000

theorem matrix_constraints_iff_vectorMomentSystem (q r : Fin 16 → ℝ) :
    (momentMatrix *ᵥ joinProbabilities q r = momentRhs ∧
      (∀ i, 0 ≤ q i) ∧ (∀ i, 0 ≤ r i)) ↔ VectorMomentSystem q r := by
  rw [momentMatrix_mulVec_join]
  constructor
  · rintro ⟨he,hq,hr⟩
    simp only [momentRhs, Matrix.vecCons_inj, and_true] at he
    rcases he with ⟨hn0,hn1,hm1,hm2,hm3,hm4,hm5,hm6,hc12,hc13,hc14,hc15,hc16,hc23,hc24,hc25,hc26,hc34,hc35,hc36,hc45,hc46,hc56⟩
    constructor
    all_goals first
    | exact hq _
    | exact hr _
    | linarith only [hn0,hn1,hm1,hm2,hm3,hm4,hm5,hm6,hc12,hc13,hc14,hc15,hc16,hc23,hc24,hc25,hc26,hc34,hc35,hc36,hc45,hc46,hc56]
  · intro h
    refine ⟨?_,?_,?_⟩
    · simp only [momentRhs, Matrix.vecCons_inj, and_true]
      refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
      all_goals linarith only [h.n0,h.n1,h.m1,h.m2,h.m3,h.m4,h.m5,h.m6,h.c12,h.c13,h.c14,h.c15,h.c16,h.c23,h.c24,h.c25,h.c26,h.c34,h.c35,h.c36,h.c45,h.c46,h.c56]
    · intro i
      fin_cases i
      · exact h.nq0
      · exact h.nq1
      · exact h.nq2
      · exact h.nq3
      · exact h.nq4
      · exact h.nq5
      · exact h.nq6
      · exact h.nq7
      · exact h.nq8
      · exact h.nq9
      · exact h.nq10
      · exact h.nq11
      · exact h.nq12
      · exact h.nq13
      · exact h.nq14
      · exact h.nq15
    · intro i
      fin_cases i
      · exact h.nr0
      · exact h.nr1
      · exact h.nr2
      · exact h.nr3
      · exact h.nr4
      · exact h.nr5
      · exact h.nr6
      · exact h.nr7
      · exact h.nr8
      · exact h.nr9
      · exact h.nr10
      · exact h.nr11
      · exact h.nr12
      · exact h.nr13
      · exact h.nr14
      · exact h.nr15

theorem joinProbabilities_eq_append (q r : Fin 16 → ℝ) :
    joinProbabilities q r = Fin.append q r := by
  ext i
  fin_cases i <;> rfl

theorem joinProbabilities_nonnegative (q r : Fin 16 → ℝ) :
    (∀ i, 0 ≤ joinProbabilities q r i) ↔ (∀ i, 0 ≤ q i) ∧ (∀ i, 0 ≤ r i) := by
  rw [joinProbabilities_eq_append]
  constructor
  · intro h
    exact ⟨fun i => by simpa only [Fin.append_left] using h (Fin.castAdd 16 i),
      fun i => by simpa only [Fin.append_right] using h (Fin.natAdd 16 i)⟩
  · rintro ⟨hq,hr⟩ i
    exact Fin.addCases (motive := fun k => 0 ≤ Fin.append q r k)
      (fun j => by simpa only [Fin.append_left] using hq j)
      (fun j => by simpa only [Fin.append_right] using hr j) i

/-- The complete probability polytope, with all thirty-two nonnegativity
constraints still present. -/
def momentPolytope : Set (Fin 32 → ℝ) :=
  MainTheory.LPDimension.feasibleSet momentMatrix momentRhs

theorem join_mem_momentPolytope_iff (q r : Fin 16 → ℝ) :
    joinProbabilities q r ∈ momentPolytope ↔ VectorMomentSystem q r := by
  change (momentMatrix *ᵥ joinProbabilities q r = momentRhs ∧
    ∀ i, 0 ≤ joinProbabilities q r i) ↔ _
  rw [joinProbabilities_nonnegative]
  exact matrix_constraints_iff_vectorMomentSystem q r

/-- Every point in the matrix polytope has precisely the stated full-fiber
normal form; conversely every nonnegative normal-form table is a point. -/
theorem momentPolytope_iff_normalForm (x : Fin 32 → ℝ) :
    x ∈ momentPolytope ↔
      MomentNormalForm (fun i => x (Fin.castAdd 16 i))
        (fun i => x (Fin.natAdd 16 i)) := by
  have hj : joinProbabilities (fun i => x (Fin.castAdd 16 i))
      (fun i => x (Fin.natAdd 16 i)) = x := by
    rw [joinProbabilities_eq_append]
    exact Fin.append_castAdd_natAdd
  rw [← vectorMomentSystem_iff_normalForm, ← join_mem_momentPolytope_iff, hj]

theorem uniform_momentPolytope_point :
    (fun _ : Fin 32 => (1/16 : ℝ)) ∈ momentPolytope := by
  rw [momentPolytope_iff_normalForm]
  constructor
  · ext i
    fin_cases i <;> rfl
  all_goals norm_num

/-- The supplementary LP dimension is the actual affine-hull dimension,
not just a count of free parameters before imposing nonnegativity. -/
theorem momentPolytope_affine_dimension :
    Module.finrank ℝ (affineSpan ℝ momentPolytope).direction = 9 := by
  have heq : momentMatrix *ᵥ (fun _ : Fin 32 => (1/16 : ℝ)) = momentRhs :=
    uniform_momentPolytope_point.1
  have hd := MainTheory.LPDimension.finrank_eq_card_sub_rank_of_positive
    momentMatrix momentRhs (fun _ => 1/16) heq (by intro i; norm_num)
  simpa [momentPolytope, momentMatrix_rank] using hd

end
end SixQubit.Orbit31
