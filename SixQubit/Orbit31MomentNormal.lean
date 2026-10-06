import SixQubit.Orbit31

/-! The complete iff normal form of the orbit-31 diagonal moment system.
The vector order is the actual lexical fiber order used in Orbit31. -/

namespace SixQubit.Orbit31

open scoped BigOperators
noncomputable section

def VectorMomentSystem (q r : Fin 16 → ℝ) : Prop :=
  MomentSystem (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) (q 6) (q 7) (q 8) (q 9) (q 10) (q 11) (q 12) (q 13) (q 14) (q 15) (r 0) (r 1) (r 2) (r 3) (r 4) (r 5) (r 6) (r 7) (r 8) (r 9) (r 10) (r 11) (r 12) (r 13) (r 14) (r 15)

structure MomentNormalForm (q r : Fin 16 → ℝ) : Prop where
  complement : r = ![q 15,q 14,q 13,q 12,q 11,q 10,q 9,q 8,q 7,q 6,q 5,q 4,q 3,q 2,q 1,q 0]
  row1 : q 4 + q 5 + q 6 + q 7 = 1/4
  row2 : q 8 + q 9 + q 10 + q 11 = 1/4
  row3 : q 12 + q 13 + q 14 + q 15 = 1/4
  col0 : q 0 = q 7 + q 11 + q 15 - 1/8
  col1 : q 1 = q 6 + q 10 + q 14 - 1/8
  col2 : q 2 = q 5 + q 9 + q 13 - 1/8
  col3 : q 3 = q 4 + q 8 + q 12 - 1/8
  nonneg : ∀ i, 0 ≤ q i

theorem normalForm_of_vectorMomentSystem (q r : Fin 16 → ℝ)
    (h : VectorMomentSystem q r) : MomentNormalForm q r := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · ext i
    fin_cases i
    · have he := eq15 h
      simpa using (show r 0 = q 15 by linarith)
    · have he := eq14 h
      simpa using (show r 1 = q 14 by linarith)
    · have he := eq13 h
      simpa using (show r 2 = q 13 by linarith)
    · have he := eq12 h
      simpa using (show r 3 = q 12 by linarith)
    · have he := eq11 h
      simpa using (show r 4 = q 11 by linarith)
    · have he := eq10 h
      simpa using (show r 5 = q 10 by linarith)
    · have he := eq9 h
      simpa using (show r 6 = q 9 by linarith)
    · have he := eq8 h
      simpa using (show r 7 = q 8 by linarith)
    · have he := eq7 h
      simpa using (show r 8 = q 7 by linarith)
    · have he := eq6 h
      simpa using (show r 9 = q 6 by linarith)
    · have he := eq5 h
      simpa using (show r 10 = q 5 by linarith)
    · have he := eq4 h
      simpa using (show r 11 = q 4 by linarith)
    · have he := eq3 h
      simpa using (show r 12 = q 3 by linarith)
    · have he := eq2 h
      simpa using (show r 13 = q 2 by linarith)
    · have he := eq1 h
      simpa using (show r 14 = q 1 by linarith)
    · have he := eq0 h
      simpa using (show r 15 = q 0 by linarith)
  · have he := row1 h
    linarith
  · have he := row2 h
    linarith
  · have he := row3 h
    linarith
  · have he := col0 h
    linarith
  · have he := col1 h
    linarith
  · have he := col2 h
    linarith
  · have he := col3 h
    linarith
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

theorem vectorMomentSystem_of_normalForm (q r : Fin 16 → ℝ)
    (h : MomentNormalForm q r) : VectorMomentSystem q r := by
  rw [h.complement]
  unfold VectorMomentSystem
  change MomentSystem (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) (q 6) (q 7) (q 8) (q 9) (q 10) (q 11) (q 12) (q 13) (q 14) (q 15) (q 15) (q 14) (q 13) (q 12) (q 11) (q 10) (q 9) (q 8) (q 7) (q 6) (q 5) (q 4) (q 3) (q 2) (q 1) (q 0)
  constructor
  all_goals first
  | exact h.nonneg _
  | linarith only [h.row1,h.row2,h.row3,h.col0,h.col1,h.col2,h.col3]

/-- The exact twenty-three moment equations and nonnegativity are equivalent
to complement equality, three quarter-mass rows, and four column formulas. -/
theorem vectorMomentSystem_iff_normalForm (q r : Fin 16 → ℝ) :
    VectorMomentSystem q r ↔ MomentNormalForm q r :=
  ⟨normalForm_of_vectorMomentSystem q r, vectorMomentSystem_of_normalForm q r⟩

end
end SixQubit.Orbit31
