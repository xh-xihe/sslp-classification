import MainTheory.KLWeightEquality
import SixQubit.Pin

/-!
# Six-qubit rank-two codes of distance at least three have exact distance three

The already-certified MacWilliams identities imply a strictly positive
weight-three gap `B3 - A3`.  Detection of every weight-three error would make
that gap zero, so no general quantum Singleton bound is needed.
-/

namespace MainTheory.SixQubitExactDistance

open MainTheory.CodeSpec MainTheory.KLWeightEquality
open SS.MacWilliams

noncomputable section

/-- The raw weight-three gap for every normalized rank-two six-qubit code. -/
theorem Bco_three_sub_Aco_three (psi : Fin 2 → SS.State 6 ℂ)
    (hnorm : ∀ k, SS.innerC (psi k) (psi k) = 1)
    (h3 : SS.HasDistance psi 3) :
    Bco psi 3 - Aco psi 3 =
      80 + 10 * Aco psi 1 + 4 * Aco psi 2 + Aco psi 3 := by
  have h0 := SixQubit.Pin.Aco_zero psi hnorm
  obtain ⟨h4, h5, h6⟩ := macwilliams_six psi h3 h0
  obtain ⟨_, _, _, hb3, _, _, _⟩ := bco_transform_six psi
  linarith

/-- In the manuscript's normalization the weight-three gap is at least 20. -/
theorem twenty_le_BWeight_three_sub_AWeight_three
    (F : OrthonormalFrame 6 2) (h3 : SS.HasDistance F.vec 3) :
    20 ≤ BWeight F 3 - AWeight F 3 := by
  have hnorm : ∀ k, SS.innerC (F.vec k) (F.vec k) = 1 := by
    intro k
    simpa using F.orthonormal k k
  have hgap := Bco_three_sub_Aco_three F.vec hnorm h3
  have h1 := SixQubit.Pin.Aco_nonneg F.vec 1
  have h2 := SixQubit.Pin.Aco_nonneg F.vec 2
  have h3n := SixQubit.Pin.Aco_nonneg F.vec 3
  rw [Bco_eq_four_mul_BWeight, Aco_eq_four_mul_AWeight] at hgap
  rw [Aco_eq_four_mul_AWeight] at h3n
  linarith

/-- No orthonormal rank-two six-qubit frame of distance at least three can
also detect every weight-three Pauli error. -/
theorem not_hasDistance_four (F : OrthonormalFrame 6 2)
    (h3 : SS.HasDistance F.vec 3) : ¬ SS.HasDistance F.vec 4 := by
  intro h4
  have hgap := twenty_le_BWeight_three_sub_AWeight_three F h3
  have heq := AWeight_eq_BWeight_of_hasDistance F h4 (show 3 < 4 by omega)
  linarith

/-- Exact distance three, witnessed by a physical Pauli of weight exactly
three whose Knill--Laflamme condition fails. -/
theorem exists_weight_three_not_KL (F : OrthonormalFrame 6 2)
    (h3 : SS.HasDistance F.vec 3) :
    ∃ P : SS.PauliString 6, P.wt = 3 ∧ ¬ SS.KLCondition F.vec P := by
  classical
  by_contra h
  push_neg at h
  apply not_hasDistance_four F h3
  intro P hP
  by_cases hw : P.wt = 3
  · exact h P hw
  · apply h3 P
    change P.wt ≤ 3 at hP
    change P.wt ≤ 2
    omega

/-- The existing `ExactCode 6 2 3` type therefore really has distance exactly
three at these parameters, although its generic predicate is monotone. -/
theorem exactCode_distance_three (C : ExactCode 6 2 3) :
    SS.HasDistance C.frame.vec 3 ∧ ¬ SS.HasDistance C.frame.vec 4 ∧
      ∃ P : SS.PauliString 6, P.wt = 3 ∧ ¬ SS.KLCondition C.frame.vec P :=
  ⟨C.hasDistance, not_hasDistance_four C.frame C.hasDistance,
    exists_weight_three_not_KL C.frame C.hasDistance⟩

end

end MainTheory.SixQubitExactDistance
