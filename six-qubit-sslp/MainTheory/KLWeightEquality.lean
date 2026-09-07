import MainTheory.CodeSpec

/-! # Equality of A and B coefficients below the code distance -/

namespace MainTheory.KLWeightEquality

open scoped BigOperators
open MainTheory.CodeSpec
open SS.MacWilliams

noncomputable section

variable {n K : ℕ}

/-- Each weight layer satisfying KL has equal raw A and B coefficients. -/
theorem Bco_eq_Aco_of_detects (psi : Fin K → SS.State n ℂ) (j : ℕ)
    (h : SS.Detects psi j) : Bco psi j = Aco psi j := by
  classical
  rw [Bco, Aco, Finset.mul_sum]
  exact Finset.sum_congr rfl fun P hP =>
    frob_of_KL psi P (h P (by
      have hw := (Finset.mem_filter.mp hP).2
      omega))

/-- The existing monotone distance predicate supplies all weight layers
strictly below its stated distance. -/
theorem Bco_eq_Aco_of_hasDistance (psi : Fin K → SS.State n ℂ)
    {d j : ℕ} (h : SS.HasDistance psi d) (hj : j < d) :
    Bco psi j = Aco psi j := by
  apply Bco_eq_Aco_of_detects
  intro P hP
  apply h P
  omega

/-- The paper-normalized low-weight Knill--Laflamme identity. -/
theorem AWeight_eq_BWeight_of_hasDistance (F : OrthonormalFrame n K)
    {d j : ℕ} (h : SS.HasDistance F.vec d) (hj : j < d) :
    AWeight F j = BWeight F j := by
  unfold AWeight BWeight
  rw [Bco_eq_Aco_of_hasDistance F.vec h hj]

end

end MainTheory.KLWeightEquality
