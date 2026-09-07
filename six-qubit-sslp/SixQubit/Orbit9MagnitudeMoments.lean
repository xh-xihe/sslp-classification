import SixQubit.Orbit9UniversalFinal

/-! Exact two-coordinate occupation formulas on the two complete uniform
orbit-9 fibers.  These formulas retain every amplitude, including zeros. -/

namespace SixQubit.Orbit9Universal

open scoped BigOperators ComplexConjugate
open SS.MacWilliams

noncomputable section

set_option maxHeartbeats 8000000 in
theorem occ2_S0_magnitudes (c : SS.State 6 ℂ) (i j : Fin 6) (hij : i ≠ j) :
    SixQubit.occ2On S0 c i j = Rmass c - Rdeg c i - Rdeg c j + r c i j := by
  classical
  rw [SixQubit.occ2On, Finset.sum_filter, sum_S0, Rmass_edges]
  fin_cases i <;> fin_cases j
  all_goals try exact (hij rfl).elim
  all_goals
    simp [Rdeg, r, Fin.sum_univ_succ, one, pair, SS.bxor, SS.complement]
    ring

set_option maxHeartbeats 8000000 in
theorem occ2_S1_magnitudes (d : SS.State 6 ℂ) (i j : Fin 6) (hij : i ≠ j) :
    SixQubit.occ2On S1 d i j = Qmass d - q d i - q d j + s d i j := by
  classical
  rw [SixQubit.occ2On, Finset.sum_filter, sum_S1]
  fin_cases i <;> fin_cases j
  all_goals try exact (hij rfl).elim
  all_goals
    simp [Qmass, q, s, Fin.sum_univ_succ, one, pair, SS.bxor, SS.complement]
    ring

/-- The two edge-probability matrices coincide, including boundary zeros. -/
theorem edge_magnitudes_equal (c d : SS.State 6 ℂ) (H : FullKL c d)
    (i j : Fin 6) : r c i j = s d i j := by
  by_cases hij : i = j
  · subst j
    simp [r, s]
  have he := SixQubit.occ2On_eq_of_hasDistance S0 S1 c d
    H.support0 H.support1 H.norm0 H.norm1 H.distance i j
  rw [occ2_S0_magnitudes c i j hij, occ2_S1_magnitudes d i j hij] at he
  have hm := global_masses c d H.support0 H.support1 H.norm0 H.norm1 H.distance
  have hi := pq_degree c d H.support0 H.support1 H.norm0 H.norm1 H.distance i
  have hj := pq_degree c d H.support0 H.support1 H.norm0 H.norm1 H.distance j
  linarith [hm.2.1, hm.2.2.2, hi.1, hi.2.1, hj.1, hj.2.1]

end
end SixQubit.Orbit9Universal
