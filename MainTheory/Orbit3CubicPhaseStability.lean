import MainTheory.Orbit3CliffordAverage
import MainTheory.FiniteCubicMoments

/-! # Global-phase invariance of actual cubic Gram entries -/

namespace MainTheory.Orbit3CubicPhaseStability

open MainTheory.Orbit3CliffordAverage MainTheory.FiniteCubicMoments
open SixQubit.CodeEquiv SixQubit.Generated.SpectatorClifford
open scoped BigOperators

noncomputable section

def monomial (t : SS.BitString 6 × SS.BitString 6 × SS.BitString 6) (w : SS.State 6 ℂ) : ℂ :=
  w t.1 * w t.2.1 * w t.2.2

def entry (t u : SS.BitString 6 × SS.BitString 6 × SS.BitString 6) (w : SS.State 6 ℂ) : ℝ :=
  (star (monomial t w) * monomial u w).re

theorem monomial_scal (t : SS.BitString 6 × SS.BitString 6 × SS.BitString 6)
    (z : ℂ) (w : SS.State 6 ℂ) : monomial t (scal z w) = z ^ 3 * monomial t w := by
  unfold monomial scal
  ring

theorem entry_phase_stable (t u : SS.BitString 6 × SS.BitString 6 × SS.BitString 6) :
    PhaseStable (entry t u) := by
  intro z w hz
  have hz3 : star (z ^ 3) * z ^ 3 = 1 := by
    rw [star_pow, ← mul_pow, hz, one_pow]
  unfold entry
  rw [monomial_scal, monomial_scal, star_mul]
  have he : star (monomial t w) * star (z ^ 3) * (z ^ 3 * monomial u w) =
      (star (z ^ 3) * z ^ 3) * (star (monomial t w) * monomial u w) := by ring
  rw [he, hz3, one_mul]

theorem actual_H_entry_identity (t u : SS.BitString 6 × SS.BitString 6 × SS.BitString 6)
    (w : SS.State 6 ℂ) :
    (∑ g : Fin 24, entry t u (act hadamard (act (clifford g) w))) =
      ∑ g : Fin 24, entry t u (act (clifford g) w) :=
  average_H _ (entry_phase_stable t u) w

end
end MainTheory.Orbit3CubicPhaseStability
