import SixQubit.Orbit9SupportCard
import SixQubit.Orbit9S2Transport

/-!
# Orbit 9: the active singleton support cannot have cardinality two

This is the finite-set wrapper around the arbitrary-label diagonal KL
contradiction.  `Finset.card_eq_two` merely selects the two active labels;
all amplitude and KL work is performed by `two_active_impossible`.
-/

namespace SixQubit.Orbit9Universal

open scoped BigOperators ComplexConjugate

noncomputable section

/-- Genuine full-fibre KL data rule out a two-element active singleton set. -/
theorem active_card_ne_two (c d : SS.State 6 ℂ) (H : FullKL c d) :
    (ActiveSet c).card ≠ 2 := by
  intro hcard
  rcases Finset.card_eq_two.mp hcard with ⟨a, b, hab, hset⟩
  apply two_active_impossible c d H a b
  refine ⟨hab, ?_, ?_, ?_⟩
  · apply (mem_ActiveSet c a).mp
    rw [hset]
    simp
  · apply (mem_ActiveSet c b).mp
    rw [hset]
    simp
  · intro i
    rw [← mem_ActiveSet c i, hset]
    simp

end

end SixQubit.Orbit9Universal
