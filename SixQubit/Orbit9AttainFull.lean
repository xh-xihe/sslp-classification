import SixQubit.Orbit9Attain
import SixQubit.BEnumerator

/-!
# Orbit 9: bundled exact attainment

This module packages the exhibited algebraic code with all data required by
the orbit-level certification statement: original-fibre support, both exact
normalizations, genuine Knill--Laflamme distance, and the complete `A/B`
enumerator pair.
-/

namespace SixQubit.Orbit9Attain

open SS.MacWilliams SixQubit SixQubit.Pin SixQubit.Orbit9Real

noncomputable section

theorem w0_full_fibre :
    ∀ x, SS.weight av x ≠ 0 → w0 x = 0 := by
  intro x hx
  apply w0_vanishes x
  intro hmem
  exact hx (L0_in_fiber x hmem)

theorem w1_full_fibre :
    ∀ x, SS.weight av x ≠ 1 → w1 x = 0 := by
  intro x hx
  apply w1_vanishes x
  intro hmem
  exact hx (L1_in_fiber x hmem)

theorem enumerator_pair_attained :
    IsE2A ![w0, w1] ∧ IsE2B ![w0, w1] := by
  have hnorm : ∀ k, SS.innerC ((![w0, w1] : Fin 2 → SS.State 6 ℂ) k)
      ((![w0, w1] : Fin 2 → SS.State 6 ℂ) k) = 1 := by
    intro k
    fin_cases k
    · exact w0_normalized
    · exact w1_normalized
  have hA0 := Aco_zero ![w0, w1] hnorm
  rcases enumerator with ⟨hA1, hA2, hA3, hA4, hA5, hA6⟩
  have hA : IsE2A ![w0, w1] :=
    ⟨hA0, hA1, hA2, hA3, hA4, hA5, hA6⟩
  exact ⟨hA, e2B_of_e2A _ hA⟩

/-- A single theorem exposing every kernel-checked attainment obligation. -/
theorem fully_certified_attainment :
    ∃ c d : SS.State 6 ℂ,
      (∀ x, SS.weight av x ≠ 0 → c x = 0) ∧
      (∀ x, SS.weight av x ≠ 1 → d x = 0) ∧
      SS.innerC c c = 1 ∧ SS.innerC d d = 1 ∧
      SS.HasDistance ![c,d] 3 ∧
      IsE2A ![c,d] ∧ IsE2B ![c,d] := by
  refine ⟨w0, w1, w0_full_fibre, w1_full_fibre,
    w0_normalized, w1_normalized, is_code, ?_⟩
  exact enumerator_pair_attained

end

end SixQubit.Orbit9Attain
