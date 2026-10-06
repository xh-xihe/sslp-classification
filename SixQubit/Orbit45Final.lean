import SixQubit.Orbit45Interval

/-!
# Orbit 45: final fully kernel-certified image

This file exposes the two directions of the manuscript theorem at source
level.  The converse quantifies over arbitrary amplitudes on the two complete
`av`-fibres (support is allowed to be a proper subset at boundary points) and
assumes only normalization and the genuine kernel-level
distance predicate.  The constructive direction returns actual full-fibre
codewords for every `t ∈ [2/3,1]`, with their complete raw A/B enumerators.
-/

namespace SixQubit.Orbit45Final

open SixQubit.Realize
open SixQubit.Orbit45Support
open SixQubit.Orbit45Family

noncomputable section

/-- **Source-level universal orbit-45 converse.**  Every normalized genuine
distance-three code supported on the two complete orbit-45 fibres has exactly
the manuscript's A/B enumerators at a parameter in `[2/3,1]`. -/
theorem universal_converse_full_fibres (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ y, SS.weight av y ≠ 3 → d y = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) :
    ∃ t : ℝ, (2/3 : ℝ) ≤ t ∧ t ≤ 1 ∧
      IsFamilyA ![c,d] t ∧ IsFamilyB ![c,d] t := by
  have hcS : ∀ x, x ∉ S0 → c x = 0 := by
    intro x hx
    apply hc x
    intro hwt
    apply hx
    rw [← S0_eq_fiber]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hwt⟩
  have hdS : ∀ y, y ∉ S1 → d y = 0 := by
    intro y hy
    apply hd y
    intro hwt
    apply hy
    rw [← S1_eq_fiber]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, hwt⟩
  exact universal_family c d hcS hdS hnc hnd hcode

/-- **Pointwise attainment of the exact orbit-45 interval.**  For every
`t ∈ [2/3,1]` this returns two actual normalized states supported on the two
complete fibres and satisfying genuine `HasDistance`, together with the exact
complete raw A/B families.  It does not claim that every fibre amplitude is
nonzero; endpoint members may have smaller support. -/
theorem interval_attainment_full_fibres (t : ℝ)
    (hlo : (2/3 : ℝ) ≤ t) (hi : t ≤ 1) :
    ∃ c d : SS.State 6 ℂ,
      (∀ x, SS.weight av x ≠ 0 → c x = 0) ∧
      (∀ y, SS.weight av y ≠ 3 → d y = 0) ∧
      SS.innerC c c = 1 ∧ SS.innerC d d = 1 ∧
      SS.HasDistance ![c,d] 3 ∧
      IsFamilyA ![c,d] t ∧ IsFamilyB ![c,d] t := by
  exact SixQubit.Orbit45Attain.interval_attainment_full_fibres t hlo hi

/-- A single theorem exposing both directions of the exact orbit-45
weight-enumerator image stated in the manuscript. -/
theorem fully_certified :
    (∀ (c d : SS.State 6 ℂ),
      (∀ x, SS.weight av x ≠ 0 → c x = 0) →
      (∀ y, SS.weight av y ≠ 3 → d y = 0) →
      SS.innerC c c = 1 → SS.innerC d d = 1 →
      SS.HasDistance ![c,d] 3 →
      ∃ t : ℝ, (2/3 : ℝ) ≤ t ∧ t ≤ 1 ∧
        IsFamilyA ![c,d] t ∧ IsFamilyB ![c,d] t) ∧
    (∀ t : ℝ, (2/3 : ℝ) ≤ t → t ≤ 1 →
      ∃ c d : SS.State 6 ℂ,
        (∀ x, SS.weight av x ≠ 0 → c x = 0) ∧
        (∀ y, SS.weight av y ≠ 3 → d y = 0) ∧
        SS.innerC c c = 1 ∧ SS.innerC d d = 1 ∧
        SS.HasDistance ![c,d] 3 ∧
        IsFamilyA ![c,d] t ∧ IsFamilyB ![c,d] t) := by
  constructor
  · intro c d hc hd hnc hnd hcode
    exact universal_converse_full_fibres c d hc hd hnc hnd hcode
  · intro t hlo hi
    exact interval_attainment_full_fibres t hlo hi

end

end SixQubit.Orbit45Final
