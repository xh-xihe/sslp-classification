import Mathlib
import SixQubit.Orbit21Farkas
import SixQubit.Orbit21Real
import SixQubit.BEnumerator

/-!
# Orbit 21: the fully kernel-certified enumerator image

The theorem in this file is quantified over arbitrary amplitudes supported in
the two *full* orbit fibres.  It combines the support-level Walsh certificate
of `Orbit21Residual`, the exact Farkas expansion of `Orbit21Farkas`, the scalar
shadow squeeze, and the complete six-qubit MacWilliams transform.  The explicit
code in `Orbit21Real` proves attainment.
-/

namespace SixQubit.Orbit21Enum

open SS.MacWilliams SixQubit.Pin

/-- **The exact A/B image of every orbit-21 code.** -/
theorem enumerator_pair_unique_fiber (c d : SS.State 6 ℂ)
    (hc : ∀ s, SS.weight Orbit21Cert.av s ≠ 0 → c s = 0)
    (hd : ∀ s, SS.weight Orbit21Cert.av s ≠ 2 → d s = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) :
    IsE2A ![c, d] ∧ IsE2B ![c, d] := by
  let psi : Fin 2 → SS.State 6 ℂ := ![c, d]
  have hnorm : ∀ k, SS.innerC (psi k) (psi k) = 1 := by
    intro k
    fin_cases k
    · exact hnc
    · exact hnd
  have hlow : 4 ≤ Aco psi 2 :=
    Orbit21Farkas.four_le_Aco_two psi hc hd hnorm hdist
  have hA0 : Aco psi 0 = 4 := Aco_zero psi hnorm
  rcases Orbit21Bound.enumerator_of_A2_bound psi hdist hA0 hlow with
    ⟨hA1, hA2, hA3, hA4, hA5, hA6⟩
  have hA : IsE2A psi := ⟨hA0, hA1, hA2, hA3, hA4, hA5, hA6⟩
  exact ⟨hA, e2B_of_e2A psi hA⟩

/-- The explicit exact code supplies a point in the full-fibre problem. -/
theorem enumerator_pair_attained :
    IsE2A ![Orbit21Real.w0, Orbit21Real.w1] ∧
      IsE2B ![Orbit21Real.w0, Orbit21Real.w1] := by
  apply enumerator_pair_unique_fiber Orbit21Real.w0 Orbit21Real.w1
  · intro s hs
    apply Orbit21Real.w0_vanishes s
    intro hL
    exact hs (Orbit21Real.L0_in_fiber s hL)
  · intro s hs
    apply Orbit21Real.w1_vanishes s
    intro hL
    exact hs (Orbit21Real.L1_in_fiber s hL)
  · exact Orbit21Real.w0_normalized
  · exact Orbit21Real.w1_normalized
  · exact Orbit21Real.is_code

/-- One code-level headline exposing both the universal exact image and a
genuine point attaining it.  In particular, nonemptiness is not represented
only by an enumerator equality for an otherwise opaque pair of states. -/
theorem fully_certified :
    (∀ c d : SS.State 6 ℂ,
      (∀ s, SS.weight Orbit21Cert.av s ≠ 0 → c s = 0) →
      (∀ s, SS.weight Orbit21Cert.av s ≠ 2 → d s = 0) →
      SS.innerC c c = 1 → SS.innerC d d = 1 →
      SS.HasDistance ![c,d] 3 →
      IsE2A ![c,d] ∧ IsE2B ![c,d]) ∧
    (∃ c d : SS.State 6 ℂ,
      (∀ s, SS.weight Orbit21Cert.av s ≠ 0 → c s = 0) ∧
      (∀ s, SS.weight Orbit21Cert.av s ≠ 2 → d s = 0) ∧
      SS.innerC c c = 1 ∧ SS.innerC d d = 1 ∧
      SS.HasDistance ![c,d] 3 ∧
      IsE2A ![c,d] ∧ IsE2B ![c,d]) := by
  constructor
  · intro c d hc hd hnc hnd hdist
    exact enumerator_pair_unique_fiber c d hc hd hnc hnd hdist
  · refine ⟨Orbit21Real.w0, Orbit21Real.w1, ?_, ?_,
      Orbit21Real.w0_normalized, Orbit21Real.w1_normalized,
      Orbit21Real.is_code, enumerator_pair_attained.1,
      enumerator_pair_attained.2⟩
    · intro s hs
      apply Orbit21Real.w0_vanishes s
      intro hL
      exact hs (Orbit21Real.L0_in_fiber s hL)
    · intro s hs
      apply Orbit21Real.w1_vanishes s
      intro hL
      exact hs (Orbit21Real.L1_in_fiber s hL)

end SixQubit.Orbit21Enum
