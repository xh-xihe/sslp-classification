import SixQubit.Orbit9NoTwo
import SixQubit.Orbit9EqualPairBridge
import SixQubit.Orbit9AttainFull

/-!
# Orbit 9: universal original-gauge certification and attainment

This file is the top-level composition theorem.  Its universal input consists
only of the two complete original orbit-9 fibre conditions, exact
normalization of both logical words, and genuine distance three.  The proof
translates to the uniform gauge, closes the two-point branch, obtains the
four-point branch and its common equal-bit pair, then transports the enumerator
back to the original gauge.
-/

namespace SixQubit.Orbit9Universal

open SS.MacWilliams

noncomputable section

/-- Every normalized distance-three code on the two complete original orbit-9
fibres has the claimed `A` and `B` enumerators. -/
theorem original_universal_certification (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight SixQubit.Orbit9Real.av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight SixQubit.Orbit9Real.av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c,d] 3) :
    IsE2A ![c,d] ∧ IsE2B ![c,d] := by
  let cu := toUniform c
  let du := toUniform d
  have H : FullKL cu du := {
    support0 := toUniform_support0 c hc
    support1 := toUniform_support1 d hd
    norm0 := by
      rw [innerC_toUniform]
      exact hnc
    norm1 := by
      rw [innerC_toUniform]
      exact hnd
    distance := hasDistance_toUniform c d hdist
  }
  have hnot2 : (ActiveSet cu).card ≠ 2 := active_card_ne_two cu du H
  have hfour : (ActiveSet cu).card = 4 :=
    active_card_eq_four_of_ne_two cu du H hnot2
  rcases equal_pair_of_card_four cu du H hfour with
    ⟨r, s, hrs, hcu, hdu⟩
  exact original_of_uniform_equal_pair c d hnc hnd hdist r s hrs hcu hdu

/-- **The structural clause in the manuscript's orbit-9 theorem.**  In the
uniform gauge there are two distinct physical coordinates whose weight-two
`Z`-pair fixes both logical words.  This is stated with the actual Pauli action,
not merely with the intermediate equal-bits support predicate. -/
theorem uniform_weightTwo_scalar (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight SixQubit.Orbit9Real.av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight SixQubit.Orbit9Real.av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c,d] 3) :
    ∃ r s : Fin 6, r ≠ s ∧
      (let G : SS.PauliString 6 :=
        ⟨fun _ => false, SS.bxor (SS.stdBasis r) (SS.stdBasis s)⟩
       G.wt = 2 ∧
         SS.pauliAct G (toUniform c) = toUniform c ∧
         SS.pauliAct G (toUniform d) = toUniform d) := by
  have H : FullKL (toUniform c) (toUniform d) := {
    support0 := toUniform_support0 c hc
    support1 := toUniform_support1 d hd
    norm0 := by
      rw [innerC_toUniform]
      exact hnc
    norm1 := by
      rw [innerC_toUniform]
      exact hnd
    distance := hasDistance_toUniform c d hdist
  }
  have hnot2 : (ActiveSet (toUniform c)).card ≠ 2 :=
    active_card_ne_two (toUniform c) (toUniform d) H
  have hfour : (ActiveSet (toUniform c)).card = 4 :=
    active_card_eq_four_of_ne_two (toUniform c) (toUniform d) H hnot2
  rcases equal_pair_of_card_four (toUniform c) (toUniform d) H hfour with
    ⟨r, s, hrs, hcu, hdu⟩
  refine ⟨r, s, hrs, ?_⟩
  exact ⟨zpair_wt r s hrs,
    zpair_fixes_of_equalBits (toUniform c) r s hcu,
    zpair_fixes_of_equalBits (toUniform d) r s hdu⟩

/-- One headline exposing both halves of a full orbit certification:
universality for arbitrary full-fibre codes, the manuscript's uniform-gauge
weight-two scalar, and explicit nonempty attainment. -/
theorem fully_kernel_certified :
    (∀ c d : SS.State 6 ℂ,
      (∀ x, SS.weight SixQubit.Orbit9Real.av x ≠ 0 → c x = 0) →
      (∀ x, SS.weight SixQubit.Orbit9Real.av x ≠ 1 → d x = 0) →
      SS.innerC c c = 1 → SS.innerC d d = 1 →
      SS.HasDistance ![c,d] 3 →
      (IsE2A ![c,d] ∧ IsE2B ![c,d]) ∧
      ∃ r s : Fin 6, r ≠ s ∧
        (let G : SS.PauliString 6 :=
          ⟨fun _ => false, SS.bxor (SS.stdBasis r) (SS.stdBasis s)⟩
         G.wt = 2 ∧
           SS.pauliAct G (toUniform c) = toUniform c ∧
           SS.pauliAct G (toUniform d) = toUniform d)) ∧
    (∃ c d : SS.State 6 ℂ,
      (∀ x, SS.weight SixQubit.Orbit9Real.av x ≠ 0 → c x = 0) ∧
      (∀ x, SS.weight SixQubit.Orbit9Real.av x ≠ 1 → d x = 0) ∧
      SS.innerC c c = 1 ∧ SS.innerC d d = 1 ∧
      SS.HasDistance ![c,d] 3 ∧
      IsE2A ![c,d] ∧ IsE2B ![c,d]) := by
  constructor
  · intro c d hc hd hnc hnd hdist
    exact ⟨original_universal_certification c d hc hd hnc hnd hdist,
      uniform_weightTwo_scalar c d hc hd hnc hnd hdist⟩
  · exact SixQubit.Orbit9Attain.fully_certified_attainment

end


end SixQubit.Orbit9Universal
