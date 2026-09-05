import MainTheory.CodeOrbitStatus
import MainTheory.GroupOrder

/-!
# The group audit, entered from a group element

`thm:sslp-completeness` asks for an audit of the intrinsic projective diagonal
group.  What this development had was two statements that never met.
`SSLPCompleteness.orderOf_le_nine` bounds the order of an actual group element
by nine.  `CodeOrbitStatus.code_logicalOrder_mem` gives membership in
`{2, 3, 5}`, but for the `m` of a normal form the theorem itself produced, with
no link back to the element one started from -- so it could not be applied to a
given symmetry.

The link is now available: `SortedPivotConstruction.exists_sortedNormalForm_pivot`
carries the identification of `S.m` with the order of whichever diagonal
symmetry the entrance was built from, and `CodeOrbitKey` and
`CodeOrbitStatus.exists_key_transport` pass it on.  This file spends it.

* `exists_key_of_element` -- run the whole pipeline starting from a *group
  element* rather than from a chosen real phase vector, and get back a key
  whose `m` is that element's order.
* `orderOf_mem` -- every element of the intrinsic group of an exact `((6,2,3))`
  code has order `1`, `2`, `3` or `5`.  This is
  `GlobalClassificationBridge.SixQubitIntrinsicInputs.orderAudit` proved
  outright; that structure is declared in the repository and never
  constructed, so the two theorems gated behind it were sound and unusable.
* `natCard_mem` -- and the group itself has order `1`, `2`, `3` or `5`.

What this is **not**: the other half of `thm:sslp-completeness`, that the
equivalence quotient returns the selected data.  The sixty-six keys are orbits
of labelled Boolean *support* pairs under `CubeAction.Parameter 6`, and a
single key carries a whole family of amplitude tuples, so "same key" is
strictly weaker than "equivalent code" until a rigidity theorem collapses that
family.  Exactly one orbit has one.
-/

namespace MainTheory.IntrinsicOrderAudit

open MainTheory
open MainTheory.ClassificationLevels
open MainTheory.GlobalClassificationBridge
open MainTheory.SortedForm
open MainTheory.OuterCompleteness
open MainTheory.CodeFiberBridge
open MainTheory.FiniteOrbitPipeline
open MainTheory.CubeCompletionTransport

/-- **The orbit key of a code, entered from one of its diagonal symmetries.**

Same pipeline as `CodeOrbitStatus.exists_key_transport`, but the phase vector
is manufactured from the element instead of being supplied, so the key's `m` is
the order of *that* element rather than of some normal form's. -/
theorem exists_key_of_element (C : CodeSpec.ExactCode 6 2 3)
    (u : diagonalSymmetryGroup (exactCodeProjector C))
    (hu : intrinsicClass (exactCodeProjector C) u ≠ 1) :
    ∃ (S : SortedNormalForm C) (k : Fin 66),
      (MainTheory.Generated.FiniteOrbitBase.keyAt k).q = S.q ∧
      (MainTheory.Generated.FiniteOrbitBase.keyAt k).m
        = orderOf (intrinsicClass (exactCodeProjector C) u) ∧
      S.m = orderOf (intrinsicClass (exactCodeProjector C) u) ∧
      HasCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt k).fibers ∧
      MainTheory.CubeAction.FiberEquivalent
        (fibersOfPair (recordFiberPair (recordOf S)))
        (MainTheory.Generated.FiniteOrbitBase.keyAt k).fibers := by
  obtain ⟨theta, hexp⟩ :=
    MainTheory.LocalPhaseAngle.exists_angleVector (u : LocalPhase 6)
  have hpres := MainTheory.SymmetryToEntrance.codePreserving_of_symmetry C.frame
    (u : LocalPhase 6) u.2 theta hexp
  have hnt := MainTheory.SymmetryToEntrance.projectivelyNontrivialReal_of_class_ne_one
    C (u : LocalPhase 6) u.2 theta hexp hu
  obtain ⟨S, k, hq, hm, hfe, hord⟩ :=
    MainTheory.CodeOrbitStatus.exists_key_transport C theta hpres hnt
  have hSm : S.m = orderOf (intrinsicClass (exactCodeProjector C) u) := hord u hexp
  exact ⟨S, k, hq, hm.trans hSm, hSm,
    completion_of_fiberEquivalent
      (MainTheory.CodeOrbitStatus.hasCompletion_codePair S) hfe, hfe⟩

/-- **The order audit.**

Every element of the intrinsic projective diagonal logical group of an exact
`((6,2,3))` code has order one, two, three or five.

`SSLPCompleteness.orderOf_le_nine` gives only `<= 9`, and
`CodeOrbitStatus.code_logicalOrder_mem` gives `{2, 3, 5}` for a normal form's
own `m`; neither could be applied to a given element. -/
theorem orderOf_mem (C : CodeSpec.ExactCode 6 2 3) (g : IntrinsicGroup C) :
    orderOf g = 1 ∨ orderOf g = 2 ∨ orderOf g = 3 ∨ orderOf g = 5 := by
  by_cases hg : g = 1
  · subst hg
    simp
  · obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective g
    show orderOf (intrinsicClass (exactCodeProjector C) u) = 1 ∨
      orderOf (intrinsicClass (exactCodeProjector C) u) = 2 ∨
      orderOf (intrinsicClass (exactCodeProjector C) u) = 3 ∨
      orderOf (intrinsicClass (exactCodeProjector C) u) = 5
    obtain ⟨S, k, _, hm, _, hc, _⟩ := exists_key_of_element C u hg
    rcases MainTheory.OrderRange.logicalOrder_mem k hc with h | h | h
    · exact Or.inr (Or.inl (by rw [← hm, h]))
    · exact Or.inr (Or.inr (Or.inl (by rw [← hm, h])))
    · exact Or.inr (Or.inr (Or.inr (by rw [← hm, h])))

/-- The same, bounded: no element has order above five. -/
theorem orderOf_le_five (C : CodeSpec.ExactCode 6 2 3) (g : IntrinsicGroup C) :
    orderOf g ≤ 5 := by
  rcases orderOf_mem C g with h | h | h | h <;> omega

/-- **The group audit.**

The intrinsic projective diagonal logical group of an exact `((6,2,3))` code
has order one, two, three or five.  It is cyclic, so its order is the order of
a generator, and `orderOf_mem` audits that. -/
theorem natCard_mem (C : CodeSpec.ExactCode 6 2 3) :
    Nat.card (IntrinsicGroup C) = 1 ∨ Nat.card (IntrinsicGroup C) = 2 ∨
      Nat.card (IntrinsicGroup C) = 3 ∨ Nat.card (IntrinsicGroup C) = 5 := by
  obtain ⟨g, _, hcard⟩ := MainTheory.GroupOrder.exists_generator_orderOf_eq_natCard C
  rw [← hcard]
  exact orderOf_mem C g

theorem natCard_le_five (C : CodeSpec.ExactCode 6 2 3) :
    Nat.card (IntrinsicGroup C) ≤ 5 := by
  rcases natCard_mem C with h | h | h | h <;> omega

end MainTheory.IntrinsicOrderAudit
