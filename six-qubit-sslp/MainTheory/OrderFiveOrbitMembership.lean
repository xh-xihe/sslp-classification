import MainTheory.OrderFiveCodeRigidity

/-!
# Orbit membership for the order-five codes

`thm:unique-C5-LU` has two clauses.  The second -- every exact `((6,2,3))`
code carrying a projective diagonal logical element of order five has a
projector local-unitarily equivalent to the canonical one -- is
`OrderFiveCodeRigidity.luEquivalent_canonical_of_orderFive`.

The first clause is the *orbit* statement: such a code belongs to SSLP orbit
`36`.  That is strictly more than local-unitary equivalence.  `LUEquivalent`
(`ClassificationLevels.lean`) is the equivalence closure of arbitrary
one-qubit unitaries and qubit permutations; it says nothing about the code's
support fibres, whereas an SSLP orbit is by definition an orbit of a labelled
Boolean fibre pair under `CubeAction.Parameter 6`
(`CubeAction.FiberEquivalent F G` is literally `exists g, actFibers g F = G`).
So the rigidity theorem does not imply the membership clause, and no
declaration stated it.

Everything needed was nonetheless already proved.
`IntrinsicOrderAudit.exists_key_of_element` runs the classification pipeline
from a *group element*, and returns -- besides the key -- both

* `S.m = orderOf u`, unconditionally rather than for a normal form the theorem
  happens to produce, and
* the cube-action equivalence `FiberEquivalent (fibersOfPair (recordFiberPair
  (recordOf S))) (keyAt k).fibers`.

`OrderFiveUniqueCompletion.eq_key34_of_orderFive_completion` then pins the key
to `34`, whose paper id is `36`.  `luEquivalent_canonical_of_orderFive`
obtains exactly these facts inside its own proof and discards the fibre
equivalence; this file keeps it.

What "belongs to orbit 36" means here, stated exactly: the support fibre pair
of the code's sorted normal form is carried onto the fibre pair of table key
`34` by a single element of the cube group, and `paperOrbitId 34 = 36`.  The
normal form is tied to `C` by its own `source_span` and `frame_eq` fields -- a
local `X` string and a qubit permutation -- so this is a statement about `C`.
-/

namespace MainTheory.OrderFiveOrbitMembership

open MainTheory
open MainTheory.ClassificationLevels
open MainTheory.GlobalClassificationBridge
open MainTheory.SortedForm
open MainTheory.OuterCompleteness
open MainTheory.CodeFiberBridge
open MainTheory.FiniteOrbitPipeline
open MainTheory.CubeCompletionTransport
open MainTheory.CubeAction

/-- An element of order five forces the whole intrinsic group to have order
five: its order divides the group's, and `IntrinsicOrderAudit.natCard_mem`
leaves only `5`. -/
theorem natCard_eq_five_of_orderFive (C : CodeSpec.ExactCode 6 2 3)
    (g : IntrinsicGroup C) (hg : orderOf g = 5) :
    Nat.card (IntrinsicGroup C) = 5 := by
  have hdvd : (5 : ℕ) ∣ Nat.card (IntrinsicGroup C) := hg ▸ orderOf_dvd_natCard g
  rcases MainTheory.IntrinsicOrderAudit.natCard_mem C with h | h | h | h <;>
    rw [h] at hdvd ⊢ <;> omega

/-- **`thm:unique-C5-LU`, clause one, with the key exhibited.**

An exact `((6,2,3))` code with a projective diagonal logical element of order
five has a sorted normal form whose fibre pair is cube-equivalent to that of
table key `34`, and key `34` is paper orbit `36`. -/
theorem orbit36_of_orderFive (C : CodeSpec.ExactCode 6 2 3)
    (g : IntrinsicGroup C) (hg : orderOf g = 5) :
    ∃ (S : SortedNormalForm C) (k : Fin 66),
      k = 34 ∧
      MainTheory.Generated.FiniteOrbitBase.paperOrbitId k = 36 ∧
      S.m = 5 ∧
      (MainTheory.Generated.FiniteOrbitBase.keyAt k).m = 5 ∧
      FiberEquivalent (fibersOfPair (recordFiberPair (recordOf S)))
        (MainTheory.Generated.FiniteOrbitBase.keyAt k).fibers := by
  have hg1 : g ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hg
    omega
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨S, k, _, hm, hSm, hc, hfe⟩ :=
    MainTheory.IntrinsicOrderAudit.exists_key_of_element C u hg1
  have hm5 : (MainTheory.Generated.FiniteOrbitBase.keyAt k).m = 5 := by
    rw [hm]; exact hg
  have hk34 : k = 34 :=
    MainTheory.OrderFiveUniqueCompletion.eq_key34_of_orderFive_completion k hm5 hc
  refine ⟨S, k, hk34, ?_, hSm.trans hg, hm5, hfe⟩
  exact MainTheory.OrderFiveUniqueCompletion.paperOrbitId_eq_36_of_orderFive_completion
    k hm5 hc

/-- The membership clause in its most literal form: a single cube-group
parameter carries the code's normal-form fibre pair onto the orbit-36 key. -/
theorem exists_cubeParameter_orbit36 (C : CodeSpec.ExactCode 6 2 3)
    (g : IntrinsicGroup C) (hg : orderOf g = 5) :
    ∃ (S : SortedNormalForm C) (gamma : Parameter 6),
      actFibers gamma (fibersOfPair (recordFiberPair (recordOf S)))
          = (MainTheory.Generated.FiniteOrbitBase.keyAt 34).fibers ∧
        MainTheory.Generated.FiniteOrbitBase.paperOrbitId 34 = 36 := by
  obtain ⟨S, k, hk, hid, _, _, hfe⟩ := orbit36_of_orderFive C g hg
  subst hk
  obtain ⟨gamma, hgamma⟩ := hfe
  exact ⟨S, gamma, hgamma, hid⟩

/-- **`thm:unique-C5-LU`.**

Both clauses at once: an exact `((6,2,3))` code carrying a projective
diagonal logical element of order five belongs to SSLP orbit `36`, and its
projector is local-unitarily equivalent to the canonical orbit-36 projector.
The intrinsic group is then cyclic of order exactly five. -/
theorem unique_C5_LU (C : CodeSpec.ExactCode 6 2 3)
    (g : IntrinsicGroup C) (hg : orderOf g = 5) :
    Nat.card (IntrinsicGroup C) = 5 ∧
      (∃ (S : SortedNormalForm C) (gamma : Parameter 6),
        actFibers gamma (fibersOfPair (recordFiberPair (recordOf S)))
          = (MainTheory.Generated.FiniteOrbitBase.keyAt 34).fibers ∧
        MainTheory.Generated.FiniteOrbitBase.paperOrbitId 34 = 36) ∧
      LUEquivalent (CodeProjector.ofFrame C.frame)
        (CodeProjector.ofFrame MainTheory.Orbit36LUBridge.canonicalFrame) :=
  ⟨natCard_eq_five_of_orderFive C g hg,
    exists_cubeParameter_orbit36 C g hg,
    MainTheory.OrderFiveCodeRigidity.luEquivalent_canonical_of_orderFive C g hg⟩

/-- The same, entered from the group's order rather than from an element. -/
theorem unique_C5_LU_of_natCard (C : CodeSpec.ExactCode 6 2 3)
    (h : Nat.card (IntrinsicGroup C) = 5) :
    (∃ (S : SortedNormalForm C) (gamma : Parameter 6),
        actFibers gamma (fibersOfPair (recordFiberPair (recordOf S)))
          = (MainTheory.Generated.FiniteOrbitBase.keyAt 34).fibers ∧
        MainTheory.Generated.FiniteOrbitBase.paperOrbitId 34 = 36) ∧
      LUEquivalent (CodeProjector.ofFrame C.frame)
        (CodeProjector.ofFrame MainTheory.Orbit36LUBridge.canonicalFrame) := by
  obtain ⟨g, _, hcard⟩ := MainTheory.GroupOrder.exists_generator_orderOf_eq_natCard C
  have hg : orderOf g = 5 := by rw [hcard, h]
  exact ⟨exists_cubeParameter_orbit36 C g hg,
    MainTheory.OrderFiveCodeRigidity.luEquivalent_canonical_of_orderFive C g hg⟩

end MainTheory.OrderFiveOrbitMembership
