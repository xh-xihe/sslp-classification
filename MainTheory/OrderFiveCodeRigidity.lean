import MainTheory.IntrinsicOrderAudit
import MainTheory.NormalFormLUBridge
import MainTheory.Orbit36LUBridge
import MainTheory.OrderFivePaperIdentification

/-!
# `thm:unique-C5-LU` for an arbitrary order-five code

`ClassificationLevelsSix.level_four_lu_class` proves the rigidity half of
`thm:unique-C5-LU` only for codes whose two logical words are already supported
on orbit 36's two *table* fibres, and its own header said what was missing:
carrying it to an arbitrary exact `((6,2,3))` code with a projective order-five
element needs a state-level transport from that code's fibres to the table's,
which `CodeOrbitStatus.code_orderFive_is_orbit36` supplies only at the level of
directory keys.

Every link of that transport now exists, and this file composes them.

* `IntrinsicOrderAudit.exists_key_of_element` places the code on a key whose
  `m` is the order of the element one started from -- so `m = 5` is a
  hypothesis about the code, not about a normal form the theorem chose.
* `OrderFiveUniqueCompletion.eq_key34_of_orderFive_completion` pins the key to
  `34`, and `OrderFivePaperIdentification.paper36_equivalent_directoryKey34` is
  a *proved* cube action between that key's fibres and the table's.
* `CubeCompletionTransport.pushCompletion` moves the code's own states along
  the composite action, and `CodeOrbitStatus.completion_codePair` keeps them
  tied to the normal form rather than erasing them behind `Nonempty`.
* `CubeCompletionTransport.equivalent_pushPair` says that move is a code
  equivalence, and `NormalFormLUBridge.luEquivalent_ofFrame_normalForm` carries
  the normal form back to the code's own projector.

The hypothesis shape matters and is the reason this is not stated as
`∃ S, S.m = 5 → …`.  Such a conclusion does not mention the bound `S`, so it
is satisfied by any normal form with `m ≠ 5` and says nothing about the code.
Here the order-five condition is imposed on an actual element of
`IntrinsicGroup C`.
-/

namespace MainTheory.OrderFiveCodeRigidity

open MainTheory
open MainTheory.ClassificationLevels
open MainTheory.GlobalClassificationBridge
open MainTheory.SortedForm
open MainTheory.OuterCompleteness
open MainTheory.CodeFiberBridge
open MainTheory.FiniteOrbitPipeline
open MainTheory.CubeCompletionTransport
open MainTheory.CubeAction

noncomputable section

/-- **Every exact `((6,2,3))` code with a projective diagonal logical element
of order five has a projector local-unitarily equivalent to the canonical
orbit-36 projector.**

This is `thm:unique-C5-LU` at the level the paper states it. -/
theorem luEquivalent_canonical_of_orderFive (C : CodeSpec.ExactCode 6 2 3)
    (g : IntrinsicGroup C) (hg : orderOf g = 5) :
    LUEquivalent (CodeProjector.ofFrame C.frame)
      (CodeProjector.ofFrame MainTheory.Orbit36LUBridge.canonicalFrame) := by
  have hg1 : g ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hg
    omega
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨S, k, _, hm, _, hc, hfe⟩ :=
    MainTheory.IntrinsicOrderAudit.exists_key_of_element C u hg1
  have hm5 : (MainTheory.Generated.FiniteOrbitBase.keyAt k).m = 5 := by
    rw [hm]; exact hg
  have hk34 : k = 34 :=
    MainTheory.OrderFiveUniqueCompletion.eq_key34_of_orderFive_completion k hm5 hc
  subst hk34
  -- the composite cube action, from the code's own fibres to the table's
  obtain ⟨gg, hgg⟩ : FiberEquivalent (fibersOfPair (recordFiberPair (recordOf S)))
      MainTheory.OrderFivePaperIdentification.paper36Fibers :=
    fiberEquivalent_trans hfe (fiberEquivalent_symm
      MainTheory.OrderFivePaperIdentification.paper36_equivalent_directoryKey34.2.2)
  -- push the code's own states along it
  set W := pushCompletion (MainTheory.CodeOrbitStatus.completion_codePair S) gg
    with hWdef
  have hstates : (MainTheory.CodeOrbitStatus.completion_codePair S).states
      = S.frame.vec := by
    funext j
    fin_cases j <;> rfl
  have hWpush : W.states = pushPair gg S.frame.vec := by
    rw [hWdef]
    show pushPair gg (MainTheory.CodeOrbitStatus.completion_codePair S).states = _
    rw [hstates]
  -- the pushed states live on the table fibres
  have hsupp : ∀ j : Fin 2, ∀ x,
      x ∉ MainTheory.OrderFivePaperIdentification.paper36Fibers (finColor j) →
        W.states j x = 0 := by
    intro j x hx
    refine W.supported j x ?_
    rwa [hgg]
  have hc0 : ∀ x, x ∉ SixQubit.Orbit36Transport.originalS0 → W.states 0 x = 0 :=
    fun x hx => hsupp 0 x (by simpa [MainTheory.OrderFivePaperIdentification.paper36Fibers]
      using hx)
  have hd1 : ∀ y, y ∉ SixQubit.Orbit36Transport.originalS1 → W.states 1 y = 0 :=
    fun y hy => hsupp 1 y (by simpa [MainTheory.OrderFivePaperIdentification.paper36Fibers]
      using hy)
  have hnc : SS.innerC (W.states 0) (W.states 0) = 1 := W.normalized 0
  have hnd : SS.innerC (W.states 1) (W.states 1) = 1 := W.normalized 1
  have hvec : ![W.states 0, W.states 1] = W.states := by
    funext j
    fin_cases j <;> rfl
  have hdist : SS.HasDistance ![W.states 0, W.states 1] 3 := by
    rw [hvec]
    exact W.hasDistance
  -- the frame carried by the pushed states
  set F36 := MainTheory.Orbit36LUBridge.originalFrame (W.states 0) (W.states 1)
    hc0 hd1 hnc hnd with hF36
  have hF36vec : F36.vec = W.states := by
    rw [hF36]
    exact hvec
  -- assemble the three local-unitary moves
  have h1 : LUEquivalent (CodeProjector.ofFrame C.frame)
      (CodeProjector.ofFrame S.frame) :=
    MainTheory.NormalFormLUBridge.luEquivalent_ofFrame_normalForm S
  have h2 : LUEquivalent (CodeProjector.ofFrame S.frame)
      (CodeProjector.ofFrame F36) := by
    refine MainTheory.LocalMonomialSixBridge.luEquivalent_of_codeEquivalent _ _ ?_
    rw [hF36vec, hWpush]
    exact equivalent_pushPair gg S.frame.vec
  have h3 : LUEquivalent (CodeProjector.ofFrame F36)
      (CodeProjector.ofFrame MainTheory.Orbit36LUBridge.canonicalFrame) :=
    MainTheory.Orbit36LUBridge.original_projector_luEquivalent_canonical
      (W.states 0) (W.states 1) hc0 hd1 hnc hnd hdist
  exact luEquivalent_equivalence.trans h1
    (luEquivalent_equivalence.trans h2 h3)

/-- **Uniqueness of the order-five local-unitary class.**

Any two exact `((6,2,3))` codes carrying a projective diagonal logical element
of order five have local-unitarily equivalent projectors -- the other half of
`thm:unique-C5-LU`. -/
theorem luEquivalent_of_orderFive (C C' : CodeSpec.ExactCode 6 2 3)
    (g : IntrinsicGroup C) (hg : orderOf g = 5)
    (g' : IntrinsicGroup C') (hg' : orderOf g' = 5) :
    LUEquivalent (CodeProjector.ofFrame C.frame)
      (CodeProjector.ofFrame C'.frame) :=
  luEquivalent_equivalence.trans
    (luEquivalent_canonical_of_orderFive C g hg)
    (luEquivalent_equivalence.symm
      (luEquivalent_canonical_of_orderFive C' g' hg'))

end

end MainTheory.OrderFiveCodeRigidity
