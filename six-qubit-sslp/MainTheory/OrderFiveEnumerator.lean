import MainTheory.OrderFiveOrbitMembership
import MainTheory.WImageOrbit36
import MainTheory.LocalUnitaryEnumerators

/-!
# `cor:m5-unique-unconditional`: the enumerator clause

The corollary has three clauses.  Orbit 36 is the only rank-compatible moment
orbit admitting an order-five code, every such code has the Shor--Laflamme
enumerator

  `A = (1, 0, 21/25, 0, 291/25, 384/25, 79/25)`,

and it belongs, up to the lift-aware normal form, to the rigid orbit-36 class.

`MainTheory.OrderFiveOrbitMembership.unique_C5_LU` carries the first and third.
The middle one -- the enumerator value for an *arbitrary* order-five code, not
just for a pair on the table fibres -- had no declaration: `WImage_orbit36`
proves the value on the table fibres, and nothing transported it to the code.

The transport is local-unitary invariance of the enumerator,
`LocalUnitaryEnumerators.Aco_luEquivalent`, which was already proved and never
used for this.  Both an arbitrary order-five code and the attainment witness
on the table fibres are LU-equivalent to the canonical orbit-36 projector, so
their enumerators agree with each other.
-/

namespace MainTheory.OrderFiveEnumerator

open MainTheory
open MainTheory.ClassificationLevels
open MainTheory.GlobalClassificationBridge

noncomputable section

/-- The attainment witness on the orbit-36 table fibres, with its enumerator.
It exists because `WImage_orbit36` is a singleton, not the empty set. -/
theorem exists_table_witness :
    ∃ c d : SS.State 6 ℂ,
      (∀ x, x ∉ SixQubit.Orbit36Transport.originalS0 → c x = 0) ∧
      (∀ y, y ∉ SixQubit.Orbit36Transport.originalS1 → d y = 0) ∧
      SS.innerC c c = 1 ∧ SS.innerC d d = 1 ∧
      SS.HasDistance ![c, d] 3 ∧
      ∀ j, MainTheory.WImages.R5A j = SS.MacWilliams.Aco ![c, d] j / 4 := by
  have hR : MainTheory.WImages.R5A ∈
      MainTheory.Levels.WImage SixQubit.Orbit36Transport.originalAv 0 1 := by
    rw [MainTheory.WImages.WImage_orbit36]
    simp
  obtain ⟨c, d, hc, hd, hnc, hnd, hdist, hA⟩ := hR
  refine ⟨c, d, ?_, ?_, hnc, hnd, hdist, hA⟩
  · intro x hx
    apply hc x
    simpa [SixQubit.Orbit36Transport.originalS0] using hx
  · intro y hy
    apply hd y
    simpa [SixQubit.Orbit36Transport.originalS1] using hy

/-- The canonical orbit-36 projector carries the manuscript's enumerator. -/
theorem canonical_enumerator (j : Fin 7) :
    SS.MacWilliams.Aco MainTheory.Orbit36LUBridge.canonicalFrame.vec j / 4
      = MainTheory.WImages.R5A j := by
  obtain ⟨c, d, hc, hd, hnc, hnd, hdist, hA⟩ := exists_table_witness
  have hlu := MainTheory.Orbit36LUBridge.original_projector_luEquivalent_canonical
    c d hc hd hnc hnd hdist
  have heq := MainTheory.LocalUnitaryEnumerators.Aco_luEquivalent
    (MainTheory.Orbit36LUBridge.originalFrame c d hc hd hnc hnd)
    MainTheory.Orbit36LUBridge.canonicalFrame hlu (j : ℕ)
  rw [heq]
  exact (hA j).symm

/-- **`cor:m5-unique-unconditional`, the enumerator clause.**

Every exact `((6,2,3))` code with a projective diagonal logical element of
order five has the orbit-36 Shor--Laflamme enumerator. -/
theorem orderFive_enumerator (C : CodeSpec.ExactCode 6 2 3)
    (g : IntrinsicGroup C) (hg : orderOf g = 5) (j : Fin 7) :
    SS.MacWilliams.Aco C.frame.vec j / 4 = MainTheory.WImages.R5A j := by
  have hlu := MainTheory.OrderFiveCodeRigidity.luEquivalent_canonical_of_orderFive C g hg
  have heq := MainTheory.LocalUnitaryEnumerators.Aco_luEquivalent
    C.frame MainTheory.Orbit36LUBridge.canonicalFrame hlu (j : ℕ)
  rw [← heq]
  exact canonical_enumerator j

/-- **`cor:m5-unique-unconditional`**, all three clauses.

Orbit 36 is the only moment orbit carrying an order-five code -- exhibited as
a single cube-group element sending the code's normal-form fibre pair onto
table key `34`, whose paper orbit id is `36`; every such code has the
manuscript's enumerator; and its projector is local-unitarily equivalent to
the canonical orbit-36 projector. -/
theorem m5_unique_unconditional_full (C : CodeSpec.ExactCode 6 2 3)
    (g : IntrinsicGroup C) (hg : orderOf g = 5) :
    (∃ (S : SortedForm.SortedNormalForm C) (gamma : MainTheory.CubeAction.Parameter 6),
        MainTheory.CubeAction.actFibers gamma
            (MainTheory.FiniteOrbitPipeline.fibersOfPair
              (MainTheory.OuterCompleteness.recordFiberPair
                (MainTheory.CodeFiberBridge.recordOf S)))
          = (MainTheory.Generated.FiniteOrbitBase.keyAt 34).fibers ∧
        MainTheory.Generated.FiniteOrbitBase.paperOrbitId 34 = 36) ∧
      (∀ j : Fin 7,
        SS.MacWilliams.Aco C.frame.vec j / 4 = MainTheory.WImages.R5A j) ∧
      LUEquivalent (CodeProjector.ofFrame C.frame)
        (CodeProjector.ofFrame MainTheory.Orbit36LUBridge.canonicalFrame) :=
  ⟨MainTheory.OrderFiveOrbitMembership.exists_cubeParameter_orbit36 C g hg,
    fun j => orderFive_enumerator C g hg j,
    MainTheory.OrderFiveCodeRigidity.luEquivalent_canonical_of_orderFive C g hg⟩

end

end MainTheory.OrderFiveEnumerator
