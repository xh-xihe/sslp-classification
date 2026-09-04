import MainTheory.CodeOrbitStatus
import MainTheory.SSLPOrbitLevels
import MainTheory.ProvedWEUnion
import MainTheory.Orbit36LUBridge
import MainTheory.RankTwoSSLP

/-!
# The four classification levels, at six qubits

`ClassificationLevels` defines the four objects `def:six-classification-levels`
distinguishes, and its header still cites the 20260822 draft.  Three of the
four named objects there have no users; they are definitions in search of a
theorem, and a reader checking the paper's definition against this development
finds the vocabulary but not the content.

This file supplies the content: one theorem per level, each about six-qubit
codes, each discharged by results the development already has.  Nothing new is
proved -- the point is that after this file every level of
`def:six-classification-levels` has a statement attached to it, so the named
object is load-bearing rather than decorative.

The levels the paper distinguishes, and what is said about each here:

* **(i) intrinsic logical-group level** -- the group is finite and cyclic, and
  a nontrivial one has order `2`, `3` or `5`;
* **(ii) SSLP realization-orbit level** -- exactly fifteen orbits;
* **(iii) weight-enumerator level** -- the eleven exact images and their union;
* **(iv) local-unitary code level** -- the orbit-36 sector is a single class.

Level (iv) is stated where the rigidity theorem states it, on codes supported
in orbit 36's two table fibres.  Carrying it to an *arbitrary* order-five code
needs the state-level transport from that code's fibres to the table's, which
`CodeOrbitStatus.code_orderFive_is_orbit36` supplies only at the level of
directory keys; that step is not in this development.
-/

namespace MainTheory.ClassificationLevelsSix

open MainTheory
open MainTheory.ClassificationLevels
open MainTheory.SortedForm

/-! ## Level (i): the intrinsic logical group -/

/-- **Level (i) at six qubits.**

The intrinsic projective diagonal logical group of an exact `((6,2,3))` code
carrying a projectively nontrivial diagonal symmetry is finite and cyclic, and
the order of the symmetry is `2`, `3` or `5`.

The first two conjuncts are `RankTwoSSLP.rank_two_sslp`; the third is
`six:thm:global-status` read at the level of codes. -/
theorem level_one_intrinsic_group (C : CodeSpec.ExactCode 6 2 3)
    (theta : Fin 6 → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id) :
    IsCyclic (IntrinsicProjectiveDiagonalLogicalGroup
        (CodeProjector.ofFrame C.frame)) ∧
      Finite (GlobalClassificationBridge.IntrinsicGroup C) ∧
      ∃ S : SortedNormalForm C, S.m = 2 ∨ S.m = 3 ∨ S.m = 5 := by
  obtain ⟨hcyc, hfin, _⟩ :=
    MainTheory.RankTwoSSLP.rank_two_sslp C theta hpres hnt
  exact ⟨hcyc, hfin,
    MainTheory.CodeOrbitStatus.code_logicalOrder_mem C theta hpres hnt⟩

/-! ## Level (ii): the realization orbits -/

/-- **Level (ii) at six qubits**: the realization-orbit level has exactly
fifteen members, and every moment orbit either belongs to it or has empty
`K_r`. -/
theorem level_two_realization_orbits :
    Nat.card MainTheory.SSLPOrbitLevels.RealizationOrbit = 15 ∧
      ∀ r : MainTheory.SSLPOrbitLevels.MomentOrbit,
        MainTheory.SSLPOrbitLevels.IsRealizationOrbit r ∨
          IsEmpty (MainTheory.SSLPOrbitLevels.KSet r) :=
  ⟨MainTheory.SSLPOrbitLevels.card_realizationOrbit,
    MainTheory.SSLPOrbitLevels.realization_or_empty⟩

/-! ## Level (iii): the weight-enumerator images -/

/-- **Level (iii) at six qubits**: the union of the eleven exact images is the
`L`-interval, the upper `M`-segment and the isolated point. -/
theorem level_three_weight_enumerators :
    MainTheory.ProvedWEUnion.provedImages =
      MainTheory.WImages.FI '' Set.Icc (0 : ℝ) 1 ∪
        MainTheory.WImages.FII '' Set.Icc (2 / 3 : ℝ) 1 ∪
        {MainTheory.WImages.R5A} :=
  MainTheory.ProvedWEUnion.provedImages_eq

/-! ## Level (iv): the local-unitary code classes -/

/-- **Level (iv) at six qubits**: any two exact distance-three codes supported
on orbit 36's two table fibres have local-unitarily equivalent projectors.

This is the rigidity half of `thm:unique-C5-LU` in the shape
`eq:LU-equivalence` asks for: an identification of *projectors*, not of
amplitude tuples. -/
theorem level_four_lu_class
    (c d c' d' : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit36Transport.originalS0 → c x = 0)
    (hd : ∀ y, y ∉ SixQubit.Orbit36Transport.originalS1 → d y = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3)
    (hc' : ∀ x, x ∉ SixQubit.Orbit36Transport.originalS0 → c' x = 0)
    (hd' : ∀ y, y ∉ SixQubit.Orbit36Transport.originalS1 → d' y = 0)
    (hnc' : SS.innerC c' c' = 1) (hnd' : SS.innerC d' d' = 1)
    (hdist' : SS.HasDistance ![c', d'] 3) :
    LUEquivalent
      (CodeProjector.ofFrame
        (MainTheory.Orbit36LUBridge.originalFrame c d hc hd hnc hnd))
      (CodeProjector.ofFrame
        (MainTheory.Orbit36LUBridge.originalFrame c' d' hc' hd' hnc' hnd')) :=
  luEquivalent_equivalence.trans
    (MainTheory.Orbit36LUBridge.original_projector_luEquivalent_canonical
      c d hc hd hnc hnd hdist)
    (luEquivalent_equivalence.symm
      (MainTheory.Orbit36LUBridge.original_projector_luEquivalent_canonical
        c' d' hc' hd' hnc' hnd' hdist'))

end MainTheory.ClassificationLevelsSix
