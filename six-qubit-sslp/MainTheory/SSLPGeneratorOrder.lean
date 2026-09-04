import MainTheory.GroupOrder
import MainTheory.BoundedGeneratorOrder

/-!
# `thm:d3-sslp-classification` for a *generator*

`D3BoundedNormalForm.exists_sortedNormalForm_le_betaN` proves the modulus half
of `thm:d3-sslp-classification`: the sorted two-fibre normal form can be taken
with `q <= beta_n`.  What it does not prove is the corollary's own reading of
`m`.  The paper says "the projective diagonal logical group is nontrivial ...
then *a generator* has a primitive physical representative `D(a;q)` with
`m | q`", and there `m` is the order of the whole cyclic group.  The existing
theorem runs on an arbitrary projectively nontrivial real phase vector, so its
`S.m` is only the order of *some* element -- a divisor of the group order, not
the group order.

Closing the gap needs three facts that were separately available and never
composed:

* `GroupOrder.exists_generator_orderOf_eq_natCard` -- the group is finite and
  cyclic at `d = 3`, so a generator exists;
* `GroupOrder.logicalOrder_eq_natCard_of_generator` -- if the chosen symmetry
  generates, its `logicalOrder` *is* `Nat.card`;
* `BoundedGeneratorOrder.logicalOrder_boundedGenerator` -- the `beta_n` route
  does not move that order.

The last one matters because the bound and the order are produced by two
different generators: the bound comes from the sparse `boundedGenerator`, the
order from the original one.  Without it the two halves of `eq:d3-sslp-bound`
could not be asserted of the same normal form.
-/

namespace MainTheory.SSLPGeneratorOrder

open MainTheory
open MainTheory.ClassificationLevels
open MainTheory.GlobalClassificationBridge
open MainTheory.SectionTwoGeneral
open MainTheory.D3NormalizedFreshPhase
open MainTheory.D3AutomaticBoundedGenerator
open MainTheory.D3BoundedNormalForm
open SixQubit.CodeEquiv

variable {n : ℕ}

/-- **The sorted normal form of a generator, with the `beta_n` bound.**

The record's `m` is the order of the entire projective diagonal logical group,
which is what `thm:d3-sslp-classification` means by `C_m`; its `q` still meets
the distance-three cutoff. -/
theorem exists_sortedNormalForm_le_betaN_order {B : ℕ}
    (beta : BinaryBeta.BetaBound n B)
    (C : CodeSpec.ExactCode n 2 3)
    (hnontrivial : ∃ g : IntrinsicGroup C, g ≠ 1) :
    ∃ S : SortedForm.SortedNormalForm C,
      S.q ≤ B ∧ S.m = Nat.card (IntrinsicGroup C) := by
  haveI := GeneralFiniteness.finite_intrinsicGroup C
  haveI := GeneralFiniteness.isCyclic C
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := IntrinsicGroup C)
  have hg1 : g ≠ 1 := by
    rintro rfl
    obtain ⟨x, hx⟩ := hnontrivial
    exact hx (by simpa using hg x)
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨theta, hexp⟩ :=
    MainTheory.LocalPhaseAngle.exists_angleVector (u : LocalPhase n)
  have hpres := SymmetryToEntrance.codePreserving_of_symmetry C.frame
    (u : LocalPhase n) u.2 theta hexp
  have hnt := SymmetryToEntrance.projectivelyNontrivialReal_of_class_ne_one
    C (u : LocalPhase n) u.2 theta hexp hg1
  letI : NeZero (rationalLift C GeneralFiniteness.two_le_three theta hpres).order :=
    ⟨(rationalLift C GeneralFiniteness.two_le_three theta hpres).order_pos.ne'⟩
  set G := finiteGenerator C GeneralFiniteness.two_le_three theta hpres hnt
    with hG
  set T := canonicalTwoFiber G with hT
  letI : NeZero (frameFreshSparsePhase T).data.order := frameFreshOrderNeZero T
  have hclass : G.intrinsicClass = intrinsicClass (exactCodeProjector C) u :=
    GeneralFiniteness.intrinsicClass_finiteGenerator C u theta hexp hpres hnt
  have hm : T.logicalOrder = Nat.card (IntrinsicGroup C) :=
    GroupOrder.logicalOrder_eq_natCard_of_generator T (by rw [hclass]; exact hg)
  set Gb := boundedGenerator T with hGb
  set Tb := canonicalTwoFiber Gb with hTb
  obtain ⟨S, hq, hmS, -, -, -⟩ :=
    SortedForm.exists_sortedNormalForm_of_generator' C Gb
  refine ⟨S, ?_, ?_⟩
  · rw [hq]
    exact automaticFreshGenerator_order_le beta T
  · rw [hmS, Tb.intrinsic_order_eq,
      BoundedGeneratorOrder.logicalOrder_boundedGenerator T Tb, hm]

/-- **`thm:d3-sslp-classification`, unfolded.**

`eq:d3-sslp-bound` is the pair `m | q`, `q <= beta_n`, with `m` the order of
the projective diagonal logical group; `eq:d3-sslp-0` and `eq:d3-sslp-1` are
the two fibre conditions, at residues `0` and `q/m`.  The equivalence to `C`
is explicit: a local `X` string `x0` and a qubit permutation, with the angle
vector sorted. -/
theorem d3_sslp_classification_generator {B : ℕ}
    (beta : BinaryBeta.BetaBound n B)
    (C : CodeSpec.ExactCode n 2 3)
    (hnontrivial : ∃ g : IntrinsicGroup C, g ≠ 1) :
    ∃ (q : ℕ) (_ : NeZero q) (zeta : ℂ) (a : Fin n → ZMod q)
      (F : CodeSpec.OrthonormalFrame n 2)
      (x0 : SS.BitString n) (perm : Equiv.Perm (Fin n)),
      CodeSpec.codeSpan C.frame = CodeSpec.codeSpan F ∧
      IsPrimitiveRoot zeta q ∧
      Gate.Primitive q a ∧
      Monotone (fun j => (a j).val) ∧
      2 ≤ q ∧ q ≤ B ∧
      2 ≤ Nat.card (IntrinsicGroup C) ∧
      Nat.card (IntrinsicGroup C) ∣ q ∧
      SS.HasDistance (fun k s => F.vec k (SS.bxor (permStr perm s) x0)) 3 ∧
      SS.SSConditionState a 0
        (fun s => F.vec 0 (SS.bxor (permStr perm s) x0)) ∧
      SS.SSConditionState a
        (((q / Nat.card (IntrinsicGroup C) : ℕ) : ZMod q))
        (fun s => F.vec 1 (SS.bxor (permStr perm s) x0)) := by
  obtain ⟨S, hqB, hm⟩ := exists_sortedNormalForm_le_betaN_order beta C hnontrivial
  haveI := S.q_ne
  have hF : (fun k s => S.source.vec k (SS.bxor (permStr S.perm s) S.x0))
      = S.frame.vec := by
    funext k s
    exact (S.frame_eq k s).symm
  have h0 : (fun s => S.source.vec 0 (SS.bxor (permStr S.perm s) S.x0))
      = S.frame.vec 0 := by
    funext s
    exact (S.frame_eq 0 s).symm
  have h1 : (fun s => S.source.vec 1 (SS.bxor (permStr S.perm s) S.x0))
      = S.frame.vec 1 := by
    funext s
    exact (S.frame_eq 1 s).symm
  refine ⟨S.q, S.q_ne, S.zeta, S.angle, S.source, S.x0, S.perm,
    S.source_span, S.primitiveRoot, S.primitive, S.sorted, S.two_le_q, hqB,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hm]; exact S.two_le_m
  · rw [← hm]; exact S.m_dvd_q
  · rw [hF]; exact S.hasDistance
  · rw [h0]; exact S.leftFiber
  · rw [h1, ← hm]; exact S.rightFiber

/-- The six-qubit case, unconditionally: `beta_6 = 9` is a kernel theorem. -/
theorem d3_sslp_classification_generator_six
    (C : CodeSpec.ExactCode 6 2 3)
    (hnontrivial : ∃ g : IntrinsicGroup C, g ≠ 1) :
    ∃ S : SortedForm.SortedNormalForm C,
      S.q ≤ 9 ∧ S.m = Nat.card (IntrinsicGroup C) :=
  exists_sortedNormalForm_le_betaN_order
    MainTheory.Generated.BinaryBetaSixKernel.Certificate.upper C hnontrivial

end MainTheory.SSLPGeneratorOrder
