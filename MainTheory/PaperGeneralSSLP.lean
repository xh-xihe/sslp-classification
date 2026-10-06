import MainTheory.GeneralColoredSubspaces
import MainTheory.GeneralColoredConverse
import MainTheory.RankTwoGeneratorGeneral
import MainTheory.RankTwoSSLPCanonical
import MainTheory.SSLPConverse
import MainTheory.SectionTwoGeneral

/-!
# `thm:general-sslp-normal-form` and `cor:rank-two-sslp`, in the paper's shape

The 20260905 revision restructures Section 3: the SSLP normal form is now
stated at arbitrary rank as `thm:general-sslp-normal-form`, with the
one-logical-qubit case demoted to `cor:rank-two-sslp`.

Every piece of both is already proved.  `GeneralColoredExistence` produces the
coloured frame and keeps the original projective class -- `T.intrinsic = g`,
not "the class of some element the construction happened to build", which is
the distinction this project has repeatedly found theorems failing;
`GeneralColoredConverse.ColoredFrame` carries the outer data of
`eq:general-sslp-outer-data` and the colour conditions of
`eq:general-sslp-colors` as fields; and `GeneralColoredSubspaces` supplies
`eq:general-colored-fibers`, both the dimension count and the fibre
containment, together with the direct-sum decomposition.

What was missing is the interface.  None of those files cites a paper label,
so a reader checking the manuscript against the package finds the theorem's
parts and not the theorem.  This file states the two results in the shape the
manuscript states them, and is the file a reader should be sent to.

The rank-two corollary needs no new work either: `rank_two_sslp_canonical`
gives cyclicity and the sorted two-fibre eigenbasis at `d >= 2`,
`RankTwoGeneratorGeneral.exists_sortedNormalForm_natCard` makes its `m` the
order of the whole group as the corollary's "say `C_m`" requires, and
`SSLPConverse.sslp_converse` is its closing sentence.
-/

namespace MainTheory.PaperGeneralSSLP

open MainTheory
open MainTheory.CodeSpec
open MainTheory.GlobalClassificationBridge
open MainTheory.GeneralColoredConverse
open MainTheory.GeneralColoredSubspaces

variable {n K d : ℕ}

/-- **`thm:general-sslp-normal-form`.**

For an exact `((n,K,d))` code with `d >= 2` and a nontrivial projective
diagonal logical element `g` of order `m`, there are outer data
`(q, a)` and colours `gamma` such that the logical eigenspaces have the
prescribed dimensions and sit inside the corresponding subset-sum fibres.

Reading the conclusion against the manuscript:
`2 <= q`, `m | q`, `Monotone`, `Gate.Primitive` are `eq:general-sslp-outer-data`;
`color base = 0`, injectivity, `Gate.Primitive m color` and `sum rank = K` are
`eq:general-sslp-colors`; the `finrank` and `<=` clauses are
`eq:general-colored-fibers`; and the supremum clause says the eigenspaces
really decompose the code rather than merely sitting inside it.

`m = orderOf g` is the point of the statement: the normal form is built for
the element supplied, not for one the construction chose.

The `T`, `x0` and `sigma` are the manuscript's "up to local `X` conjugation,
permutation of the physical qubits, and a logical scalar", and they are not
decoration.  Dropping them leaves a statement that asserts some coloured frame
of distance `d` exists somewhere, with no claim that it is a normal form of
`C` at all -- true, and not the theorem.  `T.intrinsic = g` keeps the original
projective class, `frame_eq` is the explicit `X^{x0}` conjugation followed by
the qubit permutation, and `angle_eq` says the outer data is the permuted flip
of the code's own lift. -/
theorem general_sslp_normal_form (C : ExactCode n K d) (hd : 2 ≤ d)
    (g : IntrinsicGroup C) (hg : g ≠ 1) :
    ∃ (q m t : ℕ) (hq : NeZero q) (hm : NeZero m)
      (T : @GeneralColoredNormalForm.FiniteSectors n K d C q t hq)
      (S : @ColoredFrame n K q m t hq hm)
      (x0 : SS.BitString n) (sigma : Equiv.Perm (Fin n)),
      T.intrinsic = g ∧ m = orderOf g ∧ 2 ≤ m ∧ 2 ≤ q ∧ m ∣ q ∧
      (∀ j s, S.frame.vec j s =
        T.frame.vec j (SS.bxor (SixQubit.CodeEquiv.permStr sigma s) x0)) ∧
      S.angle = PermutationSemanticTransport.permAngle sigma
        (Normalize.flip T.angle x0) ∧
      Monotone (fun j => (S.angle j).val) ∧
      Gate.Primitive q S.angle ∧
      S.color S.base = 0 ∧
      Function.Injective S.color ∧
      Gate.Primitive m S.color ∧
      (∑ alpha, S.rank alpha) = K ∧
      (∀ alpha, Module.finrank ℂ (ColoredFrame.sectorSpace S alpha) = S.rank alpha) ∧
      (∀ alpha, ColoredFrame.sectorSpace S alpha ≤
        fiberSubspace S.angle (ColoredResidueArithmetic.scaledColor q (S.color alpha))) ∧
      (⨆ alpha, ColoredFrame.sectorSpace S alpha) = codeSpan S.frame ∧
      SS.HasDistance S.frame.vec d := by
  obtain ⟨q, m, t, hq, hm, T, S, x0, sigma, hclass, hmg, hm2, hq2,
    _, _, _, _, hangle, hframe, _, hdist⟩ :=
    MainTheory.GeneralColoredExistence.general_colored_sslp_normal_form C hd g hg
  refine ⟨q, m, t, hq, hm, T, S, x0, sigma, hclass, hmg, hm2, hq2, S.modulus_dvd,
    hframe, hangle, S.sorted, S.primitive,
    S.color_zero, S.color_distinct, S.color_primitive, S.sum_rank, ?_, ?_, ?_, hdist⟩
  · exact fun alpha => ColoredFrame.sectorSpace_finrank S alpha
  · exact fun alpha => ColoredFrame.sectorSpace_le_fiber S alpha
  · exact ColoredFrame.iSup_sectorSpace S

/-- **`cor:rank-two-sslp`.**

The one-logical-qubit specialization, at the manuscript's own `d >= 2` and
under its own hypothesis on the group rather than on a chosen phase vector.

The record's fields are the corollary's displays: `sorted` and `lt_q` are
`eq:a-canonical`'s ordering, `primitive` its `gcd` condition, `leftFiber` and
`rightFiber` are `eq:0L-fiber` and `eq:1L-fiber`, `m_dvd_q` is `eq:K2-bound`,
and `source_span` with `frame_eq` are the local `X` conjugation and the qubit
permutation.  `S.m = Nat.card` is the corollary's "say `C_m`": the group
itself, not the order of one of its elements. -/
theorem rank_two_sslp (C : ExactCode n 2 d) (hd : 2 ≤ d)
    (hnontrivial : ∃ g : IntrinsicGroup C, g ≠ 1) :
    IsCyclic (ClassificationLevels.IntrinsicProjectiveDiagonalLogicalGroup
      (ClassificationLevels.CodeProjector.ofFrame C.frame)) ∧
    Finite (IntrinsicGroup C) ∧
    ∃ S : SortedForm.SortedNormalForm C,
      S.m = Nat.card (IntrinsicGroup C) ∧
      2 ≤ S.q ∧ 2 ≤ S.m ∧ S.m ∣ S.q ∧
      Monotone (fun j => (S.angle j).val) ∧
      (∀ j, (S.angle j).val < S.q) ∧
      Gate.Primitive S.q S.angle ∧
      SS.SSConditionState S.angle 0 (S.frame.vec 0) ∧
      SS.SSConditionState S.angle (((S.q / S.m : ℕ) : ZMod S.q)) (S.frame.vec 1) ∧
      SS.HasDistance S.frame.vec d ∧
      CodeSpec.codeSpan C.frame = CodeSpec.codeSpan S.source ∧
      (∀ k s, S.frame.vec k s =
        S.source.vec k (SS.bxor (SixQubit.CodeEquiv.permStr S.perm s) S.x0)) := by
  obtain ⟨S, hcard⟩ :=
    MainTheory.RankTwoGeneratorGeneral.exists_sortedNormalForm_natCard hd C hnontrivial
  exact ⟨MainTheory.ProjectiveGroupGeneral.cyclic_of_rank_two C hd,
    MainTheory.GeneralFinitenessRank.finite_intrinsicGroup C hd,
    S, hcard, S.two_le_q, S.two_le_m, S.m_dvd_q, S.sorted, S.lt_q, S.primitive,
    S.leftFiber, S.rightFiber, S.hasDistance, S.source_span, S.frame_eq⟩

/-- The corollary's closing sentence, at arbitrary length: any orthonormal pair
of the displayed form satisfying the complete Knill--Laflamme equations defines
a code on which `D(a;q)` acts projectively with order exactly `m`. -/
theorem rank_two_sslp_converse {q m : ℕ} [NeZero q] {zeta : ℂ}
    (hzeta : IsPrimitiveRoot zeta q) {a : Fin n → ZMod q}
    (hprim : Gate.Primitive q a) (hmq : m ∣ q) (hm : 2 ≤ m)
    (F : OrthonormalFrame n 2) (hdist : SS.HasDistance F.vec d)
    (h0 : SS.SSConditionState a 0 (F.vec 0))
    (h1 : SS.SSConditionState a ((((q / m : ℕ)) : ZMod q)) (F.vec 1)) :
    ∃ (C : ExactCode n 2 d) (g : IntrinsicGroup C),
      C.frame = F ∧ orderOf g = m ∧ g ≠ 1 :=
  MainTheory.SSLPConverse.sslp_converse hzeta hprim hmq hm F hdist h0 h1


/-! ## `lem:phase-sector-support` -/

/-- **`lem:phase-sector-support`, clauses (i) and (ii).**

The manuscript states this lemma under one hypothesis -- that `D(theta)`
preserves the code -- and its proof uses only the spectral decomposition
`eq:spectral-decomp`.  Detection enters the surrounding section only for the
common first moment of `eq:Nj-detection`, which is a different statement.

The Lean side matches that division exactly: `sectorSupport_nonempty`,
`sectorSupport_disjoint` and `phase_congruence` each take a bare
`SectorDecomposition`, while `exists_common_sector_mean` is the one that asks
for `ZDetects`.  So this is stated with no detection and no distance
hypothesis, which is what the manuscript claims and is stronger than the
packaged `SectionTwoGeneral.phaseSectors`, whose `2 <= d` is inherited from
the mean clause it also carries. -/
theorem phase_sector_support (C : ExactCode n K d) (theta : Fin n → ℝ)
    (hpres : CodePreserving C.frame (PhaseSectorBridge.realGateEnd theta)) :
    (∀ alpha,
      (PhaseSectorFull.sectorSupport
        (SectionTwoGeneral.resolutionOf C theta hpres).sectors alpha).Nonempty) ∧
    (∀ alpha beta, alpha ≠ beta →
      Disjoint
        (PhaseSectorFull.sectorSupport
          (SectionTwoGeneral.resolutionOf C theta hpres).sectors alpha)
        (PhaseSectorFull.sectorSupport
          (SectionTwoGeneral.resolutionOf C theta hpres).sectors beta)) ∧
    (∀ alpha x,
      x ∈ PhaseSectorFull.sectorSupport
        (SectionTwoGeneral.resolutionOf C theta hpres).sectors alpha →
      ∃ k : ℤ, MainTheory.RealGate.angle theta x
        - (SectionTwoGeneral.resolutionOf C theta hpres).sectors.phase alpha
          = (k : ℝ)) :=
  ⟨PhaseSectorFull.sectorSupport_nonempty _,
    fun _ _ => PhaseSectorFull.sectorSupport_disjoint _,
    PhaseSectorFull.phase_congruence _⟩

end MainTheory.PaperGeneralSSLP
