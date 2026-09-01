import MainTheory.SectionTwoGeneral
import MainTheory.BoundedRepresentationProof
import MainTheory.BetaExists
import MainTheory.LogicalCharacter
import MainTheory.IntrinsicAbelian

/-!
# Finiteness and cyclicity at arbitrary `n`

`thm:finite-projective-group` asserts the projective diagonal logical group is
finite abelian, and `thm:rank-two-sslp` that in rank two it is cyclic.  Both
were available in this repository only at six qubits, because the bound that
drove them -- `q <= 9` -- is a 1716-case certificate specific to `n = 6`.

The generalization does not need that certificate, only the *existence* of a
bound, which `BetaExists.exists_betaBound` supplies at every size.  Chaining
it with the now-general spectral extraction, finite-generator packaging and
bounded-representation transport gives finiteness for every exact rank-two
distance-three code, and cyclicity follows from the phase-ratio character.

What does not generalize, and is not claimed to: the *value* nine.  At
arbitrary `n` one gets some bound, named by a supremum over a finite type,
with nothing said about its size.
-/

namespace MainTheory.GeneralFiniteness

open MainTheory.ClassificationLevels
open MainTheory.GlobalClassificationBridge
open MainTheory.SectionTwoGeneral
open MainTheory.D3AutomaticBoundedGenerator
open MainTheory.D3NormalizedFreshPhase

variable {n : ℕ}

/-- The distance hypothesis these modules need, as a single named term.

Using `by norm_num` at each occurrence would produce syntactically different
proofs of the same triviality, and the `NeZero` instances downstream would
then fail to line up. -/
theorem two_le_three : (2 : ℕ) ≤ 3 := by norm_num

/-- **Every class of the intrinsic group has a bounded representative**, at
arbitrary `n`.

The bound is `BetaExists.betaOf n`, the largest inverse denominator among
zero--one matrices of size at most `n`. -/
theorem hasBoundedRepresentation {B : ℕ} (beta : BinaryBeta.BetaBound n B)
    (C : CodeSpec.ExactCode n 2 3) (theta : Fin n → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id) :
    letI : NeZero (rationalLift C two_le_three theta hpres).order :=
      ⟨(rationalLift C two_le_three theta hpres).order_pos.ne'⟩
    BoundedClassPower.BoundedClass B
      (exactCodeProjector C)
      (finiteGenerator C two_le_three theta hpres hnt).intrinsicClass := by
  letI : NeZero (rationalLift C two_le_three theta hpres).order :=
    ⟨(rationalLift C two_le_three theta hpres).order_pos.ne'⟩
  set G := finiteGenerator C two_le_three theta hpres hnt with hG
  refine BoundedRepresentationProof.boundedClass_of_twoFiber G
    (canonicalTwoFiber G)
    (automaticFreshGeneratorOfGenerator_order_le beta G) ?_
  exact automaticFreshGenerator_sameProjective_normalizedFinite
    (canonicalTwoFiber G)

/-- **Every class of the intrinsic group is bounded**, at arbitrary `n`.

The trivial class is named by the trivial label; every other class supplies a
projectively nontrivial symmetry, whose generator is bounded by the theorem
above, and the class is recovered from a coprime power of it. -/
theorem hasBoundedRepresentation_general {B : ℕ}
    (beta : BinaryBeta.BetaBound n B) (hB : 0 < B)
    (C : CodeSpec.ExactCode n 2 3) :
    BoundedRepresentation.HasBoundedRepresentation B C := by
  intro g
  by_cases hg : g = 1
  · subst hg
    exact SymmetryToEntrance.exists_label_of_class_one C hB
  · obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨theta, hexp⟩ :=
      LocalPhaseAngle.exists_angleVector (u : LocalPhase n)
    have hpres := SymmetryToEntrance.codePreserving_of_symmetry C.frame
      (u : LocalPhase n) u.2 theta hexp
    have hnt := SymmetryToEntrance.projectivelyNontrivialReal_of_class_ne_one
      C (u : LocalPhase n) u.2 theta hexp hg
    letI : NeZero (rationalLift C two_le_three theta hpres).order :=
      ⟨(rationalLift C two_le_three theta hpres).order_pos.ne'⟩
    set G := finiteGenerator C two_le_three theta hpres hnt with hG
    have hz : G.zeta ^ (rationalLift C two_le_three theta hpres).order = 1 :=
      G.primitiveRoot.pow_eq_one
    have hGu : G.intrinsicClass
        = intrinsicClass (exactCodeProjector C) u := by
      rw [BoundedRepresentationProof.intrinsicClass_eq_phaseOfAngle G]
      obtain ⟨lam, hlam, hact⟩ :=
        finiteGenerator_sameProjective C two_le_three theta hpres hnt
      refine IntrinsicClassBridge.intrinsicClass_eq_of_sameProjective
        (exactCodeProjector C) _ _ lam hlam (fun phi hphi => ?_)
      have hmem : phi ∈ CodeSpec.codeSpan C.frame :=
        (inProjectorRange_ofFrame_iff C.frame phi).1 hphi
      have hthis := hact phi hmem
      simp only [D3RationalLiftFiniteGenerator.finiteGeneratorOfLiftEnd,
        RankTwoGlobal.finiteGateEnd, LinearMap.coe_mk, AddHom.coe_mk] at hthis
      rw [show D3RationalLiftFiniteGenerator.finiteGeneratorOfLift
          (resolutionOf C theta hpres) (rationalLift C two_le_three theta hpres)
          hnt = G from rfl] at hthis
      rw [MainTheory.FiniteGateAsPhase.gate_eq_diagonalAction G.zeta hz G.angle phi,
        SymmetryToEntrance.realGateEnd_eq_diagonalAction
          (u : LocalPhase n) theta hexp phi] at hthis
      exact hthis
    show BoundedClassPower.BoundedClass B
      (exactCodeProjector C) (intrinsicClass (exactCodeProjector C) u)
    rw [← hGu]
    exact hasBoundedRepresentation beta C theta hpres hnt

/-- **The intrinsic projective diagonal group is finite**, at arbitrary `n`. -/
theorem finite_intrinsicGroup (C : CodeSpec.ExactCode n 2 3) :
    Finite (IntrinsicGroup C) :=
  BoundedRepresentation.finite_of_representation
    (hasBoundedRepresentation_general (BetaExists.betaBound_betaOf n)
      (BetaExists.betaOf_pos n) C)

/-! ## Cyclicity at arbitrary `n` -/

/-- **The intrinsic projective diagonal group is cyclic**, at arbitrary `n`,
with no hypothesis at all.

An independent review pointed out that the nontriviality hypothesis this
theorem first carried was not needed: if no symmetry is projectively
nontrivial then every class is the identity and the group is a subsingleton,
which is cyclic.  So `thm:rank-two-sslp`'s "that group is cyclic, say `C_m`"
holds for every exact rank-two distance-three code outright, and the paper's
nontriviality assumption is only what makes `m >= 2`. -/
theorem isCyclic (C : CodeSpec.ExactCode n 2 3) :
    IsCyclic (IntrinsicProjectiveDiagonalLogicalGroup
      (CodeProjector.ofFrame C.frame)) := by
  by_cases h : ∃ u0 : diagonalSymmetryGroup (CodeProjector.ofFrame C.frame),
      ¬ IsProjectivelyTrivial (CodeProjector.ofFrame C.frame) u0
  · obtain ⟨u0, h0⟩ := h
    exact LogicalCharacter.isCyclic_of_nontrivial C u0 h0
      (finite_intrinsicGroup C)
  · push_neg at h
    haveI : Subsingleton (IntrinsicProjectiveDiagonalLogicalGroup
        (CodeProjector.ofFrame C.frame)) := by
      constructor
      intro a b
      refine QuotientGroup.induction_on a (fun x => ?_)
      refine QuotientGroup.induction_on b (fun y => ?_)
      rw [QuotientGroup.eq]
      exact h _
    infer_instance

/-- **The projective diagonal logical group is finite abelian**, at arbitrary
`n` -- `thm:finite-projective-group`'s conclusion for rank two.

A note on weight: the finiteness half is the substantive one.  Abelianness is
pointwise commutativity of `LocalPhase n` carried through the quotient, and
would hold of a projector unrelated to any code; it is bundled here only
because the paper states the two together. -/
theorem finite_and_abelian (C : CodeSpec.ExactCode n 2 3) :
    Finite (IntrinsicGroup C) ∧
      ∀ g h : IntrinsicProjectiveDiagonalLogicalGroup
        (CodeProjector.ofFrame C.frame), g * h = h * g :=
  ⟨finite_intrinsicGroup C,
    IntrinsicAbelian.intrinsicGroup_mul_comm _⟩

/-- **The general result recovers the sharp six-qubit statement.**

An independent review noted that a finiteness theorem phrased only in terms of
`betaOf n` -- a supremum over a finite type, of unknown size -- could not
recover `q <= 9`.  Because the theorem above takes an arbitrary bound, feeding
it the certified `BetaBound 6 9` returns exactly the six-qubit form: every
class is named by a label of modulus at most nine. -/
theorem hasBoundedRepresentation_six
    (betaSix : BinaryBeta.BetaBound 6 9) (C : CodeSpec.ExactCode 6 2 3) :
    BoundedRepresentation.HasBoundedRepresentation 9 C :=
  hasBoundedRepresentation_general betaSix (by norm_num) C

end MainTheory.GeneralFiniteness
