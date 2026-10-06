import MainTheory.GeneralFiniteness
import MainTheory.ProjectiveGroupGeneral
import MainTheory.SortedNormalForm

/-!
# `thm:rank-two-sslp`'s `C_m` at the paper's own `d >= 2`

`thm:rank-two-sslp` says the projective diagonal logical group "is cyclic, say
`C_m`", and then takes a *generator*, so its `m` is the order of the whole
group.  `GroupOrder.rank_two_sslp_generator` says exactly that -- at `d = 3`,
because the class identification it runs on,
`GeneralFiniteness.intrinsicClass_finiteGenerator`, was stated only there.  At
the paper's own hypothesis `d >= 2` the strongest statement was
`RankTwoSSLPCanonical.rank_two_sslp_canonical`, whose modulus is pinned only by
the record's `m_isOrder` field: the order of *some* element, hence a divisor of
`Nat.card` rather than `Nat.card`.

Nothing in the identification was ever distance-three.  `finiteGenerator` and
`finiteGenerator_sameProjective` both carry `hd : 2 <= d` already, and the
proof below is the `d = 3` one with `two_le_three` replaced by `hd`.  With it,
the group half of `thm:rank-two-sslp` holds at `d >= 2` with the paper's `m`:
finiteness is `GeneralFinitenessRank.finite_intrinsicGroup`, cyclicity is
`ProjectiveGroupGeneral.cyclic_of_rank_two`, and a generator exists because the
group is finite and cyclic.
-/

namespace MainTheory.RankTwoGeneratorGeneral

open MainTheory
open MainTheory.ClassificationLevels
open MainTheory.GlobalClassificationBridge
open MainTheory.SectionTwoGeneral
open MainTheory.GeneralFiniteness

variable {n : ℕ}

/-- **The class identification at the paper's own `d >= 2`.**

Verbatim the `d = 3` proof of `GeneralFiniteness.intrinsicClass_finiteGenerator`
with the distance hypothesis left general; nothing in it was ever specific to
three. -/
theorem intrinsicClass_finiteGenerator' {d : ℕ} (hd : 2 ≤ d)
    (C : CodeSpec.ExactCode n 2 d)
    (u : diagonalSymmetryGroup (exactCodeProjector C))
    (theta : Fin n → ℝ)
    (hexp : ∀ j, Complex.exp (2 * (Real.pi : ℂ) * Complex.I
      * ((theta j : ℝ) : ℂ)) = (((u : LocalPhase n) j : ℂ)))
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id) :
    letI : NeZero (rationalLift C hd theta hpres).order :=
      ⟨(rationalLift C hd theta hpres).order_pos.ne'⟩
    (finiteGenerator C hd theta hpres hnt).intrinsicClass
      = intrinsicClass (exactCodeProjector C) u := by
  letI : NeZero (rationalLift C hd theta hpres).order :=
    ⟨(rationalLift C hd theta hpres).order_pos.ne'⟩
  set G := finiteGenerator C hd theta hpres hnt with hG
  obtain ⟨lam, hlam, hact⟩ :=
    finiteGenerator_sameProjective C hd theta hpres hnt
  show intrinsicClass (exactCodeProjector C) G.intrinsicSymmetry
      = intrinsicClass (exactCodeProjector C) u
  refine IntrinsicClassBridge.intrinsicClass_eq_of_sameProjective
    (exactCodeProjector C) _ _ lam hlam (fun phi hphi => ?_)
  have hmem : phi ∈ CodeSpec.codeSpan C.frame :=
    (inProjectorRange_ofFrame_iff C.frame phi).1 hphi
  have hthis := hact phi hmem
  simp only [D3RationalLiftFiniteGenerator.finiteGeneratorOfLiftEnd,
    RankTwoGlobal.finiteGateEnd, LinearMap.coe_mk, AddHom.coe_mk] at hthis
  rw [show D3RationalLiftFiniteGenerator.finiteGeneratorOfLift
      (resolutionOf C theta hpres) (rationalLift C hd theta hpres) hnt = G from rfl,
    ← diagonalAction_finiteLocalPhase G.zeta G.primitiveRoot G.angle phi,
    SymmetryToEntrance.realGateEnd_eq_diagonalAction
      (u : LocalPhase n) theta hexp phi] at hthis
  exact hthis

/-- **`thm:rank-two-sslp`'s `m` is the group order, at `d >= 2`.**

The normal form returned has `S.m = Nat.card (IntrinsicGroup C)`, not merely
the order of some element. -/
theorem exists_sortedNormalForm_natCard {d : ℕ} (hd : 2 ≤ d)
    (C : CodeSpec.ExactCode n 2 d)
    (hnontrivial : ∃ g : IntrinsicGroup C, g ≠ 1) :
    ∃ S : SortedForm.SortedNormalForm C,
      S.m = Nat.card (IntrinsicGroup C) := by
  haveI := MainTheory.GeneralFinitenessRank.finite_intrinsicGroup C hd
  haveI := MainTheory.ProjectiveGroupGeneral.cyclic_of_rank_two C hd
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := IntrinsicGroup C)
  have hg1 : g ≠ 1 := by
    rintro rfl
    obtain ⟨x, hx⟩ := hnontrivial
    exact hx (by simpa using hg x)
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨theta, hexp⟩ :=
    MainTheory.LocalPhaseAngle.exists_angleVector (u : LocalPhase n)
  have hpres := MainTheory.SymmetryToEntrance.codePreserving_of_symmetry C.frame
    (u : LocalPhase n) u.2 theta hexp
  have hnt := MainTheory.SymmetryToEntrance.projectivelyNontrivialReal_of_class_ne_one
    C (u : LocalPhase n) u.2 theta hexp hg1
  letI : NeZero (rationalLift C hd theta hpres).order :=
    ⟨(rationalLift C hd theta hpres).order_pos.ne'⟩
  obtain ⟨S, _, hmS, _, _, _⟩ :=
    SortedForm.exists_sortedNormalForm_of_generator' C
      (finiteGenerator C hd theta hpres hnt)
  refine ⟨S, ?_⟩
  rw [hmS, intrinsicClass_finiteGenerator' hd C u theta hexp hpres hnt]
  have htop : Subgroup.zpowers (intrinsicClass (exactCodeProjector C) u)
      = (⊤ : Subgroup (IntrinsicGroup C)) :=
    (Subgroup.eq_top_iff' _).2 hg
  calc
    orderOf (intrinsicClass (exactCodeProjector C) u)
        = Nat.card (Subgroup.zpowers (intrinsicClass (exactCodeProjector C) u)) :=
      (Nat.card_zpowers _).symm
    _ = Nat.card ((⊤ : Subgroup (IntrinsicGroup C)) : Set (IntrinsicGroup C)) := by
        rw [htop]; rfl
    _ = Nat.card (IntrinsicGroup C) := by simp

end MainTheory.RankTwoGeneratorGeneral
