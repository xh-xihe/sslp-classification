import MainTheory.GeneralColoredNormalForm

/-! # The general colored SSLP theorem from an actual exact code -/

namespace MainTheory.GeneralColoredExistence

open ClassificationLevels GlobalClassificationBridge PhaseSectorBridge PhaseSectorFull
open D3RationalLiftFiniteGenerator GeneralColoredNormalForm GeneralColoredConverse
open ColoredResidueArithmetic PermutationSemanticTransport

noncomputable section

variable {n K d : ℕ} {theta : Fin n → ℝ} {C : CodeSpec.ExactCode n K d}

set_option linter.unusedSectionVars false

def sectorPoint (R : LogicalSectorResolution C theta) (alpha : Fin R.sectorCount) :
    SS.BitString n := Classical.choose (sectorSupport_nonempty R.sectors alpha)

theorem sectorPoint_mem (R : LogicalSectorResolution C theta) (alpha : Fin R.sectorCount) :
    sectorPoint R alpha ∈ sectorSupport R.sectors alpha :=
  Classical.choose_spec (sectorSupport_nonempty R.sectors alpha)

variable (R : LogicalSectorResolution C theta)
  (L : FiniteLift.RationalColoredLift R.sectors) [NeZero L.order]

theorem finite_sector_eigen (u : R.sectors.Index) :
    Gate.gate (D3NormalizedFiniteToReal.canonicalRoot L.order) (modularAngle L)
      (R.sectors.vec u) =
      fun x => (projectiveScalar L * phaseExp (R.sectors.phase u.1)) * R.sectors.vec u x := by
  rw [finiteGate_eq_rationalRealGate, projectiveScalar_action L u]
  funext x
  rw [congrFun (R.sectors.eigen u) x]
  ring

def sectorResidue (alpha : Fin R.sectorCount) : ZMod L.order :=
  SS.weight (modularAngle L) (sectorPoint R alpha)

theorem chi_sectorResidue (alpha : Fin R.sectorCount) :
    Cyclic.chi (D3NormalizedFiniteToReal.canonicalRoot L.order) (sectorResidue R L alpha)
      = projectiveScalar L * phaseExp (R.sectors.phase alpha) := by
  obtain ⟨r, hr⟩ := exists_vec_ne_zero_of_mem_support R.sectors alpha
    (sectorPoint R alpha) (sectorPoint_mem R alpha)
  exact PhaseSector.diag_eq_of_eigen _ _ _ _ (finite_sector_eigen R L ⟨alpha, r⟩) _ hr

theorem sectorResidue_injective : Function.Injective (sectorResidue R L) := by
  intro alpha beta h
  apply R.sectors.phaseDistinct
  apply mul_left_cancel₀ (projectiveScalar_ne_zero L)
  rw [← chi_sectorResidue R L alpha, ← chi_sectorResidue R L beta, h]

theorem sector_fiber (u : R.sectors.Index) :
    SS.SSConditionState (modularAngle L) (sectorResidue R L u.1) (R.sectors.vec u) := by
  intro x hx
  apply Cyclic.chi_injective (D3NormalizedFiniteToReal.canonicalRoot L.order)
    (D3NormalizedFiniteToReal.canonicalRoot_primitive L.order)
  rw [chi_sectorResidue]
  exact PhaseSector.diag_eq_of_eigen _ _ _ _ (finite_sector_eigen R L u) x hx

/-- The primitive finite sectors are constructed from the actual spectral lift. -/
def finiteSectorsOfLift : FiniteSectors C L.order R.sectorCount where
  angle := modularAngle L
  primitive := modularAngle_primitive L
  rank := R.sectors.rank
  rank_pos := R.sectors.rank_pos
  reindex := R.link.reindex
  frame := FiniteLift.reindexedSectorFrame R.sectors R.link.reindex
  span_eq := R.link.span_eq
  base := FiniteLift.baseSector R.sectors
  residue := sectorResidue R L
  residue_distinct := sectorResidue_injective R L
  fiber j := sector_fiber R L (R.link.reindex j)

theorem finiteSectorsOfLift_intrinsic
    (v : diagonalSymmetryGroup (exactCodeProjector C))
    (hexp : ∀ j, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((theta j : ℝ) : ℂ))
      = (((v : LocalPhase n) j : ℂ))) :
    (finiteSectorsOfLift R L).intrinsic = intrinsicClass (exactCodeProjector C) v := by
  have hs : (finiteSectorsOfLift R L).symmetry = GeneralLiftOrder.liftSymmetry R L := by
    apply Subtype.ext
    rfl
  rw [FiniteSectors.intrinsic, hs]
  exact GeneralLiftOrder.intrinsicClass_liftSymmetry R L v hexp

/-- **The forward general colored SSLP normal form**, retaining the original
projective class, the actual source code, and its requested distance.

The finite sectors `T` represent the original class `g`.  The displayed
colored frame `S` is precisely its local-X and coordinate-permutation image,
with no change of logical generator.  Its colors are unique residues in
`ZMod m`, and the record contains both primitivity conditions and sorted angles.
-/
theorem general_colored_sslp_normal_form (C : CodeSpec.ExactCode n K d)
    (hd : 2 ≤ d) (g : IntrinsicGroup C) (hg : g ≠ 1) :
    ∃ (q m t : ℕ) (hq : NeZero q) (hm : NeZero m)
      (T : @FiniteSectors n K d C q t hq)
      (S : @ColoredFrame n K q m t hq hm)
      (x0 : SS.BitString n) (sigma : Equiv.Perm (Fin n)),
      T.intrinsic = g ∧ m = orderOf g ∧ 2 ≤ m ∧ 2 ≤ q ∧
      S.rank = T.rank ∧ HEq S.reindex T.reindex ∧ S.base = T.base ∧ S.base.val = 0 ∧
      S.angle = permAngle sigma (Normalize.flip T.angle x0) ∧
      (∀ j s, S.frame.vec j s =
        T.frame.vec j (SS.bxor (SixQubit.CodeEquiv.permStr sigma s) x0)) ∧
      (∀ alpha, scaledColor q (S.color alpha) = T.delta alpha) ∧
      SS.HasDistance S.frame.vec d := by
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨theta, hexp⟩ := LocalPhaseAngle.exists_angleVector (v : LocalPhase n)
  have hpres := SymmetryToEntrance.codePreserving_of_symmetry C.frame
    (v : LocalPhase n) v.2 theta hexp
  let R := SectionTwoGeneral.resolutionOf C theta hpres
  obtain ⟨L⟩ := FiniteLift.exists_rationalColoredLift R.sectors (R.zDetects hd)
  letI : NeZero L.order := ⟨L.order_pos.ne'⟩
  let T := finiteSectorsOfLift R L
  have hclass : T.intrinsic = intrinsicClass (exactCodeProjector C) v :=
    finiteSectorsOfLift_intrinsic R L v hexp
  let m := orderOf T.intrinsic
  letI : NeZero m := ⟨T.order_pos.ne'⟩
  have hm2 : 2 ≤ m := by
    have hmpos := T.order_pos
    have hm1 : m ≠ 1 := by
      intro h
      exact hg (by change intrinsicClass (exactCodeProjector C) v = 1
                   rw [← hclass]; exact orderOf_eq_one_iff.1 h)
    omega
  have hq2 : 2 ≤ L.order := le_trans hm2
    (Nat.le_of_dvd L.order_pos T.order_dvd)
  obtain ⟨S, x0, sigma, hrank, he, hbase, ha, hf, hc, hdS⟩ :=
    T.exists_normalized (m := m) rfl
  exact ⟨L.order, m, R.sectorCount, inferInstance, inferInstance, T, S, x0, sigma,
    hclass, congrArg orderOf hclass, hm2, hq2, hrank, he, hbase,
    by rw [hbase]; rfl, ha, hf, hc, hdS⟩

end

end MainTheory.GeneralColoredExistence
