import QECC.IntrinsicSSLP
import QECC.ColorArithmetic

namespace QECC

open scoped BigOperators

noncomputable section

/-- The projectively meaningful eigenvalue ratio for two common logical
eigenlines.  Additive circle phases turn division of eigenvalues into
subtraction. -/
def eigenvalueRatio {G : Type*} [AddGroup G]
    (lambda0 lambda1 : G →+ UnitAddCircle) : G →+ UnitAddCircle :=
  lambda1 - lambda0

@[simp] theorem eigenvalueRatio_apply {G : Type*} [AddGroup G]
    (lambda0 lambda1 : G →+ UnitAddCircle) (g : G) :
    eigenvalueRatio lambda0 lambda1 g = lambda1 g - lambda0 g :=
  rfl

/-- The eigenvalue-ratio homomorphism is faithful if equal phases on the two
eigenlines occur only for the projective identity. -/
theorem eigenvalueRatio_injective {G : Type*} [AddGroup G]
    (lambda0 lambda1 : G →+ UnitAddCircle)
    (hfaithful : ∀ g, lambda1 g = lambda0 g → g = 0) :
    Function.Injective (eigenvalueRatio lambda0 lambda1) := by
  intro g h hgh
  have hzero : eigenvalueRatio lambda0 lambda1 (g - h) = 0 := by
    rw [map_sub, hgh, sub_self]
  have heq : lambda1 (g - h) = lambda0 (g - h) := by
    exact sub_eq_zero.mp hzero
  exact sub_eq_zero.mp (hfaithful (g - h) heq)

/-- A finite additive group that embeds in the circle is cyclic.  This is the
abstract form of the eigenvalue-ratio argument for a two-dimensional logical
space. -/
theorem isAddCyclic_of_finite_injective_unitAddCircle
    {G : Type*} [AddGroup G] [Finite G]
    (ratio : G →+ UnitAddCircle) (hratio : Function.Injective ratio) :
    IsAddCyclic G := by
  let circleMap : Multiplicative G →* ℂ :=
    { toFun := fun g => ((AddCircle.toCircle (ratio g.toAdd) : Circle) : ℂ)
      map_one' := by simp
      map_mul' := by
        intro g h
        change (((AddCircle.toCircle (ratio (g.toAdd + h.toAdd))) : Circle) : ℂ) =
          (((AddCircle.toCircle (ratio g.toAdd)) : Circle) : ℂ) *
            (((AddCircle.toCircle (ratio h.toAdd)) : Circle) : ℂ)
        rw [map_add, AddCircle.toCircle_add, Circle.coe_mul] }
  have hcircleMap : Function.Injective circleMap := by
    intro g h hgh
    apply Multiplicative.toAdd.injective
    apply hratio
    apply AddCircle.injective_toCircle one_ne_zero
    apply Subtype.coe_injective
    exact hgh
  letI : IsCyclic (Multiplicative G) :=
    isCyclic_of_subgroup_isDomain circleMap hcircleMap
  obtain ⟨g, hg⟩ :
      ∃ g : Multiplicative G, Function.Surjective (fun k : ℤ => g ^ k) :=
    IsCyclic.exists_zpow_surjective
  refine ⟨⟨g.toAdd, ?_⟩⟩
  intro x
  obtain ⟨k, hk⟩ := hg (Multiplicative.ofAdd x)
  refine ⟨k, ?_⟩
  apply Multiplicative.ofAdd.injective
  simpa using hk

/-- Every finite additive subgroup of the unit circle is cyclic. -/
instance AddSubgroup.unitAddCircle_isAddCyclic (H : AddSubgroup UnitAddCircle)
    [Finite H] : IsAddCyclic H :=
  isAddCyclic_of_finite_injective_unitAddCircle H.subtype H.subtype_injective

/-- Multiplication by a unit modulo `q` commutes with the color embedding,
where the unit acts on colors through reduction modulo `m`. -/
theorem unit_mul_colorEmbed {m q : ℕ} (hmq : m ∣ q) (u : (ZMod q)ˣ)
    (gamma : ZMod m) :
    (u : ZMod q) * colorEmbed m q hmq gamma =
      colorEmbed m q hmq
        (((ZMod.unitsMap hmq u : (ZMod m)ˣ) : ZMod m) * gamma) := by
  obtain ⟨w, hw⟩ := ZMod.intCast_surjective (u : ZMod q)
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective gamma
  have hred : ((ZMod.unitsMap hmq u : (ZMod m)ˣ) : ZMod m) =
      (w : ZMod m) := by
    rw [ZMod.unitsMap_val, ← hw, ZMod.cast_intCast hmq]
  rw [hred]
  rw [← Int.cast_mul]
  rw [← hw, colorEmbed_intCast, colorEmbed_intCast]
  push_cast
  ring

/-- A primitive rank-two color can be normalized to `1` by a unit modulo the
physical order.  The chosen physical power remains a generator modulo `q`. -/
theorem exists_unit_scaling_colorEmbed_eq_one {m q : ℕ} (hq : 0 < q)
    (hmq : m ∣ q) (gamma : ZMod m) (hgamma : IsUnit gamma) :
    ∃ u : (ZMod q)ˣ,
      (u : ZMod q) * colorEmbed m q hmq gamma =
        colorEmbed m q hmq 1 := by
  obtain ⟨u, hu⟩ := exists_unit_lift_mul_eq_one hq hmq gamma hgamma
  refine ⟨u, ?_⟩
  rw [unit_mul_colorEmbed hmq u gamma, hu]

/-- Having full additive order in `ZMod m` is the same primitivity condition
needed to regard a rank-two color as a unit. -/
theorem isUnit_of_addOrderOf_eq_modulus {m : ℕ} (hm : 0 < m)
    (gamma : ZMod m) (hgamma : addOrderOf gamma = m) : IsUnit gamma := by
  letI : NeZero m := ⟨hm.ne'⟩
  have hval : (gamma.val : ZMod m) = gamma := ZMod.natCast_zmod_val gamma
  have hgamma' : addOrderOf (gamma.val : ZMod m) = m := by
    rw [hval]
    exact hgamma
  rw [ZMod.addOrderOf_coe gamma.val hm.ne'] at hgamma'
  have hgcd : Nat.gcd m gamma.val = 1 := by
    rw [Nat.div_eq_self] at hgamma'
    exact hgamma'.resolve_left hm.ne'
  rw [← hval]
  apply (ZMod.isUnit_iff_coprime gamma.val m).2
  rw [Nat.coprime_comm, Nat.coprime_iff_gcd_eq_one]
  exact hgcd

/-- Order-theoretic form of rank-two color normalization. -/
theorem exists_unit_scaling_colorEmbed_eq_one_of_full_order {m q : ℕ}
    (hm : 0 < m) (hq : 0 < q) (hmq : m ∣ q) (gamma : ZMod m)
    (hgamma : addOrderOf gamma = m) :
    ∃ u : (ZMod q)ˣ,
      (u : ZMod q) * colorEmbed m q hmq gamma =
        colorEmbed m q hmq 1 :=
  exists_unit_scaling_colorEmbed_eq_one hq hmq gamma
    (isUnit_of_addOrderOf_eq_modulus hm gamma hgamma)

/-- The distinguished color `1` embeds as the residue `q / m`. -/
theorem colorEmbed_one_eq_div {m q : ℕ} (hmq : m ∣ q) :
    colorEmbed m q hmq 1 = (q / m : ZMod q) := by
  simpa using colorEmbed_intCast m q hmq (1 : ℤ)

/-- Supplying the eigenvalue-ratio embedding completes the cyclicity step for
the rank-two projective diagonal group.  Finiteness is supplied by the first
main theorem from single-site `Z` detection. -/
theorem CodeProjector.projectiveDiagonalGroup_isAddCyclic_of_ratioEmbedding
    {n : ℕ} (C : CodeProjector n 2) (hZ : C.DetectsSingleZ)
    (ratio : C.ProjectiveDiagonalGroup →+ UnitAddCircle)
    (hratio : Function.Injective ratio) :
    IsAddCyclic C.ProjectiveDiagonalGroup := by
  letI : Finite C.ProjectiveDiagonalGroup :=
    C.projectiveDiagonalGroup_finite
      (C.detectsNumberOps_of_detectsSingleZ hZ)
  exact isAddCyclic_of_finite_injective_unitAddCircle ratio hratio

/-- Eigenphases on two common logical eigenlines give the ratio embedding
used in the rank-two cyclicity proof. -/
theorem CodeProjector.projectiveDiagonalGroup_isAddCyclic_of_two_eigenphases
    {n : ℕ} (C : CodeProjector n 2) (hZ : C.DetectsSingleZ)
    (lambda0 lambda1 : C.ProjectiveDiagonalGroup →+ UnitAddCircle)
    (hfaithful : ∀ U, lambda1 U = lambda0 U → U = 0) :
    IsAddCyclic C.ProjectiveDiagonalGroup :=
  C.projectiveDiagonalGroup_isAddCyclic_of_ratioEmbedding hZ
    (eigenvalueRatio lambda0 lambda1)
    (eigenvalueRatio_injective lambda0 lambda1 hfaithful)

namespace CodeProjector

variable {n K q : ℕ} (C : CodeProjector n K)

/-- Every diagonal gate preserves every computational support subspace. -/
theorem diagonalGate_mulVec_mem_fiberSubspace
    (theta : PhaseVector n) (a : Fin n → ZMod q) (b : ZMod q)
    (psi : State n) (hpsi : psi ∈ fiberSubspace a b) :
    (diagonalGate theta).mulVec psi ∈ fiberSubspace a b := by
  intro x hx
  simp [diagonalGate, Matrix.mulVec, hpsi x hx]

/-- Restriction of a code-preserving diagonal gate to one fixed residue
sector of another diagonal action. -/
def phaseSectorMap (theta : PhaseVector n) (htheta : C.Preserves theta)
    (a : Fin n → ZMod q) (b : ZMod q) :
    C.phaseSector a b →ₗ[ℂ] C.phaseSector a b where
  toFun psi := ⟨(diagonalGate theta).mulVec psi.1, by
    rw [C.mem_phaseSector]
    have hmem := (C.mem_phaseSector (a := a) (b := b)).1 psi.2
    constructor
    · apply C.preserves_code_range theta htheta psi.1 hmem.1
    · exact diagonalGate_mulVec_mem_fiberSubspace theta a b psi.1 hmem.2⟩
  map_add' psi phi := by
    apply Subtype.ext
    simp [Matrix.mulVec_add]
  map_smul' c psi := by
    apply Subtype.ext
    simp [Matrix.mulVec_smul]

@[simp] theorem phaseSectorMap_apply_coe
    (theta : PhaseVector n) (htheta : C.Preserves theta)
    (a : Fin n → ZMod q) (b : ZMod q) (psi : C.phaseSector a b) :
    (C.phaseSectorMap theta htheta a b psi).1 =
      (diagonalGate theta).mulVec psi.1 :=
  rfl

/-- On a one-dimensional phase sector, evaluation at any nonzero coordinate
of a nonzero vector identifies the scalar by which a preserving diagonal gate
acts. -/
theorem phaseSectorMap_eq_supportPhase_smul_id
    (theta : PhaseVector n) (htheta : C.Preserves theta)
    (a : Fin n → ZMod q) (b : ZMod q)
    (hdim : Module.finrank ℂ (C.phaseSector a b) = 1)
    (psi0 : C.phaseSector a b) (x0 : BitString n)
    (hx0 : psi0.1 x0 ≠ 0) :
    C.phaseSectorMap theta htheta a b =
      ((((supportPhase theta x0).toCircle : Circle) : ℂ)) • LinearMap.id := by
  obtain ⟨c, hc, _⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim
      (C.phaseSectorMap theta htheta a b)
  have hcoordinate := congrArg
    (fun psi : C.phaseSector a b ↦ psi.1 x0)
    (LinearMap.congr_fun hc psi0)
  have hc_eq : c = (((supportPhase theta x0).toCircle : Circle) : ℂ) := by
    apply mul_right_cancel₀ hx0
    simpa [phaseSectorMap, diagonalGate, Matrix.mulVec] using hcoordinate.symm
  rw [hc, hc_eq]

/-- Coordinate evaluation of physical phases is an additive homomorphism. -/
def supportPhaseEvalHom (x : BitString n) : PhaseVector n →+ LocalPhase where
  toFun theta := supportPhase theta x
  map_zero' := supportPhase_zero x
  map_add' theta phi := supportPhase_add theta phi x

/-- The eigenvalue ratio at two computational coordinates, restricted to
code-preserving phases. -/
def preservingPhaseRatioHom (x0 x1 : BitString n) :
    C.preservingPhases →+ LocalPhase :=
  ((supportPhaseEvalHom x1).comp C.preservingPhases.subtype) -
    ((supportPhaseEvalHom x0).comp C.preservingPhases.subtype)

@[simp] theorem preservingPhaseRatioHom_apply (x0 x1 : BitString n)
    (theta : C.preservingPhases) :
    C.preservingPhaseRatioHom x0 x1 theta =
      supportPhase theta.1 x1 - supportPhase theta.1 x0 :=
  rfl

/-- A nonzero coordinate identifies a circle phase from its scalar action on
a state vector. -/
theorem supportPhase_eq_of_mulVec_eq_smul
    (theta : PhaseVector n) (psi : State n) (x : BitString n)
    (c : LocalPhase) (hx : psi x ≠ 0)
    (hact : (diagonalGate theta).mulVec psi =
      (((c.toCircle : Circle) : ℂ)) • psi) :
    supportPhase theta x = c := by
  have hcoordinate := congrFun hact x
  have hmul :
      (((supportPhase theta x).toCircle : Circle) : ℂ) * psi x =
        (((c.toCircle : Circle) : ℂ)) * psi x := by
    simpa [diagonalGate, Matrix.mulVec] using hcoordinate
  have hcomplex :
      (((supportPhase theta x).toCircle : Circle) : ℂ) =
        (((c.toCircle : Circle) : ℂ)) :=
    mul_right_cancel₀ hx hmul
  apply AddCircle.injective_toCircle one_ne_zero
  exact Subtype.coe_injective hcomplex

/-- The coordinate projectors onto all modular fibers resolve every code
vector into its phase-sector components. -/
theorem sum_phaseSectorComponent_coe [NeZero q] (hq : 0 < q)
    (a : Fin n → ZMod q) (hpres : C.Preserves (phaseHom n q hq a))
    (psi : C.CodeSpace) :
    ∑ b : ZMod q, (C.phaseSectorComponent hq a hpres b psi).1 = psi.1 := by
  funext x
  simp only [Finset.sum_apply, phaseSectorComponent_apply_coe,
    fiberProjector_mulVec_apply]
  rw [Finset.sum_eq_single (subsetSum a x)]
  · simp
  · intro b _ hb
    rw [if_neg]
    exact fun h => hb h.symm
  · simp

/-- The number of active residues cannot exceed the code dimension. -/
theorem card_activeResidue_le [NeZero q] (hq : 0 < q)
    (a : Fin n → ZMod q) (hpres : C.Preserves (phaseHom n q hq a)) :
    Fintype.card (C.ActiveResidue a) ≤ K := by
  classical
  calc
    Fintype.card (C.ActiveResidue a) =
        ∑ _b : C.ActiveResidue a, 1 := by simp
    _ ≤ ∑ b : C.ActiveResidue a,
        Module.finrank ℂ (C.phaseSector a b.1) := by
      apply Finset.sum_le_sum
      intro b _
      exact C.activeResidue_finrank_pos a b
    _ = K := C.sum_finrank_activeResidue hq a hpres

/-- On a rank-two code, a nontrivial modular projective action has exactly two
active residue sectors. -/
theorem card_activeResidue_eq_two_of_projectiveClass_ne_zero
    {n q : ℕ} [NeZero q] (C : CodeProjector n 2) (hq : 0 < q)
    (a : Fin n → ZMod q) (hpres : C.Preserves (phaseHom n q hq a))
    (hne : C.projectiveClassMap ⟨phaseHom n q hq a, hpres⟩ ≠ 0) :
    Fintype.card (C.ActiveResidue a) = 2 := by
  classical
  have hle : Fintype.card (C.ActiveResidue a) ≤ 2 :=
    C.card_activeResidue_le hq a hpres
  have hsum :
      ∑ b : C.ActiveResidue a, Module.finrank ℂ (C.phaseSector a b.1) = 2 :=
    C.sum_finrank_activeResidue hq a hpres
  have hcard_ne_zero : Fintype.card (C.ActiveResidue a) ≠ 0 := by
    intro hcard
    letI : IsEmpty (C.ActiveResidue a) := Fintype.card_eq_zero_iff.mp hcard
    have hemptySum :
        (∑ b : C.ActiveResidue a,
          Module.finrank ℂ (C.phaseSector a b.1)) = 0 := by simp
    omega
  have hpos : 0 < Fintype.card (C.ActiveResidue a) :=
    Nat.pos_of_ne_zero hcard_ne_zero
  obtain ⟨b0⟩ := (Fintype.card_pos_iff.mp hpos)
  have hcard_ne_one : Fintype.card (C.ActiveResidue a) ≠ 1 := by
    intro hcard
    have huniq : ∀ b : C.ActiveResidue a, b = b0 :=
      fun b => Fintype.card_le_one_iff.mp hcard.le b b0
    apply hne
    have hrel : (1 : ℕ) • C.relativeResidues a b0 = 0 := by
      funext b
      rw [huniq b]
      simp
    simpa using
      (C.nsmul_projectiveClass_eq_zero_iff hq a hpres b0 1).2 hrel
  omega

/-- Consequently, each active sector of a nontrivial modular action on a
rank-two code is one-dimensional. -/
theorem finrank_phaseSector_eq_one_of_rank_two_projectiveClass_ne_zero
    {n q : ℕ} [NeZero q] (C : CodeProjector n 2) (hq : 0 < q)
    (a : Fin n → ZMod q) (hpres : C.Preserves (phaseHom n q hq a))
    (hne : C.projectiveClassMap ⟨phaseHom n q hq a, hpres⟩ ≠ 0)
    (b : C.ActiveResidue a) :
    Module.finrank ℂ (C.phaseSector a b.1) = 1 := by
  classical
  have hcard := C.card_activeResidue_eq_two_of_projectiveClass_ne_zero
    hq a hpres hne
  have hsum := C.sum_finrank_activeResidue hq a hpres
  have hunivcard : (Finset.univ : Finset (C.ActiveResidue a)).card = 2 := by
    simpa using hcard
  obtain ⟨b0, b1, hb01, huniv⟩ := Finset.card_eq_two.mp hunivcard
  have hsum_pair :
      Module.finrank ℂ (C.phaseSector a b0.1) +
        Module.finrank ℂ (C.phaseSector a b1.1) = 2 := by
    simpa [huniv, hb01] using hsum
  have hb0pos := C.activeResidue_finrank_pos a b0
  have hb1pos := C.activeResidue_finrank_pos a b1
  have hb0one : Module.finrank ℂ (C.phaseSector a b0.1) = 1 := by omega
  have hb1one : Module.finrank ℂ (C.phaseSector a b1.1) = 1 := by omega
  have hbmem : b ∈ ({b0, b1} : Finset (C.ActiveResidue a)) := by
    rw [← huniv]
    exact Finset.mem_univ b
  rcases Finset.mem_insert.mp hbmem with hb | hb
  · subst b
    exact hb0one
  · have hb' : b = b1 := Finset.mem_singleton.mp hb
    subst b
    exact hb1one

/-- A two-element active-residue type can be enumerated by two distinct
residues. -/
theorem exists_activeResidue_pair_of_card_eq_two [NeZero q]
    (a : Fin n → ZMod q)
    (hcard : Fintype.card (C.ActiveResidue a) = 2) :
    ∃ b0 b1 : C.ActiveResidue a,
      b0 ≠ b1 ∧ ∀ b : C.ActiveResidue a, b = b0 ∨ b = b1 := by
  classical
  have hunivcard : (Finset.univ : Finset (C.ActiveResidue a)).card = 2 := by
    simpa using hcard
  obtain ⟨b0, b1, hb01, huniv⟩ := Finset.card_eq_two.mp hunivcard
  refine ⟨b0, b1, hb01, ?_⟩
  intro b
  have hb : b ∈ ({b0, b1} : Finset (C.ActiveResidue a)) := by
    rw [← huniv]
    exact Finset.mem_univ b
  simpa using hb

/-- Two exhaustive one-dimensional sectors of one diagonal logical action
define a faithful eigenvalue-ratio character on the entire projective
diagonal group.  Every preserving diagonal gate leaves the two sectors
invariant because physical diagonal gates commute. -/
theorem exists_injective_projectivePhaseRatio_of_two_sectors
    [NeZero q] (hq : 0 < q) (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a))
    (b0 b1 : C.ActiveResidue a)
    (hexhaust : ∀ b : C.ActiveResidue a, b = b0 ∨ b = b1)
    (hdim0 : Module.finrank ℂ (C.phaseSector a b0.1) = 1)
    (hdim1 : Module.finrank ℂ (C.phaseSector a b1.1) = 1) :
    ∃ ratio : C.ProjectiveDiagonalGroup →+ UnitAddCircle,
      Function.Injective ratio := by
  classical
  obtain ⟨psi0, hpsi0mem, hpsi0ne⟩ :=
    (Submodule.ne_bot_iff (C.phaseSector a b0.1)).1 b0.2
  obtain ⟨psi1, hpsi1mem, hpsi1ne⟩ :=
    (Submodule.ne_bot_iff (C.phaseSector a b1.1)).1 b1.2
  have hexistsCoordinate (psi : State n) (hpsi : psi ≠ 0) :
      ∃ x : BitString n, psi x ≠ 0 := by
    by_contra h
    push_neg at h
    apply hpsi
    funext x
    exact h x
  obtain ⟨x0, hx0⟩ := hexistsCoordinate psi0 hpsi0ne
  obtain ⟨x1, hx1⟩ := hexistsCoordinate psi1 hpsi1ne
  let v0 : C.phaseSector a b0.1 := ⟨psi0, hpsi0mem⟩
  let v1 : C.phaseSector a b1.1 := ⟨psi1, hpsi1mem⟩
  let ratioPres : C.preservingPhases →+ UnitAddCircle :=
    C.preservingPhaseRatioHom x0 x1
  have hscalar_le : C.scalarPhases ≤ ratioPres.ker := by
    intro theta htheta
    change ratioPres theta = 0
    obtain ⟨c, hc⟩ := C.actsAsScalar_on_code theta.1 htheta
    have hcode0 : C.proj.mulVec psi0 = psi0 :=
      (C.mem_codeSpace_iff psi0).1 hpsi0mem.1
    have hcode1 : C.proj.mulVec psi1 = psi1 :=
      (C.mem_codeSpace_iff psi1).1 hpsi1mem.1
    have hphase0 : supportPhase theta.1 x0 = c :=
      supportPhase_eq_of_mulVec_eq_smul theta.1 psi0 x0 c hx0
        (hc psi0 hcode0)
    have hphase1 : supportPhase theta.1 x1 = c :=
      supportPhase_eq_of_mulVec_eq_smul theta.1 psi1 x1 c hx1
        (hc psi1 hcode1)
    change supportPhase theta.1 x1 - supportPhase theta.1 x0 = 0
    rw [hphase0, hphase1, sub_self]
  let ratio : C.ProjectiveDiagonalGroup →+ UnitAddCircle :=
    QuotientAddGroup.lift C.scalarPhases ratioPres hscalar_le
  have hkernel (theta : C.preservingPhases)
      (htheta : ratioPres theta = 0) : C.ActsAsScalar theta.1 := by
    have hphase : supportPhase theta.1 x1 = supportPhase theta.1 x0 := by
      apply sub_eq_zero.mp
      exact htheta
    apply (C.actsAsScalar_iff_action_on_code theta.1).2
    refine ⟨supportPhase theta.1 x0, ?_⟩
    intro psi hpsi
    let psiCode : C.CodeSpace :=
      ⟨psi, (C.mem_codeSpace_iff psi).2 hpsi⟩
    have hcomponent (b : ZMod q) :
        (diagonalGate theta.1).mulVec
            (C.phaseSectorComponent hq a hpres b psiCode).1 =
          ((((supportPhase theta.1 x0).toCircle : Circle) : ℂ)) •
            (C.phaseSectorComponent hq a hpres b psiCode).1 := by
      by_cases hb : C.phaseSector a b = ⊥
      · have hzero : C.phaseSectorComponent hq a hpres b psiCode = 0 := by
          apply Subtype.ext
          simpa [hb] using
            (C.phaseSectorComponent hq a hpres b psiCode).2
        rw [hzero]
        simp
      · let active : C.ActiveResidue a := ⟨b, hb⟩
        rcases hexhaust active with hactive | hactive
        · have hb0 : b = b0.1 := congrArg Subtype.val hactive
          subst b
          have hmap := C.phaseSectorMap_eq_supportPhase_smul_id
            theta.1 theta.2 a b0.1 hdim0 v0 x0 hx0
          have happ := LinearMap.congr_fun hmap
            (C.phaseSectorComponent hq a hpres b0.1 psiCode)
          exact congrArg Subtype.val happ
        · have hb1 : b = b1.1 := congrArg Subtype.val hactive
          subst b
          have hmap := C.phaseSectorMap_eq_supportPhase_smul_id
            theta.1 theta.2 a b1.1 hdim1 v1 x1 hx1
          have happ := congrArg Subtype.val (LinearMap.congr_fun hmap
            (C.phaseSectorComponent hq a hpres b1.1 psiCode))
          simpa [hphase] using happ
    have hsum := C.sum_phaseSectorComponent_coe hq a hpres psiCode
    calc
      (diagonalGate theta.1).mulVec psi =
          (diagonalGate theta.1).mulVec
            (∑ b : ZMod q,
              (C.phaseSectorComponent hq a hpres b psiCode).1) := by
            rw [hsum]
      _ = ∑ b : ZMod q, (diagonalGate theta.1).mulVec
            (C.phaseSectorComponent hq a hpres b psiCode).1 := by
            simpa only [Matrix.mulVecLin_apply] using
              (map_sum (diagonalGate theta.1).mulVecLin
                (fun b : ZMod q ↦
                  (C.phaseSectorComponent hq a hpres b psiCode).1)
                Finset.univ)
      _ = ∑ b : ZMod q,
            ((((supportPhase theta.1 x0).toCircle : Circle) : ℂ)) •
              (C.phaseSectorComponent hq a hpres b psiCode).1 := by
            apply Finset.sum_congr rfl
            intro b _
            exact hcomponent b
      _ = ((((supportPhase theta.1 x0).toCircle : Circle) : ℂ)) •
            (∑ b : ZMod q,
              (C.phaseSectorComponent hq a hpres b psiCode).1) := by
            rw [Finset.smul_sum]
      _ = ((((supportPhase theta.1 x0).toCircle : Circle) : ℂ)) • psi := by
            rw [hsum]
  refine ⟨ratio, ?_⟩
  intro U V hUV
  apply sub_eq_zero.mp
  let W := U - V
  have hratioW : ratio W = 0 := by
    dsimp [W]
    rw [map_sub, hUV, sub_self]
  obtain ⟨theta, htheta⟩ :=
    (QuotientAddGroup.mk'_surjective C.scalarPhases) W
  have hratioPres : ratioPres theta = 0 := by
    have h := hratioW
    rw [← htheta] at h
    simpa [ratio] using h
  have hthetaScalar : theta ∈ C.scalarPhases := hkernel theta hratioPres
  have hWzero : W = 0 := by
    rw [← htheta]
    exact (QuotientAddGroup.eq_zero_iff theta).2 hthetaScalar
  exact hWzero

/-- Any single nontrivial modular diagonal action on a rank-two code supplies
the two one-dimensional sectors needed to construct a faithful character of
the full projective diagonal group. -/
theorem exists_injective_projectivePhaseRatio_of_rankTwo_nontrivial
    {n q : ℕ} [NeZero q] (C : CodeProjector n 2) (hq : 0 < q)
    (a : Fin n → ZMod q) (hpres : C.Preserves (phaseHom n q hq a))
    (hne : C.projectiveClassMap ⟨phaseHom n q hq a, hpres⟩ ≠ 0) :
    ∃ ratio : C.ProjectiveDiagonalGroup →+ UnitAddCircle,
      Function.Injective ratio := by
  have hcard := C.card_activeResidue_eq_two_of_projectiveClass_ne_zero
    hq a hpres hne
  obtain ⟨b0, b1, _, hexhaust⟩ :=
    C.exists_activeResidue_pair_of_card_eq_two a hcard
  have hdim0 :=
    C.finrank_phaseSector_eq_one_of_rank_two_projectiveClass_ne_zero
      hq a hpres hne b0
  have hdim1 :=
    C.finrank_phaseSector_eq_one_of_rank_two_projectiveClass_ne_zero
      hq a hpres hne b1
  exact C.exists_injective_projectivePhaseRatio_of_two_sectors
    hq a hpres b0 b1 hexhaust hdim0 hdim1

/-- **Cyclicity of the nontrivial rank-two projective diagonal group.**

Single-site `Z` detection makes the group finite and supplies a finite-order
modular representative of any nonzero class.  Its two one-dimensional phase
sectors define a faithful eigenvalue-ratio character into `U(1)`, so the
whole projective group is cyclic. -/
theorem projectiveDiagonalGroup_isAddCyclic_of_rankTwo
    {n : ℕ} (C : CodeProjector n 2) (hZ : C.DetectsSingleZ)
    (U : C.ProjectiveDiagonalGroup) (hU : U ≠ 0) :
    IsAddCyclic C.ProjectiveDiagonalGroup := by
  have hdetect := C.detectsNumberOps_of_detectsSingleZ hZ
  obtain ⟨R, hpres, hclass, _, _, _⟩ :=
    C.exists_reduced_representative hdetect U hU
  have hq : 0 < R.q :=
    lt_of_lt_of_le Nat.zero_lt_two R.q_ge_two
  letI : NeZero R.q := ⟨hq.ne'⟩
  have hrepresentativeNonzero :
      C.projectiveClassMap ⟨phaseHom n R.q hq R.a, hpres⟩ ≠ 0 := by
    change C.projectiveClassMap ⟨R.phase, hpres⟩ ≠ 0
    rw [hclass]
    exact hU
  obtain ⟨ratio, hratio⟩ :=
    C.exists_injective_projectivePhaseRatio_of_rankTwo_nontrivial
      hq R.a hpres hrepresentativeNonzero
  letI : Finite C.ProjectiveDiagonalGroup :=
    C.projectiveDiagonalGroup_finite hdetect
  exact isAddCyclic_of_finite_injective_unitAddCircle ratio hratio

/-- If two active residues exhaust the active sectors, the relative-residue
vector has the same additive order as their single difference. -/
theorem addOrderOf_relativeResidues_eq_difference [NeZero q]
    (a : Fin n → ZMod q) (b0 b1 : C.ActiveResidue a)
    (hexhaust : ∀ b : C.ActiveResidue a, b = b0 ∨ b = b1) :
    addOrderOf (C.relativeResidues a b0) =
      addOrderOf (b1.1 - b0.1) := by
  have hann (k : ℕ) :
      k • C.relativeResidues a b0 = 0 ↔ k • (b1.1 - b0.1) = 0 := by
    constructor
    · intro h
      have := congrFun h b1
      simpa [relativeResidues] using this
    · intro h
      funext b
      rcases hexhaust b with rfl | rfl
      · simp [relativeResidues]
      · simpa [relativeResidues] using h
  apply Nat.dvd_antisymm
  · rw [addOrderOf_dvd_iff_nsmul_eq_zero]
    exact (hann _).2 (addOrderOf_nsmul_eq_zero _)
  · rw [addOrderOf_dvd_iff_nsmul_eq_zero]
    exact (hann _).1 (addOrderOf_nsmul_eq_zero _)

/-- Complete rank-two sector conclusion for one nontrivial modular logical
action: there are two one-dimensional sectors, and after replacing the
physical generator by a unit power their relative residue is `q / m`. -/
theorem exists_normalized_rankTwo_activeResidues
    {n q m : ℕ} [NeZero q] (C : CodeProjector n 2) (hq : 0 < q)
    (a : Fin n → ZMod q) (hpres : C.Preserves (phaseHom n q hq a))
    (hne : C.projectiveClassMap ⟨phaseHom n q hq a, hpres⟩ ≠ 0)
    (hm : 2 ≤ m) (hmq : m ∣ q)
    (horder : addOrderOf
      (C.projectiveClassMap ⟨phaseHom n q hq a, hpres⟩) = m) :
    ∃ b0 b1 : C.ActiveResidue a, ∃ u : (ZMod q)ˣ,
      b0 ≠ b1 ∧
      (∀ b : C.ActiveResidue a, b = b0 ∨ b = b1) ∧
      Module.finrank ℂ (C.phaseSector a b0.1) = 1 ∧
      Module.finrank ℂ (C.phaseSector a b1.1) = 1 ∧
      (u : ZMod q) * (b1.1 - b0.1) = (q / m : ZMod q) := by
  have hcard := C.card_activeResidue_eq_two_of_projectiveClass_ne_zero
    hq a hpres hne
  obtain ⟨b0, b1, hb01, hexhaust⟩ :=
    C.exists_activeResidue_pair_of_card_eq_two a hcard
  have hb0dim :=
    C.finrank_phaseSector_eq_one_of_rank_two_projectiveClass_ne_zero
      hq a hpres hne b0
  have hb1dim :=
    C.finrank_phaseSector_eq_one_of_rank_two_projectiveClass_ne_zero
      hq a hpres hne b1
  have hrelative := C.projectiveOrder_eq_relativeResiduesOrder
    hq a hpres b0
  have hdiff := C.addOrderOf_relativeResidues_eq_difference
    a b0 b1 hexhaust
  have hdiffOrder : addOrderOf (b1.1 - b0.1) = m := by
    rw [← hdiff, ← hrelative, horder]
  have hdiffKilled : m • (b1.1 - b0.1) = 0 := by
    rw [← hdiffOrder]
    exact addOrderOf_nsmul_eq_zero _
  obtain ⟨gamma, hgamma, _⟩ :=
    existsUnique_color_of_nsmul_eq_zero m q hm hq hmq
      (b1.1 - b0.1) hdiffKilled
  have hgammaOrder : addOrderOf gamma = m := by
    have hembedOrder := addOrderOf_injective (colorEmbed m q hmq)
      (colorEmbed_injective m q hm hq hmq) gamma
    calc
      addOrderOf gamma = addOrderOf (colorEmbed m q hmq gamma) :=
        hembedOrder.symm
      _ = addOrderOf (b1.1 - b0.1) := by rw [hgamma]
      _ = m := hdiffOrder
  obtain ⟨u, hu⟩ := exists_unit_scaling_colorEmbed_eq_one_of_full_order
    (Nat.zero_lt_of_lt hm) hq hmq gamma hgammaOrder
  refine ⟨b0, b1, u, hb01, hexhaust, hb0dim, hb1dim, ?_⟩
  rw [← hgamma, hu, colorEmbed_one_eq_div]

/-- The full data asserted by the rank-two SSLP corollary, kept in `Prop` so
dependent witnesses such as the representative, its preservation proof, and
its active sectors can be chosen together. -/
def HasRankTwoSSLPNormalForm {n : ℕ} (C : CodeProjector n 2) : Prop :=
  IsAddCyclic C.ProjectiveDiagonalGroup ∧
    ∃ U : C.ProjectiveDiagonalGroup,
      U ≠ 0 ∧
      (∀ V : C.ProjectiveDiagonalGroup,
        V ∈ AddSubgroup.zmultiples U) ∧
      ∃ (m : ℕ) (R : ReducedDiagonalRepresentative n)
        (hpres : C.Preserves R.phase),
        m = addOrderOf U ∧
        C.projectiveClassMap ⟨R.phase, hpres⟩ = U ∧
        R.commonGCD = 1 ∧
        orderOf (diagonalGate R.phase) = R.q ∧
        2 ≤ m ∧ m ∣ R.q ∧
        ∃ b0 b1 : C.ActiveResidue R.a, ∃ u : (ZMod R.q)ˣ,
          b0 ≠ b1 ∧
          (∀ b : C.ActiveResidue R.a, b = b0 ∨ b = b1) ∧
          Module.finrank ℂ (C.phaseSector R.a b0.1) = 1 ∧
          Module.finrank ℂ (C.phaseSector R.a b1.1) = 1 ∧
          (u : ZMod R.q) * (b1.1 - b0.1) =
            (R.q / m : ZMod R.q)

/-- **Rank-two SSLP normal form.**

For a distance-at-least-two rank-two code with a nonzero projective diagonal
class, the entire projective diagonal group is cyclic.  A nonzero generator
has a reduced representative of physical order `q`, its logical order `m`
divides `q`, and its two exhaustive one-dimensional sectors can be normalized
by a unit power so that their relative residue is `q / m`. -/
theorem rankTwo_sslp_normal_form
    {n d : ℕ} (C : CodeProjector n 2)
    (hd : C.HasDistanceAtLeast d) (hd2 : 2 ≤ d)
    (U0 : C.ProjectiveDiagonalGroup) (hU0 : U0 ≠ 0) :
    C.HasRankTwoSSLPNormalForm := by
  have hdTwo : C.HasDistanceAtLeast 2 := by
    intro p hp
    exact hd p (lt_of_lt_of_le hp hd2)
  have hZ : C.DetectsSingleZ :=
    C.detectsSingleZ_of_hasDistanceAtLeast_two hdTwo
  have hdetect : C.DetectsNumberOps :=
    C.detectsNumberOps_of_detectsSingleZ hZ
  have hcyclic : IsAddCyclic C.ProjectiveDiagonalGroup :=
    C.projectiveDiagonalGroup_isAddCyclic_of_rankTwo hZ U0 hU0
  letI : IsAddCyclic C.ProjectiveDiagonalGroup := hcyclic
  letI : Finite C.ProjectiveDiagonalGroup :=
    C.projectiveDiagonalGroup_finite hdetect
  obtain ⟨U, hgenerate⟩ :
      ∃ U : C.ProjectiveDiagonalGroup,
        Function.Surjective (fun k : ℤ ↦ k • U) :=
    IsAddCyclic.exists_zsmul_surjective
  have hU : U ≠ 0 := by
    intro hzero
    obtain ⟨k, hk⟩ := hgenerate U0
    apply hU0
    simpa [hzero] using hk.symm
  have hgenerates (V : C.ProjectiveDiagonalGroup) :
      V ∈ AddSubgroup.zmultiples U :=
    AddSubgroup.mem_zmultiples_iff.2 (hgenerate V)
  let m := addOrderOf U
  have hmpos : 0 < m := addOrderOf_pos U
  have hmne : m ≠ 1 := by
    intro hm
    apply hU
    exact AddMonoid.addOrderOf_eq_one_iff.mp hm
  have hm : 2 ≤ m := by omega
  obtain ⟨R, hpres, hclass, hgcd, hphysical, hdvd⟩ :=
    C.exists_reduced_representative hdetect U hU
  have hq : 0 < R.q :=
    lt_of_lt_of_le Nat.zero_lt_two R.q_ge_two
  letI : NeZero R.q := ⟨hq.ne'⟩
  have hrepresentativeNonzero :
      C.projectiveClassMap ⟨phaseHom n R.q hq R.a, hpres⟩ ≠ 0 := by
    change C.projectiveClassMap ⟨R.phase, hpres⟩ ≠ 0
    rw [hclass]
    exact hU
  have hrepresentativeOrder :
      addOrderOf
        (C.projectiveClassMap ⟨phaseHom n R.q hq R.a, hpres⟩) = m := by
    change addOrderOf (C.projectiveClassMap ⟨R.phase, hpres⟩) = m
    rw [hclass]
  obtain ⟨b0, b1, u, hb01, hexhaust, hdim0, hdim1, hnormalized⟩ :=
    C.exists_normalized_rankTwo_activeResidues hq R.a hpres
      hrepresentativeNonzero hm hdvd hrepresentativeOrder
  refine ⟨hcyclic, U, hU, hgenerates, m, R, hpres, rfl,
    hclass, hgcd, hphysical, hm, hdvd, b0, b1, u, hb01,
    hexhaust, hdim0, hdim1, ?_⟩
  exact hnormalized

end CodeProjector

end

end QECC
