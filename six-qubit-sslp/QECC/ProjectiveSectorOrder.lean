import QECC.SectorDecomposition

namespace QECC

open scoped BigOperators

noncomputable section

@[simp] theorem subsetSum_nsmul {n q : ℕ} (k : ℕ)
    (a : Fin n → ZMod q) (x : BitString n) :
    subsetSum (k • a) x = k • subsetSum a x := by
  simp only [subsetSum, Pi.smul_apply]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  cases x j <;> simp

/-- The complex phase attached to a residue remembers that residue. -/
theorem zmodPhaseScalar_injective (q : ℕ) (hq : 0 < q) :
    Function.Injective (zmodPhaseScalar q hq) := by
  letI : NeZero q := ⟨hq.ne'⟩
  intro b c hbc
  apply ZMod.toAddCircle_injective q
  apply AddCircle.injective_toCircle one_ne_zero
  apply Circle.coe_injective
  exact hbc

/-- Scaling the residue vector and the fiber label scales the eigenvalue on
that fiber by the same amount. -/
theorem diagonalGate_nsmul_phaseHom_mulVec_of_mem_fiberSubspace
    {n q : ℕ} (hq : 0 < q) (k : ℕ) (a : Fin n → ZMod q)
    (b : ZMod q) (psi : State n) (hpsi : psi ∈ fiberSubspace a b) :
    (diagonalGate (k • phaseHom n q hq a)).mulVec psi =
      zmodPhaseScalar q hq (k • b) • psi := by
  have hphase : k • phaseHom n q hq a = phaseHom n q hq (k • a) := by
    exact (map_nsmul (phaseHom n q hq) k a).symm
  rw [hphase]
  apply diagonalGate_phaseHom_mulVec_of_mem_fiberSubspace hq (k • a) (k • b)
  intro x hx
  apply hpsi x
  intro hxb
  apply hx
  rw [subsetSum_nsmul, hxb]

namespace CodeProjector

variable {n K q : ℕ} (C : CodeProjector n K)

/-- A diagonal phase is projectively scalar exactly when it acts by one
common scalar on every code vector.  The reverse implication is useful when
the code has first been decomposed into invariant phase sectors. -/
theorem actsAsScalar_iff_action_on_code (theta : PhaseVector n) :
    C.ActsAsScalar theta ↔
      ∃ c : LocalPhase, ∀ psi : State n, C.proj.mulVec psi = psi →
        (diagonalGate theta).mulVec psi =
          (((c.toCircle : Circle) : ℂ)) • psi := by
  constructor
  · exact C.actsAsScalar_on_code theta
  · rintro ⟨c, hc⟩
    apply (C.actsAsScalar_iff_gate_mul_proj theta).2
    refine ⟨c, ?_⟩
    classical
    ext x y
    let e : State n := computationalBasisState y
    have hfixed : C.proj.mulVec (C.proj.mulVec e) = C.proj.mulVec e := by
      rw [Matrix.mulVec_mulVec, C.idempotent]
    have haction := congrFun (hc (C.proj.mulVec e) hfixed) x
    have heval (A : Operator n) : A.mulVec e x = A x y := by
      simp [Matrix.mulVec, dotProduct, e, computationalBasisState]
    rw [Matrix.mulVec_mulVec, heval, Pi.smul_apply, heval] at haction
    simpa using haction

/-- Every nonzero projector entry supplies an active modular phase sector. -/
def activeResidueOfProjNe (hq : 0 < q) (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a)) {x y : BitString n}
    (hxy : C.proj x y ≠ 0) : C.ActiveResidue a := by
  refine ⟨subsetSum a x, (Submodule.ne_bot_iff _).2 ?_⟩
  let psi : State n := C.proj.col y
  refine ⟨psi, ?_, ?_⟩
  · rw [C.mem_phaseSector]
    constructor
    · funext z
      have hidem := congrFun (congrFun C.idempotent z) y
      simpa [psi, Matrix.mulVec, Matrix.mul_apply] using hidem
    · intro z hz
      by_contra hzy
      have hsumzy := C.subsetSum_eq_of_proj_ne hq a hpres hzy
      have hsumxy := C.subsetSum_eq_of_proj_ne hq a hpres hxy
      exact hz (hsumzy.trans hsumxy.symm)
  · intro hzero
    apply hxy
    have hxzero := congrFun hzero x
    simpa [psi] using hxzero

@[simp] theorem activeResidueOfProjNe_value (hq : 0 < q)
    (a : Fin n → ZMod q) (hpres : C.Preserves (phaseHom n q hq a))
    {x y : BitString n} (hxy : C.proj x y ≠ 0) :
    (C.activeResidueOfProjNe hq a hpres hxy).1 = subsetSum a x := rfl

/-- Residues measured relative to a chosen active sector.  These are exactly
the projectively meaningful logical phase labels before changing modulus. -/
def relativeResidues (a : Fin n → ZMod q) (b0 : C.ActiveResidue a) :
    C.ActiveResidue a → ZMod q :=
  fun b => b.1 - b0.1

@[simp] theorem relativeResidues_anchor (a : Fin n → ZMod q)
    (b0 : C.ActiveResidue a) :
    C.relativeResidues a b0 b0 = 0 := by
  simp [relativeResidues]

/-- A multiple of the modular phase acts projectively as a scalar precisely
when it annihilates every active residue relative to one anchor sector. -/
theorem actsAsScalar_nsmul_phaseHom_iff (hq : 0 < q)
    (a : Fin n → ZMod q) (hpres : C.Preserves (phaseHom n q hq a))
    (b0 : C.ActiveResidue a) (k : ℕ) :
    C.ActsAsScalar (k • phaseHom n q hq a) ↔
      k • C.relativeResidues a b0 = 0 := by
  letI : NeZero q := ⟨hq.ne'⟩
  constructor
  · intro hscalar
    obtain ⟨c, hc⟩ := C.actsAsScalar_on_code _ hscalar
    funext b
    obtain ⟨psi, hpsi, hpsi_ne⟩ :=
      (Submodule.ne_bot_iff (C.phaseSector a b.1)).1 b.2
    obtain ⟨psi0, hpsi0, hpsi0_ne⟩ :=
      (Submodule.ne_bot_iff (C.phaseSector a b0.1)).1 b0.2
    have hact := diagonalGate_nsmul_phaseHom_mulVec_of_mem_fiberSubspace
      hq k a b.1 psi hpsi.2
    have hact0 := diagonalGate_nsmul_phaseHom_mulVec_of_mem_fiberSubspace
      hq k a b0.1 psi0 hpsi0.2
    have hcode := (C.mem_codeSpace_iff psi).1 hpsi.1
    have hcode0 := (C.mem_codeSpace_iff psi0).1 hpsi0.1
    have heig : zmodPhaseScalar q hq (k • b.1) =
        (((c.toCircle : Circle) : ℂ)) := by
      apply smul_left_injective ℂ hpsi_ne
      exact hact.symm.trans (hc psi hcode)
    have heig0 : zmodPhaseScalar q hq (k • b0.1) =
        (((c.toCircle : Circle) : ℂ)) := by
      apply smul_left_injective ℂ hpsi0_ne
      exact hact0.symm.trans (hc psi0 hcode0)
    have hb : k • b.1 = k • b0.1 :=
      zmodPhaseScalar_injective q hq (heig.trans heig0.symm)
    change k • (b.1 - b0.1) = 0
    rw [nsmul_sub, hb, sub_self]
  · intro hrel
    refine ⟨zmodPhase q hq (k • b0.1), ?_⟩
    intro x y hxy
    let bx : C.ActiveResidue a := C.activeResidueOfProjNe hq a hpres hxy
    have hbx := congrFun hrel bx
    change k • (bx.1 - b0.1) = 0 at hbx
    rw [nsmul_sub] at hbx
    have heq : k • bx.1 = k • b0.1 := sub_eq_zero.mp hbx
    have hphase : k • phaseHom n q hq a = phaseHom n q hq (k • a) := by
      exact (map_nsmul (phaseHom n q hq) k a).symm
    rw [hphase, supportPhase_phaseHom, subsetSum_nsmul]
    change zmodPhase q hq (k • subsetSum a x) = _
    rw [← C.activeResidueOfProjNe_value hq a hpres hxy, heq]

/-- The annihilator of a projective modular action is the annihilator of its
vector of relative active residues. -/
theorem nsmul_projectiveClass_eq_zero_iff (hq : 0 < q)
    (a : Fin n → ZMod q) (hpres : C.Preserves (phaseHom n q hq a))
    (b0 : C.ActiveResidue a) (k : ℕ) :
    k • C.projectiveClassMap ⟨phaseHom n q hq a, hpres⟩ = 0 ↔
      k • C.relativeResidues a b0 = 0 := by
  rw [← map_nsmul]
  change ((↑(k • (⟨phaseHom n q hq a, hpres⟩ : C.preservingPhases)) :
      C.ProjectiveDiagonalGroup) = 0) ↔ _
  rw [QuotientAddGroup.eq_zero_iff]
  change C.ActsAsScalar (k • phaseHom n q hq a) ↔ _
  exact C.actsAsScalar_nsmul_phaseHom_iff hq a hpres b0 k

/-- The projective order of a modular diagonal action is the additive order
of its active residue differences. -/
theorem projectiveOrder_eq_relativeResiduesOrder (hq : 0 < q)
    (a : Fin n → ZMod q) (hpres : C.Preserves (phaseHom n q hq a))
    (b0 : C.ActiveResidue a) :
    addOrderOf (C.projectiveClassMap ⟨phaseHom n q hq a, hpres⟩) =
      addOrderOf (C.relativeResidues a b0) := by
  apply Nat.dvd_antisymm
  · rw [addOrderOf_dvd_iff_nsmul_eq_zero]
    apply (C.nsmul_projectiveClass_eq_zero_iff hq a hpres b0 _).2
    exact addOrderOf_nsmul_eq_zero _
  · rw [addOrderOf_dvd_iff_nsmul_eq_zero]
    apply (C.nsmul_projectiveClass_eq_zero_iff hq a hpres b0 _).1
    exact addOrderOf_nsmul_eq_zero _

end CodeProjector

end

end QECC
