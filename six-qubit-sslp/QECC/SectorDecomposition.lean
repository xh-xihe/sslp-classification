import QECC.SubsetSum

namespace QECC

open scoped BigOperators

noncomputable section

namespace CodeProjector

variable {n K q : ℕ} (C : CodeProjector n K)

/-- Preservation by a modular diagonal gate forces every nonzero projector
entry to join basis strings with the same modular subset sum. -/
theorem subsetSum_eq_of_proj_ne (hq : 0 < q) (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a)) {x y : BitString n}
    (hxy : C.proj x y ≠ 0) :
    subsetSum a x = subsetSum a y := by
  letI : NeZero q := ⟨hq.ne'⟩
  have hp := hpres x y hxy
  rw [supportPhase_phaseHom hq a x, supportPhase_phaseHom hq a y] at hp
  apply ZMod.toAddCircle_injective q
  simpa [zmodPhase] using hp

/-- The code projector commutes with every coordinate projector onto a
subset-sum fiber of a preserving modular phase. -/
theorem commutes_fiberProjector (hq : 0 < q) (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a)) (b : ZMod q) :
    C.proj * fiberProjector a b = fiberProjector a b * C.proj := by
  classical
  ext x y
  by_cases hxy : C.proj x y = 0
  · simp [fiberProjector, hxy]
  · have heq := C.subsetSum_eq_of_proj_ne hq a hpres hxy
    simp only [fiberProjector, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rw [heq]
    exact mul_comm _ _

/-- The part of the code supported in one modular subset-sum fiber. -/
def phaseSector (a : Fin n → ZMod q) (b : ZMod q) :
    Submodule ℂ (State n) :=
  C.CodeSpace ⊓ fiberSubspace a b

@[simp] theorem mem_phaseSector {a : Fin n → ZMod q} {b : ZMod q}
    {psi : State n} :
    psi ∈ C.phaseSector a b ↔
      C.proj.mulVec psi = psi ∧ psi ∈ fiberSubspace a b := by
  rw [phaseSector, Submodule.mem_inf, C.mem_codeSpace_iff]

/-- Project a code vector onto one modular phase sector. -/
def phaseSectorComponent (hq : 0 < q) (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a)) (b : ZMod q) :
    C.CodeSpace →ₗ[ℂ] C.phaseSector a b where
  toFun psi := ⟨(fiberProjector a b).mulVec psi.1, by
    rw [C.mem_phaseSector]
    constructor
    · calc
        C.proj.mulVec ((fiberProjector a b).mulVec psi.1) =
            (C.proj * fiberProjector a b).mulVec psi.1 :=
              Matrix.mulVec_mulVec _ _ _
        _ = (fiberProjector a b * C.proj).mulVec psi.1 := by
              rw [C.commutes_fiberProjector hq a hpres b]
        _ = (fiberProjector a b).mulVec (C.proj.mulVec psi.1) :=
              (Matrix.mulVec_mulVec _ _ _).symm
        _ = (fiberProjector a b).mulVec psi.1 := by
              rw [(C.mem_codeSpace_iff psi.1).1 psi.2]
    · exact (fiberProjector_mulVec_eq_self_iff a b _).1 (by
        rw [Matrix.mulVec_mulVec, fiberProjector_idempotent])⟩
  map_add' psi phi := by
    apply Subtype.ext
    simp [Matrix.mulVec_add]
  map_smul' c psi := by
    apply Subtype.ext
    simp [Matrix.mulVec_smul]

@[simp] theorem phaseSectorComponent_apply_coe (hq : 0 < q)
    (a : Fin n → ZMod q) (hpres : C.Preserves (phaseHom n q hq a))
    (b : ZMod q) (psi : C.CodeSpace) :
    (C.phaseSectorComponent hq a hpres b psi).1 =
      (fiberProjector a b).mulVec psi.1 := rfl

/-- A preserving modular diagonal action decomposes its code as the product
of its finitely many residue sectors.  Since the residue set is finite, this
is equivalently the internal direct-sum decomposition used in the paper. -/
def phaseSectorDecomposition (hq : 0 < q) (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a)) :
    C.CodeSpace ≃ₗ[ℂ] ((b : ZMod q) → C.phaseSector a b) := by
  letI : NeZero q := ⟨hq.ne'⟩
  let forward : C.CodeSpace →ₗ[ℂ] ((b : ZMod q) → C.phaseSector a b) :=
    LinearMap.pi fun b => C.phaseSectorComponent hq a hpres b
  let backward : ((b : ZMod q) → C.phaseSector a b) →ₗ[ℂ] C.CodeSpace :=
    { toFun := fun v => ⟨∑ b, (v b).1, by
          apply Submodule.sum_mem
          intro b _
          exact (v b).2.1⟩
      map_add' := by
        intro v w
        apply Subtype.ext
        simp [Finset.sum_add_distrib]
      map_smul' := by
        intro c v
        apply Subtype.ext
        simp [Finset.smul_sum] }
  exact
    { toLinearMap := forward
      invFun := backward
      left_inv := by
        intro psi
        apply Subtype.ext
        funext x
        dsimp [forward, backward, phaseSectorComponent]
        simp only [Finset.sum_apply, fiberProjector_mulVec_apply]
        rw [Finset.sum_eq_single (subsetSum a x)]
        · simp
        · intro b _ hb
          rw [if_neg]
          exact fun h => hb h.symm
        · simp
      right_inv := by
        intro v
        funext b
        apply Subtype.ext
        funext x
        dsimp [forward, backward, phaseSectorComponent]
        rw [fiberProjector_mulVec_apply]
        simp only [Finset.sum_apply]
        by_cases hxb : subsetSum a x = b
        · rw [if_pos hxb]
          rw [Finset.sum_eq_single b]
          · intro c _ hcb
            have hxc : subsetSum a x ≠ c := by
              intro h
              exact hcb (hxb.symm.trans h).symm
            exact (v c).2.2 x hxc
          · simp
        · have hvb : (v b).1 x = 0 := (v b).2.2 x hxb
          rw [if_neg hxb, hvb] }

/-- The sector dimensions add to the code dimension. -/
theorem sum_finrank_phaseSector [NeZero q] (hq : 0 < q) (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a)) :
    ∑ b : ZMod q, Module.finrank ℂ (C.phaseSector a b) = K := by
  have hdim := LinearEquiv.finrank_eq (C.phaseSectorDecomposition hq a hpres)
  rw [Module.finrank_pi_fintype] at hdim
  exact hdim.symm.trans C.codeSpace_finrank

/-- Residues whose code sectors are nonzero. -/
def ActiveResidue (a : Fin n → ZMod q) :=
  {b : ZMod q // C.phaseSector a b ≠ ⊥}

noncomputable instance activeResidueFintype [NeZero q] (a : Fin n → ZMod q) :
    Fintype (C.ActiveResidue a) := by
  classical
  unfold ActiveResidue
  infer_instance

theorem activeResidue_finrank_pos [NeZero q] (a : Fin n → ZMod q)
    (b : C.ActiveResidue a) :
    0 < Module.finrank ℂ (C.phaseSector a b.1) := by
  rw [Module.finrank_pos_iff]
  exact Submodule.nontrivial_iff_ne_bot.mpr b.2

/-- Every vector in an active phase sector has support in its corresponding
subset-sum fiber. -/
theorem phaseSector_support {a : Fin n → ZMod q} {b : ZMod q}
    (psi : C.phaseSector a b) {x : BitString n}
    (hx : subsetSum a x ≠ b) :
    psi.1 x = 0 :=
  psi.2.2 x hx

end CodeProjector

end

end QECC
