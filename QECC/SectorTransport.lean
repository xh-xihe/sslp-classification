import QECC.NormalFormTransport
import QECC.SectorDecomposition

namespace QECC

noncomputable section

/-- Relabel the coordinates of a state along an equivalence of computational
basis strings.  Thus an old amplitude at `x` becomes the new amplitude at
`e x`. -/
def stateReindex {n : ℕ} (e : BitString n ≃ BitString n) :
    State n ≃ₗ[ℂ] State n :=
  LinearEquiv.funCongrLeft ℂ ℂ e.symm

@[simp] theorem stateReindex_apply {n : ℕ}
    (e : BitString n ≃ BitString n) (psi : State n) (x : BitString n) :
    stateReindex e psi x = psi (e.symm x) :=
  rfl

@[simp] theorem stateReindex_symm {n : ℕ}
    (e : BitString n ≃ BitString n) :
    (stateReindex e).symm = stateReindex e.symm := by
  ext psi x
  rfl

@[simp] theorem stateReindex_refl {n : ℕ} :
    stateReindex (Equiv.refl (BitString n)) = LinearEquiv.refl ℂ (State n) := by
  ext psi x
  rfl

namespace CodeProjector

variable {n K q q' : ℕ} (C : CodeProjector n K)

/-- Relabelling a state intertwines a projector with its matrix reindexing. -/
theorem reindex_proj_mulVec_stateReindex
    (e : BitString n ≃ BitString n) (psi : State n) :
    (C.reindex e).proj.mulVec (stateReindex e psi) =
      stateReindex e (C.proj.mulVec psi) := by
  change ((reindexOperator e C.proj).mulVecLin)
      ((stateReindex e).toLinearMap psi) =
    (stateReindex e).toLinearMap (C.proj.mulVecLin psi)
  change ((Matrix.reindex e e C.proj).mulVecLin)
      ((stateReindex e).toLinearMap psi) =
    (stateReindex e).toLinearMap (C.proj.mulVecLin psi)
  rw [Matrix.mulVecLin_reindex]
  have hinv : (LinearEquiv.funCongrLeft ℂ ℂ e)
      (stateReindex e psi) = psi := by
    ext x
    simp [stateReindex]
  simp only [LinearMap.comp_apply]
  change (LinearEquiv.funCongrLeft ℂ ℂ e.symm)
      (C.proj.mulVec ((LinearEquiv.funCongrLeft ℂ ℂ e)
        (stateReindex e psi))) =
    stateReindex e (C.proj.mulVec psi)
  rw [hinv]
  rfl

/-- Membership in the code space is preserved and reflected by computational
basis relabelling. -/
theorem stateReindex_mem_codeSpace_iff
    (e : BitString n ≃ BitString n) (psi : State n) :
    stateReindex e psi ∈ (C.reindex e).CodeSpace ↔ psi ∈ C.CodeSpace := by
  rw [(C.reindex e).mem_codeSpace_iff, C.mem_codeSpace_iff,
    C.reindex_proj_mulVec_stateReindex]
  exact (stateReindex e).injective.eq_iff

/-- The code space itself, rather than only its projector, is transported by
computational-basis relabelling. -/
def codeSpaceReindexEquiv (e : BitString n ≃ BitString n) :
    C.CodeSpace ≃ₗ[ℂ] (C.reindex e).CodeSpace where
  toFun psi := ⟨stateReindex e psi.1,
    (C.stateReindex_mem_codeSpace_iff e psi.1).2 psi.2⟩
  invFun phi := ⟨(stateReindex e).symm phi.1, by
    apply (C.stateReindex_mem_codeSpace_iff e _).1
    have hmem : stateReindex e ((stateReindex e).symm phi.1) ∈
        (C.reindex e).CodeSpace := by
      rw [(stateReindex e).apply_symm_apply]
      exact phi.2
    exact hmem⟩
  left_inv psi := by
    apply Subtype.ext
    exact (stateReindex e).symm_apply_apply psi.1
  right_inv phi := by
    apply Subtype.ext
    exact (stateReindex e).apply_symm_apply phi.1
  map_add' psi phi := by
    apply Subtype.ext
    simp
  map_smul' c psi := by
    apply Subtype.ext
    simp

@[simp] theorem codeSpaceReindexEquiv_apply_coe
    (e : BitString n ≃ BitString n) (psi : C.CodeSpace) :
    (C.codeSpaceReindexEquiv e psi).1 = stateReindex e psi.1 :=
  rfl

/-- A set-level transport identity for subset-sum fibers induces the matching
transport identity for their coordinate support subspaces. -/
theorem stateReindex_mem_fiberSubspace_iff
    (e : BitString n ≃ BitString n)
    (a : Fin n → ZMod q) (b : ZMod q)
    (a' : Fin n → ZMod q') (b' : ZMod q')
    (hfiber : e '' subsetSumFiber a b = subsetSumFiber a' b')
    (psi : State n) :
    stateReindex e psi ∈ fiberSubspace a' b' ↔
      psi ∈ fiberSubspace a b := by
  have hlabel (x : BitString n) :
      subsetSum a' (e x) = b' ↔ subsetSum a x = b := by
    change e x ∈ subsetSumFiber a' b' ↔ x ∈ subsetSumFiber a b
    rw [← hfiber]
    simp
  constructor
  · intro hnew x hx
    have hnewx : subsetSum a' (e x) ≠ b' := by
      intro heq
      exact hx ((hlabel x).1 heq)
    have hz := hnew (e x) hnewx
    simpa using hz
  · intro hold y hy
    have holdx : subsetSum a (e.symm y) ≠ b := by
      intro heq
      apply hy
      have := (hlabel (e.symm y)).2 heq
      simpa using this
    exact hold (e.symm y) holdx

/-- A set-level transport identity for fibers transports the corresponding
intersection of that fiber subspace with the code space. -/
theorem stateReindex_mem_phaseSector_iff
    (e : BitString n ≃ BitString n)
    (a : Fin n → ZMod q) (b : ZMod q)
    (a' : Fin n → ZMod q') (b' : ZMod q')
    (hfiber : e '' subsetSumFiber a b = subsetSumFiber a' b')
    (psi : State n) :
    stateReindex e psi ∈ (C.reindex e).phaseSector a' b' ↔
      psi ∈ C.phaseSector a b := by
  change (stateReindex e psi ∈ (C.reindex e).CodeSpace ∧
      stateReindex e psi ∈ fiberSubspace a' b') ↔
    (psi ∈ C.CodeSpace ∧ psi ∈ fiberSubspace a b)
  rw [C.stateReindex_mem_codeSpace_iff,
    stateReindex_mem_fiberSubspace_iff e a b a' b' hfiber]

/-- Restrict state relabelling to an equivalence between two actual phase
sectors whose fibers are identified by the same basis equivalence. -/
def phaseSectorReindexEquiv
    (e : BitString n ≃ BitString n)
    (a : Fin n → ZMod q) (b : ZMod q)
    (a' : Fin n → ZMod q') (b' : ZMod q')
    (hfiber : e '' subsetSumFiber a b = subsetSumFiber a' b') :
    C.phaseSector a b ≃ₗ[ℂ] (C.reindex e).phaseSector a' b' where
  toFun psi := ⟨stateReindex e psi.1,
    (C.stateReindex_mem_phaseSector_iff e a b a' b' hfiber psi.1).2 psi.2⟩
  invFun phi := ⟨(stateReindex e).symm phi.1, by
    apply (C.stateReindex_mem_phaseSector_iff e a b a' b' hfiber _).1
    have hmem : stateReindex e ((stateReindex e).symm phi.1) ∈
        (C.reindex e).phaseSector a' b' := by
      rw [(stateReindex e).apply_symm_apply]
      exact phi.2
    exact hmem⟩
  left_inv psi := by
    apply Subtype.ext
    exact (stateReindex e).symm_apply_apply psi.1
  right_inv phi := by
    apply Subtype.ext
    exact (stateReindex e).apply_symm_apply phi.1
  map_add' psi phi := by
    apply Subtype.ext
    simp
  map_smul' c psi := by
    apply Subtype.ext
    simp

@[simp] theorem phaseSectorReindexEquiv_apply_coe
    (e : BitString n ≃ BitString n)
    (a : Fin n → ZMod q) (b : ZMod q)
    (a' : Fin n → ZMod q') (b' : ZMod q')
    (hfiber : e '' subsetSumFiber a b = subsetSumFiber a' b')
    (psi : C.phaseSector a b) :
    (C.phaseSectorReindexEquiv e a b a' b' hfiber psi).1 =
      stateReindex e psi.1 :=
  rfl

/-- In particular, transported phase sectors have equal dimensions. -/
theorem finrank_phaseSector_reindex
    (e : BitString n ≃ BitString n)
    (a : Fin n → ZMod q) (b : ZMod q)
    (a' : Fin n → ZMod q') (b' : ZMod q')
    (hfiber : e '' subsetSumFiber a b = subsetSumFiber a' b') :
    Module.finrank ℂ (C.phaseSector a b) =
      Module.finrank ℂ ((C.reindex e).phaseSector a' b') :=
  LinearEquiv.finrank_eq
    (C.phaseSectorReindexEquiv e a b a' b' hfiber)

/-- A transported sector is nonzero exactly when the original sector is. -/
theorem phaseSector_reindex_ne_bot_iff
    (e : BitString n ≃ BitString n)
    (a : Fin n → ZMod q) (b : ZMod q)
    (a' : Fin n → ZMod q') (b' : ZMod q')
    (hfiber : e '' subsetSumFiber a b = subsetSumFiber a' b') :
    (C.reindex e).phaseSector a' b' ≠ ⊥ ↔ C.phaseSector a b ≠ ⊥ := by
  have hdim := C.finrank_phaseSector_reindex e a b a' b' hfiber
  constructor
  · intro htarget hsource
    apply htarget
    apply Submodule.finrank_eq_zero.mp
    rw [← hdim]
    exact Submodule.finrank_eq_zero.mpr hsource
  · intro hsource htarget
    apply hsource
    apply Submodule.finrank_eq_zero.mp
    rw [hdim]
    exact Submodule.finrank_eq_zero.mpr htarget

/-- Local `X` transport identifies the old `b` sector with the sector labelled
`b - subsetSum a t` for the sign-flipped coefficient vector. -/
def xorPhaseSectorEquiv (a : Fin n → ZMod q) (t : BitString n)
    (b : ZMod q) :
    C.phaseSector a b ≃ₗ[ℂ]
      (C.reindex (xorEquiv t)).phaseSector (xorCoefficient t a)
        (b - subsetSum a t) :=
  C.phaseSectorReindexEquiv (xorEquiv t) a b
    (xorCoefficient t a) (b - subsetSum a t)
    (image_subsetSumFiber_xorEquiv a t b)

@[simp] theorem xorPhaseSectorEquiv_apply_coe
    (a : Fin n → ZMod q) (t : BitString n) (b : ZMod q)
    (psi : C.phaseSector a b) :
    (C.xorPhaseSectorEquiv a t b psi).1 =
      stateReindex (xorEquiv t) psi.1 :=
  rfl

theorem finrank_xorPhaseSector
    (a : Fin n → ZMod q) (t : BitString n) (b : ZMod q) :
    Module.finrank ℂ (C.phaseSector a b) =
      Module.finrank ℂ
        ((C.reindex (xorEquiv t)).phaseSector (xorCoefficient t a)
          (b - subsetSum a t)) :=
  LinearEquiv.finrank_eq (C.xorPhaseSectorEquiv a t b)

theorem xor_phaseSector_ne_bot_iff
    (a : Fin n → ZMod q) (t : BitString n) (b : ZMod q) :
    (C.reindex (xorEquiv t)).phaseSector (xorCoefficient t a)
        (b - subsetSum a t) ≠ ⊥ ↔
      C.phaseSector a b ≠ ⊥ :=
  C.phaseSector_reindex_ne_bot_iff (xorEquiv t) a b
    (xorCoefficient t a) (b - subsetSum a t)
    (image_subsetSumFiber_xorEquiv a t b)

/-- Local bit flips biject the active residue labels by translation through
`-subsetSum a t`. -/
def xorActiveResidueEquiv (a : Fin n → ZMod q) (t : BitString n) :
    C.ActiveResidue a ≃
      (C.reindex (xorEquiv t)).ActiveResidue (xorCoefficient t a) where
  toFun b := ⟨b.1 - subsetSum a t,
    (C.xor_phaseSector_ne_bot_iff a t b.1).2 b.2⟩
  invFun c := ⟨c.1 + subsetSum a t, by
    apply (C.xor_phaseSector_ne_bot_iff a t
      (c.1 + subsetSum a t)).1
    simpa using c.2⟩
  left_inv b := by
    apply Subtype.ext
    simp
  right_inv c := by
    apply Subtype.ext
    simp

@[simp] theorem xorActiveResidueEquiv_apply_val
    (a : Fin n → ZMod q) (t : BitString n) (b : C.ActiveResidue a) :
    (C.xorActiveResidueEquiv a t b).1 = b.1 - subsetSum a t :=
  rfl

@[simp] theorem xorActiveResidueEquiv_symm_apply_val
    (a : Fin n → ZMod q) (t : BitString n)
    (c : (C.reindex (xorEquiv t)).ActiveResidue (xorCoefficient t a)) :
    ((C.xorActiveResidueEquiv a t).symm c).1 =
      c.1 + subsetSum a t :=
  rfl

/-- Coordinate permutation identifies the `b` sector with the same-labelled
sector for the permuted coefficient vector. -/
def coordinatePhaseSectorEquiv (sigma : Equiv.Perm (Fin n))
    (a : Fin n → ZMod q) (b : ZMod q) :
    C.phaseSector a b ≃ₗ[ℂ]
      (C.reindex (coordinateEquiv sigma)).phaseSector
        (permuteCoefficient sigma a) b :=
  C.phaseSectorReindexEquiv (coordinateEquiv sigma) a b
    (permuteCoefficient sigma a) b
    (image_subsetSumFiber_coordinateEquiv sigma a b)

@[simp] theorem coordinatePhaseSectorEquiv_apply_coe
    (sigma : Equiv.Perm (Fin n)) (a : Fin n → ZMod q) (b : ZMod q)
    (psi : C.phaseSector a b) :
    (C.coordinatePhaseSectorEquiv sigma a b psi).1 =
      stateReindex (coordinateEquiv sigma) psi.1 :=
  rfl

theorem finrank_coordinatePhaseSector
    (sigma : Equiv.Perm (Fin n)) (a : Fin n → ZMod q) (b : ZMod q) :
    Module.finrank ℂ (C.phaseSector a b) =
      Module.finrank ℂ
        ((C.reindex (coordinateEquiv sigma)).phaseSector
          (permuteCoefficient sigma a) b) :=
  LinearEquiv.finrank_eq (C.coordinatePhaseSectorEquiv sigma a b)

theorem coordinate_phaseSector_ne_bot_iff
    (sigma : Equiv.Perm (Fin n)) (a : Fin n → ZMod q) (b : ZMod q) :
    (C.reindex (coordinateEquiv sigma)).phaseSector
        (permuteCoefficient sigma a) b ≠ ⊥ ↔
      C.phaseSector a b ≠ ⊥ :=
  C.phaseSector_reindex_ne_bot_iff (coordinateEquiv sigma) a b
    (permuteCoefficient sigma a) b
    (image_subsetSumFiber_coordinateEquiv sigma a b)

/-- A coordinate permutation bijects the active residues without changing
their labels. -/
def coordinateActiveResidueEquiv (sigma : Equiv.Perm (Fin n))
    (a : Fin n → ZMod q) :
    C.ActiveResidue a ≃
      (C.reindex (coordinateEquiv sigma)).ActiveResidue
        (permuteCoefficient sigma a) where
  toFun b := ⟨b.1,
    (C.coordinate_phaseSector_ne_bot_iff sigma a b.1).2 b.2⟩
  invFun c := ⟨c.1,
    (C.coordinate_phaseSector_ne_bot_iff sigma a c.1).1 c.2⟩
  left_inv b := by
    apply Subtype.ext
    rfl
  right_inv c := by
    apply Subtype.ext
    rfl

@[simp] theorem coordinateActiveResidueEquiv_apply_val
    (sigma : Equiv.Perm (Fin n)) (a : Fin n → ZMod q)
    (b : C.ActiveResidue a) :
    (C.coordinateActiveResidueEquiv sigma a b).1 = b.1 :=
  rfl

@[simp] theorem coordinateActiveResidueEquiv_symm_apply_val
    (sigma : Equiv.Perm (Fin n)) (a : Fin n → ZMod q)
    (c : (C.reindex (coordinateEquiv sigma)).ActiveResidue
      (permuteCoefficient sigma a)) :
    ((C.coordinateActiveResidueEquiv sigma a).symm c).1 = c.1 :=
  rfl

/-- The phase-sector equivalence for the full canonical normalization: first
local bit flips, then a physical-coordinate permutation. -/
def canonicalPhaseSectorEquiv (a : Fin n → ZMod q)
    (t : BitString n) (sigma : Equiv.Perm (Fin n)) (b : ZMod q) :
    C.phaseSector a b ≃ₗ[ℂ]
      ((C.reindex (xorEquiv t)).reindex (coordinateEquiv sigma)).phaseSector
        (permuteCoefficient sigma (xorCoefficient t a))
        (b - subsetSum a t) :=
  (C.xorPhaseSectorEquiv a t b).trans
    ((C.reindex (xorEquiv t)).coordinatePhaseSectorEquiv sigma
      (xorCoefficient t a) (b - subsetSum a t))

/-- The full canonical normalization bijects active sectors.  On residue
labels this is exactly translation by the anchor subset sum; the following
coordinate permutation leaves that translated label unchanged. -/
def canonicalActiveResidueEquiv (a : Fin n → ZMod q)
    (t : BitString n) (sigma : Equiv.Perm (Fin n)) :
    C.ActiveResidue a ≃
      ((C.reindex (xorEquiv t)).reindex
        (coordinateEquiv sigma)).ActiveResidue
          (permuteCoefficient sigma (xorCoefficient t a)) :=
  (C.xorActiveResidueEquiv a t).trans
    ((C.reindex (xorEquiv t)).coordinateActiveResidueEquiv sigma
      (xorCoefficient t a))

@[simp] theorem canonicalActiveResidueEquiv_apply_val
    (a : Fin n → ZMod q) (t : BitString n)
    (sigma : Equiv.Perm (Fin n)) (b : C.ActiveResidue a) :
    (C.canonicalActiveResidueEquiv a t sigma b).1 =
      b.1 - subsetSum a t :=
  rfl

@[simp] theorem canonicalActiveResidueEquiv_symm_apply_val
    (a : Fin n → ZMod q) (t : BitString n)
    (sigma : Equiv.Perm (Fin n))
    (c : ((C.reindex (xorEquiv t)).reindex
      (coordinateEquiv sigma)).ActiveResidue
        (permuteCoefficient sigma (xorCoefficient t a))) :
    ((C.canonicalActiveResidueEquiv a t sigma).symm c).1 =
      c.1 + subsetSum a t :=
  rfl

@[simp] theorem canonicalPhaseSectorEquiv_apply_coe
    (a : Fin n → ZMod q) (t : BitString n)
    (sigma : Equiv.Perm (Fin n)) (b : ZMod q)
    (psi : C.phaseSector a b) :
    (C.canonicalPhaseSectorEquiv a t sigma b psi).1 =
      stateReindex (coordinateEquiv sigma)
        (stateReindex (xorEquiv t) psi.1) :=
  rfl

theorem finrank_canonicalPhaseSector
    (a : Fin n → ZMod q) (t : BitString n)
    (sigma : Equiv.Perm (Fin n)) (b : ZMod q) :
    Module.finrank ℂ (C.phaseSector a b) =
      Module.finrank ℂ
        (((C.reindex (xorEquiv t)).reindex
          (coordinateEquiv sigma)).phaseSector
            (permuteCoefficient sigma (xorCoefficient t a))
            (b - subsetSum a t)) :=
  LinearEquiv.finrank_eq (C.canonicalPhaseSectorEquiv a t sigma b)

/-- The transported vector is supported in the canonically transformed fiber.
This is the pointwise support statement used by the displayed SSLP normal
form. -/
theorem canonicalPhaseSectorEquiv_support
    (a : Fin n → ZMod q) (t : BitString n)
    (sigma : Equiv.Perm (Fin n)) (b : ZMod q)
    (psi : C.phaseSector a b) (x : BitString n)
    (hx : subsetSum (permuteCoefficient sigma (xorCoefficient t a)) x ≠
      b - subsetSum a t) :
    (C.canonicalPhaseSectorEquiv a t sigma b psi).1 x = 0 :=
  (C.canonicalPhaseSectorEquiv a t sigma b psi).2.2 x hx

end CodeProjector

end

end QECC
