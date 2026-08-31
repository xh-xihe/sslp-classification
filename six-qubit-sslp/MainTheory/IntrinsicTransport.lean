import MainTheory.LocalPhaseConjugation
import MainTheory.GlobalClassificationBridge

/-!
# The intrinsic group transports along a local `X` conjugation

`MainTheory/LocalPhaseConjugation.lean` computes what conjugating a local
diagonal phase by `X^{x0}` does: it flips the phase at the flipped sites and
multiplies by a scalar independent of the basis string.  This file uses that to
move the whole level-(i) object.

The normalization standing between the bounded outer record and the original
code shifts every logical vector by `s -> s + x0`
(`D3NormalizedFreshPhase.normalizedState`).  Shifting an orthonormal frame that
way gives another orthonormal frame, because `s -> s + x0` is an involution of
the index type and `SS.innerC` is a sum over it.  The code span moves with it,
and by `LocalPhaseConjugation.diagonalValue_bxor` a diagonal phase preserving
one span corresponds to the flipped phase preserving the other.
-/

namespace MainTheory.IntrinsicTransport

open MainTheory.ClassificationLevels
open MainTheory.LocalPhaseConjugation

variable {n K : ℕ}

/-! ## Shifting a frame -/

/-- Shifting the index by `x0` is an involution. -/
@[simp] theorem bxor_bxor_self (x0 s : SS.BitString n) :
    SS.bxor (SS.bxor s x0) x0 = s := by
  funext i
  simp [SS.bxor]

/-- The same involution with the other association. -/
@[simp] theorem bxor_self_bxor (x0 s : SS.BitString n) :
    SS.bxor x0 (SS.bxor x0 s) = s := by
  funext i
  simp [SS.bxor]

/-- The inner product is unchanged by shifting both arguments. -/
theorem innerC_shift (phi psi : SS.State n ℂ) (x0 : SS.BitString n) :
    SS.innerC (fun s => phi (SS.bxor s x0)) (fun s => psi (SS.bxor s x0))
      = SS.innerC phi psi := by
  classical
  rw [SS.innerC, SS.innerC]
  refine Fintype.sum_bijective (fun s => SS.bxor s x0) ?_ _ _ (fun s => rfl)
  refine Function.Involutive.bijective ?_
  intro s
  exact bxor_bxor_self x0 s

/-- The shifted frame: every logical vector reindexed by `s -> s + x0`.  This is
exactly `D3NormalizedFreshPhase.normalizedState`. -/
def shiftFrame (F : CodeSpec.OrthonormalFrame n K) (x0 : SS.BitString n) :
    CodeSpec.OrthonormalFrame n K where
  vec := fun k s => F.vec k (SS.bxor s x0)
  orthonormal := by
    intro i j
    rw [innerC_shift]
    exact F.orthonormal i j

@[simp] theorem shiftFrame_vec (F : CodeSpec.OrthonormalFrame n K)
    (x0 : SS.BitString n) (k : Fin K) (s : SS.BitString n) :
    (shiftFrame F x0).vec k s = F.vec k (SS.bxor s x0) := rfl

/-- Frames are determined by their vectors; the orthonormality field is a
proof. -/
theorem frame_ext {F G : CodeSpec.OrthonormalFrame n K} (h : F.vec = G.vec) :
    F = G := by
  cases F with
  | mk fv fo =>
    cases G with
    | mk gv go =>
      simp only at h
      subst h
      rfl

/-- Shifting twice is the identity on frames. -/
@[simp] theorem shiftFrame_shiftFrame (F : CodeSpec.OrthonormalFrame n K)
    (x0 : SS.BitString n) : shiftFrame (shiftFrame F x0) x0 = F := by
  refine frame_ext ?_
  funext k s
  simp [shiftFrame]

/-! ## The code span moves with the frame -/

/-- Shifting a state by `x0`. -/
def shiftState (x0 : SS.BitString n) (phi : SS.State n ℂ) : SS.State n ℂ :=
  fun s => phi (SS.bxor s x0)

@[simp] theorem shiftState_shiftState (x0 : SS.BitString n) (phi : SS.State n ℂ) :
    shiftState x0 (shiftState x0 phi) = phi := by
  funext s
  simp [shiftState]

/-- The shift is linear, so it carries the span of the frame to the span of the
shifted frame. -/
theorem shiftState_smul (x0 : SS.BitString n) (a : ℂ) (phi : SS.State n ℂ) :
    shiftState x0 (a • phi) = a • shiftState x0 phi := rfl

theorem shiftState_add (x0 : SS.BitString n) (phi psi : SS.State n ℂ) :
    shiftState x0 (phi + psi) = shiftState x0 phi + shiftState x0 psi := rfl

/-- The shift as a linear equivalence, which is what moves a `Submodule.span`. -/
def shiftEquiv (x0 : SS.BitString n) : SS.State n ℂ ≃ₗ[ℂ] SS.State n ℂ where
  toFun := shiftState x0
  invFun := shiftState x0
  map_add' := shiftState_add x0
  map_smul' := shiftState_smul x0
  left_inv := shiftState_shiftState x0
  right_inv := shiftState_shiftState x0

@[simp] theorem shiftEquiv_apply (x0 : SS.BitString n) (phi : SS.State n ℂ) :
    shiftEquiv x0 phi = shiftState x0 phi := rfl

/-- **The shifted frame spans the shifted span.** -/
theorem codeSpan_shiftFrame (F : CodeSpec.OrthonormalFrame n K)
    (x0 : SS.BitString n) :
    CodeSpec.codeSpan (shiftFrame F x0)
      = (CodeSpec.codeSpan F).map (shiftEquiv x0).toLinearMap := by
  rw [CodeSpec.codeSpan, CodeSpec.codeSpan, Submodule.map_span]
  congr 1
  ext phi
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨F.vec k, ⟨k, rfl⟩, rfl⟩
  · rintro ⟨psi, ⟨k, rfl⟩, rfl⟩
    exact ⟨k, rfl⟩

/-! ## The diagonal action moves with the flip

This is where `LocalPhaseConjugation.diagonalValue_bxor` enters: shifting the
argument of a diagonal action is the flipped action, up to the global scalar. -/

/-- **The conjugation identity, at the level of the action on states.** -/
theorem diagonalAction_shift (u : LocalPhase n) (x0 : SS.BitString n)
    (phi : SS.State n ℂ) :
    shiftState x0 (diagonalAction u phi)
      = flipScalar u x0 • diagonalAction (flipPhase u x0) (shiftState x0 phi) := by
  funext s
  simp only [shiftState, diagonalAction, Pi.smul_apply, smul_eq_mul]
  rw [diagonalValue_bxor u x0 s]
  ring

/-- A scalar multiple of a state stays in any submodule the state lies in. -/
theorem mem_of_smul_mem {V : Submodule ℂ (SS.State n ℂ)} {a : ℂ} (ha : a ≠ 0)
    {phi : SS.State n ℂ} (h : a • phi ∈ V) : phi ∈ V := by
  have := V.smul_mem (a⁻¹) h
  rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at this

/-! ## The symmetry group transports

Putting the three layers together: the span moves by `shiftEquiv`, the action
moves by `flipPhase` up to a nonzero scalar, and a submodule is closed under
nonzero scalars.  So preserving one code span is the same as the flipped phase
preserving the other. -/

/-- Membership in the projector range, in the form the transport uses. -/
theorem inRange_shiftFrame_iff (F : CodeSpec.OrthonormalFrame n K)
    (x0 : SS.BitString n) (phi : SS.State n ℂ) :
    InProjectorRange (CodeProjector.ofFrame (shiftFrame F x0)) phi
      ↔ InProjectorRange (CodeProjector.ofFrame F) (shiftState x0 phi) := by
  rw [GlobalClassificationBridge.inProjectorRange_ofFrame_iff,
    GlobalClassificationBridge.inProjectorRange_ofFrame_iff,
    codeSpan_shiftFrame]
  constructor
  · rintro ⟨psi, hpsi, hmap⟩
    have : shiftState x0 phi = psi := by
      rw [← hmap]
      simp
    rwa [this]
  · intro h
    refine ⟨shiftState x0 phi, h, ?_ ⟩
    simp

/-- **The forward half of the group transport.**

If `u` preserves the shifted code span, the flipped phase preserves the
original. -/
theorem preserves_flip_of_preserves (F : CodeSpec.OrthonormalFrame n K)
    (x0 : SS.BitString n) (u : LocalPhase n)
    (h : ∀ phi, InProjectorRange (CodeProjector.ofFrame (shiftFrame F x0)) phi →
      InProjectorRange (CodeProjector.ofFrame (shiftFrame F x0)) (diagonalAction u phi))
    (phi : SS.State n ℂ)
    (hphi : InProjectorRange (CodeProjector.ofFrame F) phi) :
    InProjectorRange (CodeProjector.ofFrame F)
      (diagonalAction (flipPhase u x0) phi) := by
  have hshift : InProjectorRange (CodeProjector.ofFrame (shiftFrame F x0))
      (shiftState x0 phi) := by
    rw [inRange_shiftFrame_iff]
    simpa using hphi
  have hact := h _ hshift
  rw [inRange_shiftFrame_iff] at hact
  have hid := diagonalAction_shift u x0 (shiftState x0 phi)
  rw [shiftState_shiftState] at hid
  rw [hid] at hact
  rw [GlobalClassificationBridge.inProjectorRange_ofFrame_iff] at hact ⊢
  exact mem_of_smul_mem (flipScalar_ne_zero u x0) hact

end MainTheory.IntrinsicTransport
