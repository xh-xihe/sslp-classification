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

/-! ## `flipPhase` is a group map -/

/-- `unitary ℂ` is commutative, since `ℂ` is.  Mathlib registers only a `Group`
instance, so `mul_comm` is not available by typeclass and is proved here. -/
theorem unitary_mul_comm (z w : unitary ℂ) : z * w = w * z :=
  Subtype.ext (by simp [mul_comm])

theorem localPhase_mul_comm (u v : LocalPhase n) : u * v = v * u := by
  funext j
  exact unitary_mul_comm (u j) (v j)

theorem flipPhase_mul (u v : LocalPhase n) (x0 : SS.BitString n) :
    flipPhase (u * v) x0 = flipPhase u x0 * flipPhase v x0 := by
  funext j
  by_cases h : x0 j
  · simp [flipPhase, h, unitary_mul_comm]
  · simp [flipPhase, h]

theorem flipPhase_inv (u : LocalPhase n) (x0 : SS.BitString n) :
    flipPhase u⁻¹ x0 = (flipPhase u x0)⁻¹ := by
  funext j
  by_cases h : x0 j
  · simp [flipPhase, h]
  · simp [flipPhase, h]

theorem flipPhase_one (x0 : SS.BitString n) :
    flipPhase (1 : LocalPhase n) x0 = 1 := by
  funext j
  by_cases h : x0 j
  · simp [flipPhase, h]
  · simp [flipPhase, h]

/-! ## The symmetry groups correspond -/

/-- **A diagonal symmetry of the shifted code flips to one of the original.** -/
theorem mem_symmetryGroup_flip (F : CodeSpec.OrthonormalFrame n K)
    (x0 : SS.BitString n) (u : LocalPhase n)
    (hu : u ∈ diagonalSymmetryGroup (CodeProjector.ofFrame (shiftFrame F x0))) :
    flipPhase u x0 ∈ diagonalSymmetryGroup (CodeProjector.ofFrame F) := by
  refine ⟨?_, ?_⟩
  · exact preserves_flip_of_preserves F x0 u hu.1
  · intro phi hphi
    rw [← flipPhase_inv]
    exact preserves_flip_of_preserves F x0 u⁻¹ hu.2 phi hphi

/-! ## Descending to the intrinsic quotient

The last step.  `flipPhase` carries projectively trivial symmetries to
projectively trivial ones -- the scalar just picks up `flipScalar` -- so the
correspondence descends to the quotient by exactly those, which is the intrinsic
group of Definition 6.1(i). -/

/-- **Projective triviality transports.** -/
theorem isProjectivelyTrivial_flip (F : CodeSpec.OrthonormalFrame n K)
    (x0 : SS.BitString n)
    (u : diagonalSymmetryGroup (CodeProjector.ofFrame (shiftFrame F x0)))
    (hu : IsProjectivelyTrivial (CodeProjector.ofFrame (shiftFrame F x0)) u) :
    IsProjectivelyTrivial (CodeProjector.ofFrame F)
      ⟨flipPhase (u : LocalPhase n) x0,
        mem_symmetryGroup_flip F x0 (u : LocalPhase n) u.2⟩ := by
  obtain ⟨lam, hlam, hact⟩ := hu
  refine ⟨(flipScalar (u : LocalPhase n) x0)⁻¹ * lam,
    mul_ne_zero (inv_ne_zero (flipScalar_ne_zero _ _)) hlam, ?_⟩
  intro phi hphi
  have hshift : InProjectorRange (CodeProjector.ofFrame (shiftFrame F x0))
      (shiftState x0 phi) := by
    rw [inRange_shiftFrame_iff]
    simpa using hphi
  have hid := diagonalAction_shift (u : LocalPhase n) x0 (shiftState x0 phi)
  rw [shiftState_shiftState] at hid
  have hs := hact _ hshift
  rw [hs] at hid
  -- hid : shiftState x0 (lam • shiftState x0 phi)
  --         = flipScalar • diagonalAction (flipPhase u x0) phi
  have hrhs : shiftState x0 (lam • shiftState x0 phi) = lam • phi := by
    rw [shiftState_smul, shiftState_shiftState]
  rw [hrhs] at hid
  have hcancel : diagonalAction (flipPhase (u : LocalPhase n) x0) phi
      = (flipScalar (u : LocalPhase n) x0)⁻¹ • (lam • phi) := by
    rw [hid, smul_smul, inv_mul_cancel₀ (flipScalar_ne_zero _ _), one_smul]
  rw [hcancel, smul_smul]

/-- **The intrinsic classes correspond.**

Equal classes on the shifted code give equal classes on the original.  With
`flipPhase` an involution this is the isomorphism the transport needs. -/
theorem intrinsicClass_flip_eq (F : CodeSpec.OrthonormalFrame n K)
    (x0 : SS.BitString n)
    (u v : diagonalSymmetryGroup (CodeProjector.ofFrame (shiftFrame F x0)))
    (h : intrinsicClass (CodeProjector.ofFrame (shiftFrame F x0)) u
      = intrinsicClass (CodeProjector.ofFrame (shiftFrame F x0)) v) :
    intrinsicClass (CodeProjector.ofFrame F)
        ⟨flipPhase (u : LocalPhase n) x0,
          mem_symmetryGroup_flip F x0 _ u.2⟩
      = intrinsicClass (CodeProjector.ofFrame F)
        ⟨flipPhase (v : LocalPhase n) x0,
          mem_symmetryGroup_flip F x0 _ v.2⟩ := by
  rw [intrinsicClass, intrinsicClass, QuotientGroup.eq]
  rw [intrinsicClass, intrinsicClass, QuotientGroup.eq] at h
  have hmem := isProjectivelyTrivial_flip F x0 (u⁻¹ * v) h
  refine Subgroup.mem_carrier.1 ?_
  show IsProjectivelyTrivial (CodeProjector.ofFrame F) _
  convert hmem using 2
  push_cast
  rw [flipPhase_mul, flipPhase_inv]

/-! ## The group depends only on the code span

`RankTwoGlobal.FiniteGeneratorResolution` carries `span_eq`: its eigenframe
spans the same code as the original frame.  Since a diagonal symmetry is defined
by what it does to the projector *range*, and the range is the span, the
symmetry group and its projectively trivial subgroup do not see which frame was
used.  This is what lets the transport, stated for `shiftFrame F x0`, be applied
with `F` the eigenframe and read off on the original code. -/

theorem inProjectorRange_congr {F G : CodeSpec.OrthonormalFrame n K}
    (h : CodeSpec.codeSpan F = CodeSpec.codeSpan G) (phi : SS.State n ℂ) :
    InProjectorRange (CodeProjector.ofFrame F) phi
      ↔ InProjectorRange (CodeProjector.ofFrame G) phi := by
  rw [GlobalClassificationBridge.inProjectorRange_ofFrame_iff,
    GlobalClassificationBridge.inProjectorRange_ofFrame_iff, h]

/-- **The diagonal symmetry group is an invariant of the code span.** -/
theorem diagonalSymmetryGroup_congr {F G : CodeSpec.OrthonormalFrame n K}
    (h : CodeSpec.codeSpan F = CodeSpec.codeSpan G) :
    diagonalSymmetryGroup (CodeProjector.ofFrame F)
      = diagonalSymmetryGroup (CodeProjector.ofFrame G) := by
  ext u
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun phi hphi => ?_, fun phi hphi => ?_⟩
    · exact (inProjectorRange_congr h _).1 (h1 phi ((inProjectorRange_congr h _).2 hphi))
    · exact (inProjectorRange_congr h _).1 (h2 phi ((inProjectorRange_congr h _).2 hphi))
  · rintro ⟨h1, h2⟩
    refine ⟨fun phi hphi => ?_, fun phi hphi => ?_⟩
    · exact (inProjectorRange_congr h _).2 (h1 phi ((inProjectorRange_congr h _).1 hphi))
    · exact (inProjectorRange_congr h _).2 (h2 phi ((inProjectorRange_congr h _).1 hphi))

/-- Projective triviality is likewise an invariant of the span. -/
theorem isProjectivelyTrivial_congr {F G : CodeSpec.OrthonormalFrame n K}
    (h : CodeSpec.codeSpan F = CodeSpec.codeSpan G)
    (u : diagonalSymmetryGroup (CodeProjector.ofFrame F))
    (v : diagonalSymmetryGroup (CodeProjector.ofFrame G))
    (huv : (u : LocalPhase n) = (v : LocalPhase n))
    (hu : IsProjectivelyTrivial (CodeProjector.ofFrame F) u) :
    IsProjectivelyTrivial (CodeProjector.ofFrame G) v := by
  obtain ⟨lam, hlam, hact⟩ := hu
  refine ⟨lam, hlam, fun phi hphi => ?_⟩
  rw [← huv]
  exact hact phi ((inProjectorRange_congr h _).2 hphi)

end MainTheory.IntrinsicTransport
