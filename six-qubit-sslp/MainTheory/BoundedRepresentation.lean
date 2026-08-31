import MainTheory.IntrinsicClassBridge
import MainTheory.LocalPhaseAngle
import MainTheory.GlobalClassificationBridge

/-!
# The bounded-representation obligation

`GlobalClassificationBridge` states the six-qubit capstones in terms of
`IntrinsicFiniteCyclicInputs`, whose `cover` field is a
`ProjectiveGroupFinite.BoundedLiftCover`.  That field is never constructed, and
its own docstring calls it "the global completeness obligation that must
eventually be discharged from the code-preserving gate semantics and the uniform
lift bound".

Both of those inputs now exist.  The gate semantics is
`D3CertifiedSpectralOuterEntrance.arbitrary_code_enters_outer`, and the uniform
bound is the kernel-checked `BetaExact 6 9`.  What still separates them from the
cover is a *transport*, and this file makes that precise rather than describing
it.

**Where the gap actually is.**  The entrance produces three conclusions.  The
first, `SameProjectiveOnCode C.frame (resolutionFiniteGateEnd ..) (realGateEnd
theta)`, lives on the original code but carries no bound: the order of
`rationalLiftOfResolution` is positive and otherwise unconstrained.  The bound
`2 <= q <= 9` appears only in the third conclusion, and there it is attached to
the *fresh* generator on `normalizedCodeOfResolution` -- a different code.  So
the bounded object and the original group sit on opposite sides of a
normalization, and none of `PermutationSemanticTransport`,
`CubeCompletionTransport` or `UnitPowerSemanticTransport` mentions
`IntrinsicGroup` or `intrinsicClass`: the transport machinery operates on codes,
gates and records, never on the quotient group.

`BoundedRepresentation` below is exactly what has to be carried across.  Given
it, the cover and everything downstream follow, which is what this file proves.
Whoever closes the transport can discharge one named statement instead of
rediscovering which one it is.
-/

namespace MainTheory.BoundedRepresentation

open MainTheory.ClassificationLevels
open MainTheory.GlobalClassificationBridge
open MainTheory.ProjectiveGroupFinite

/-! ## The gate of a bounded label -/

/-- A phase on the unit circle, as an element of `unitary ℂ`. -/
noncomputable def circlePhase (t : ℝ) : unitary ℂ :=
  ⟨Complex.exp ((t : ℂ) * Complex.I), by
    have hstar : star (Complex.exp ((t : ℂ) * Complex.I))
        = Complex.exp (-((t : ℂ) * Complex.I)) := by
      rw [Complex.star_def, ← Complex.exp_conj]
      congr 1
      simp
    constructor
    · rw [hstar, ← Complex.exp_add]; simp
    · rw [hstar, ← Complex.exp_add]; simp⟩

/-- The local diagonal phase named by a bounded label: site `j` carries the
`a j`-th power of the primitive `(q+1)`-st root of unity. -/
noncomputable def gateOfLabel (lbl : BoundedPhaseLabel 6 9) : LocalPhase 6 :=
  fun j => circlePhase
    (2 * Real.pi * ((lbl.2 j).val : ℝ) / ((lbl.1.val : ℝ) + 1))

/-! ## The obligation -/

/-- **The one statement still missing.**

Every class of the intrinsic projective diagonal group is the class of a
diagonal symmetry whose local phase is named by a bounded label.

This is the transport described above, stated on the original code so that no
normalization appears in it. -/
def HasBoundedRepresentation (C : CodeSpec.ExactCode 6 2 3) : Prop :=
  ∀ g : IntrinsicGroup C,
    ∃ (lbl : BoundedPhaseLabel 6 9)
      (u : diagonalSymmetryGroup (exactCodeProjector C)),
      intrinsicClass (exactCodeProjector C) u = g ∧
        (u : LocalPhase 6) = gateOfLabel lbl

/-! ## What it buys -/

/-- The action a bounded label induces: the class of its gate when that gate is
a symmetry of the code, and the identity otherwise. -/
noncomputable def actionOfLabel (C : CodeSpec.ExactCode 6 2 3)
    (lbl : BoundedPhaseLabel 6 9) : IntrinsicGroup C := by
  classical
  exact if hm : gateOfLabel lbl ∈ diagonalSymmetryGroup (exactCodeProjector C) then
      intrinsicClass (exactCodeProjector C) ⟨gateOfLabel lbl, hm⟩
    else 1

/-- **The cover follows.**

The obligation is exactly what makes `actionOfLabel` surjective. -/
noncomputable def coverOfRepresentation {C : CodeSpec.ExactCode 6 2 3}
    (h : HasBoundedRepresentation C) :
    BoundedLiftCover 6 9 (IntrinsicGroup C) := by
  classical
  refine { actionOf := actionOfLabel C, covers := ?_ }
  intro g
  obtain ⟨lbl, u, hclass, hgate⟩ := h g
  refine ⟨lbl, ?_⟩
  have hm : gateOfLabel lbl ∈ diagonalSymmetryGroup (exactCodeProjector C) := by
    rw [← hgate]
    exact u.2
  have hu : (⟨gateOfLabel lbl, hm⟩ : diagonalSymmetryGroup (exactCodeProjector C)) = u :=
    Subtype.ext hgate.symm
  rw [actionOfLabel, dif_pos hm, hu, hclass]

/-- The intrinsic group is finite. -/
theorem finite_of_representation {C : CodeSpec.ExactCode 6 2 3}
    (h : HasBoundedRepresentation C) : Finite (IntrinsicGroup C) :=
  finite_of_boundedLiftCover (coverOfRepresentation h)

/-- The intrinsic group is cyclic, given a faithful character.

Together with `finite_of_representation` this is `IntrinsicFiniteCyclicInputs`
in full, so every capstone in `GlobalClassificationBridge` becomes available. -/
noncomputable def inputsOfRepresentation {C : CodeSpec.ExactCode 6 2 3}
    (h : HasBoundedRepresentation C)
    (chi : IntrinsicGroup C →* ℂ) (hchi : Function.Injective chi) :
    IntrinsicFiniteCyclicInputs (B := 9) C where
  cover := coverOfRepresentation h
  character := chi
  faithful := hchi

end MainTheory.BoundedRepresentation
