import MainTheory.ClassificationLevels

/-!
# Projective sameness determines the intrinsic class

`MainTheory/GlobalClassificationBridge.lean` states the six-qubit capstones in
terms of `IntrinsicFiniteCyclicInputs`, whose `cover` field is a
`ProjectiveGroupFinite.BoundedLiftCover`.  Its own docstring calls that field
"the global completeness obligation that must eventually be discharged from the
code-preserving gate semantics and the uniform lift bound".  Both of those are
now available: the gate semantics from
`D3CertifiedSpectralOuterEntrance.arbitrary_code_enters_outer`, and the uniform
bound from the generated `BetaExact 6 9`.

Discharging the obligation needs one bridge that is missing, and it has nothing
to do with either input: the entrance theorem concludes
`CodeSpec.SameProjectiveOnCode`, while the cover has to produce elements of the
*quotient* group `diagonalSymmetryGroup ⧸ projectivelyTrivialSubgroup`.  This
file supplies the step between them.

The argument is short.  If `u` and `v` agree up to a scalar on the code, then
`u * v⁻¹` acts as that scalar, because `v⁻¹` maps the code into itself and so
can be used to move the test vector.  Being projectively trivial is exactly
membership in the subgroup being quotiented by, so the two classes coincide.
-/

namespace MainTheory.IntrinsicClassBridge

open MainTheory.ClassificationLevels

variable {n : ℕ}

/-- A symmetry and its inverse undo each other on states. -/
theorem diagonalAction_inv_left (w : LocalPhase n) (phi : SS.State n ℂ) :
    diagonalAction w⁻¹ (diagonalAction w phi) = phi := by
  rw [← diagonalAction_mul]
  simp

/-- **The bridge.**  Projective sameness on the code is equality in the
intrinsic group.

This is the step from what `D3CertifiedSpectralOuterEntrance` concludes -- a
`CodeSpec.SameProjectiveOnCode` between a finite gate and a real one -- to what
`ProjectiveGroupFinite.BoundedLiftCover` needs, namely elements of the quotient
`diagonalSymmetryGroup / projectivelyTrivialSubgroup`.

The proof works with `u⁻¹ * v` directly rather than with `u * v⁻¹`, because the
quotient's membership condition is stated that way and `LocalPhase` is not
registered as commutative even though it is. -/
theorem intrinsicClass_eq_of_sameProjective (P : CodeProjector n)
    (u v : diagonalSymmetryGroup P) (lam : ℂ) (hlam : lam ≠ 0)
    (h : ∀ phi, InProjectorRange P phi →
      diagonalAction (u : LocalPhase n) phi
        = lam • diagonalAction (v : LocalPhase n) phi) :
    intrinsicClass P u = intrinsicClass P v := by
  rw [intrinsicClass, intrinsicClass, QuotientGroup.eq]
  refine ⟨ lam⁻¹, inv_ne_zero hlam, ?_ ⟩
  intro phi hphi
  have hcoe : (((u⁻¹ * v : diagonalSymmetryGroup P)) : LocalPhase n)
      = ((u : LocalPhase n))⁻¹ * (v : LocalPhase n) := by
    simp
  have hv : diagonalAction (v : LocalPhase n) phi = lam⁻¹ •
      diagonalAction (u : LocalPhase n) phi := by
    rw [h phi hphi, smul_smul, inv_mul_cancel₀ hlam, one_smul]
  rw [hcoe, diagonalAction_mul, hv, diagonalAction_smul, diagonalAction_inv_left]

end MainTheory.IntrinsicClassBridge
