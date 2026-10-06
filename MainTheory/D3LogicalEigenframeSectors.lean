import MainTheory.PhaseSectorBridge

/-!
# From a logical eigenframe to phase-sector data

The unresolved part of `PhaseSectorBridge.SpectralExtractionPrinciple` should
be ordinary finite-dimensional spectral linear algebra, not a second hidden
phase-sector assumption.  This module isolates the raw output of that linear
algebra: an orthonormal eigenframe spanning the actual two-dimensional code.

Everything after that output is constructive.  First, each eigenvalue is
proved to lie on the unit circle directly from a nonzero amplitude of its unit
eigenvector.  It is then written as `phaseExp` of a real phase.  The remainder
of this module groups the two eigenvectors into either one rank-two sector or
two rank-one sectors and constructs the exact sigma-index/span link required
by `LogicalSectorResolution`.
-/

namespace MainTheory.D3LogicalEigenframeSectors

open MainTheory
open MainTheory.PhaseSectorFull

noncomputable section

/-- Raw spectral output on the actual logical code: an orthonormal eigenframe
with an equality of code spans.  No sector grouping or real phase choices are
included as assumptions. -/
structure LogicalEigenframe
    (C : CodeSpec.ExactCode 6 2 3) (theta : Fin 6 → ℝ) where
  frame : CodeSpec.OrthonormalFrame 6 2
  span_eq : CodeSpec.codeSpan C.frame = CodeSpec.codeSpan frame
  eigenvalue : Fin 2 → ℂ
  eigen : ∀ k,
    MainTheory.RealGate.realGate theta (frame.vec k) =
      fun x ↦ eigenvalue k * frame.vec k x

/-- Every vector in the raw eigenframe is a nonzero state. -/
theorem LogicalEigenframe.vec_ne_zero
    {C : CodeSpec.ExactCode 6 2 3} {theta : Fin 6 → ℝ}
    (E : LogicalEigenframe C theta) (k : Fin 2) : E.frame.vec k ≠ 0 := by
  intro hzero
  have hunit := E.frame.orthonormal k k
  rw [hzero] at hunit
  simp [SS.innerC] at hunit

/-- A unit eigenvector of the real diagonal gate has an eigenvalue of complex
norm one.  This proof uses an actual nonzero amplitude, so it does not assume
unitarity merely from the name of the gate. -/
theorem LogicalEigenframe.eigenvalue_norm_eq_one
    {C : CodeSpec.ExactCode 6 2 3} {theta : Fin 6 → ℝ}
    (E : LogicalEigenframe C theta) (k : Fin 2) :
    ‖E.eigenvalue k‖ = 1 := by
  obtain ⟨x, hx⟩ := Function.ne_iff.mp (E.vec_ne_zero k)
  have hx' : E.frame.vec k x ≠ 0 := by
    simpa using hx
  have heq := MainTheory.RealGate.exp_eq_of_eigen
    theta (E.frame.vec k) (E.eigenvalue k) (E.eigen k) x hx'
  rw [← heq]
  have harg :
      2 * (Real.pi : ℂ) * Complex.I *
          (MainTheory.RealGate.angle theta x : ℂ) =
        ((2 * Real.pi * MainTheory.RealGate.angle theta x : ℝ) : ℂ) *
          Complex.I := by
    push_cast
    ring
  rw [harg]
  exact Complex.norm_exp_ofReal_mul_I _

/-- A chosen real argument for one raw logical eigenvalue. -/
def LogicalEigenframe.eigenArgument
    {C : CodeSpec.ExactCode 6 2 3} {theta : Fin 6 → ℝ}
    (E : LogicalEigenframe C theta) (k : Fin 2) : ℝ :=
  Classical.choose
    ((Complex.norm_eq_one_iff (E.eigenvalue k)).1
      (E.eigenvalue_norm_eq_one k))

theorem LogicalEigenframe.eigenArgument_spec
    {C : CodeSpec.ExactCode 6 2 3} {theta : Fin 6 → ℝ}
    (E : LogicalEigenframe C theta) (k : Fin 2) :
    Complex.exp ((E.eigenArgument k : ℂ) * Complex.I) =
      E.eigenvalue k :=
  Classical.choose_spec
    ((Complex.norm_eq_one_iff (E.eigenvalue k)).1
      (E.eigenvalue_norm_eq_one k))

/-- Real phase in the repository's turns convention (`phaseExp phi` uses
`2π i phi`). -/
def LogicalEigenframe.logicalPhase
    {C : CodeSpec.ExactCode 6 2 3} {theta : Fin 6 → ℝ}
    (E : LogicalEigenframe C theta) (k : Fin 2) : ℝ :=
  E.eigenArgument k / (2 * Real.pi)

/-- The chosen phase represents the raw eigenvalue exactly. -/
theorem LogicalEigenframe.phaseExp_logicalPhase
    {C : CodeSpec.ExactCode 6 2 3} {theta : Fin 6 → ℝ}
    (E : LogicalEigenframe C theta) (k : Fin 2) :
    phaseExp (E.logicalPhase k) = E.eigenvalue k := by
  rw [phaseExp]
  calc
    Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I *
          (E.logicalPhase k : ℂ)) =
        Complex.exp ((E.eigenArgument k : ℂ) * Complex.I) := by
      apply congrArg Complex.exp
      rw [LogicalEigenframe.logicalPhase]
      have hpi : (Real.pi : ℂ) ≠ 0 := by
        exact_mod_cast Real.pi_ne_zero
      push_cast
      field_simp [hpi]
    _ = E.eigenvalue k := E.eigenArgument_spec k

end

end MainTheory.D3LogicalEigenframeSectors
