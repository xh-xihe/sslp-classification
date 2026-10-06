import MainTheory.D3LogicalNormalizedFrame
import MainTheory.D3LogicalEigenframeGrouping

/-!
# Automatic spectral extraction on the logical two-space

This file closes the ordinary spectral-linear-algebra gap.  A first nonzero
eigenvector of the concrete two-dimensional logical action is supplied by
algebraic closedness of `ℂ`.  Inner-product preservation makes its explicit
perpendicular a second eigenvector.  After normalization and synthesis, the
two vectors form an orthonormal physical eigenframe with exactly the original
code span.  The already certified grouping construction then yields a full
`LogicalSectorResolution`.

There is no spectral-extraction premise in the final theorem of this file.
-/

namespace MainTheory.D3LogicalSpectralExtraction

open MainTheory
open MainTheory.D3LogicalCoordinateUnitary
open MainTheory.D3LogicalNormalization
open MainTheory.D3LogicalNormalizedFrame

noncomputable section

/-- Scaling an eigenvector by the explicit normalization scalar preserves its
logical eigenvalue. -/
theorem logicalAction_normalized_eigen
    (F : CodeSpec.OrthonormalFrame 6 2) (theta : Fin 6 → ℝ)
    {mu : ℂ} {v : Fin 2 → ℂ}
    (heigen : D3LogicalAction.logicalAction F
      (PhaseSectorBridge.realGateEnd theta) v = mu • v) :
    D3LogicalAction.logicalAction F
        (PhaseSectorBridge.realGateEnd theta) (normalized v) =
      mu • normalized v := by
  unfold normalized
  rw [map_smul, heigen]
  simp only [smul_smul]
  rw [mul_comm]

/-- A logical coordinate eigenvector synthesizes to a physical eigenstate of
the real diagonal gate. -/
theorem realGate_synthesis_eigen
    (F : CodeSpec.OrthonormalFrame 6 2) (theta : Fin 6 → ℝ)
    (hpres : CodeSpec.CodePreserving F
      (PhaseSectorBridge.realGateEnd theta))
    {lambda : ℂ} {u : Fin 2 → ℂ}
    (heigen : D3LogicalAction.logicalAction F
      (PhaseSectorBridge.realGateEnd theta) u = lambda • u) :
    MainTheory.RealGate.realGate theta
        (D3LogicalAction.synthesisLinear F u) =
      fun x ↦ lambda * D3LogicalAction.synthesisLinear F u x := by
  calc
    MainTheory.RealGate.realGate theta
        (D3LogicalAction.synthesisLinear F u) =
        PhaseSectorBridge.realGateEnd theta
          (D3LogicalAction.synthesisLinear F u) := rfl
    _ = D3LogicalAction.synthesisLinear F
          (D3LogicalAction.logicalAction F
            (PhaseSectorBridge.realGateEnd theta) u) :=
      (D3LogicalAction.synthesis_logicalAction F
        (PhaseSectorBridge.realGateEnd theta) hpres u).symm
    _ = D3LogicalAction.synthesisLinear F (lambda • u) := by
      rw [heigen]
    _ = lambda • D3LogicalAction.synthesisLinear F u := by
      rw [map_smul]
    _ = fun x ↦ lambda * D3LogicalAction.synthesisLinear F u x := by
      funext x
      simp [smul_eq_mul]

/-- Every preserving six-qubit real diagonal gate has a raw orthonormal
logical eigenframe spanning the exact code. -/
theorem exists_logicalEigenframe
    (C : CodeSpec.ExactCode 6 2 3) (theta : Fin 6 → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta)) :
    Nonempty
      (D3LogicalEigenframeSectors.LogicalEigenframe C theta) := by
  obtain ⟨mu, v, hv, heigen⟩ :=
    D3LogicalAction.exists_logical_eigenvector C.frame
      (PhaseSectorBridge.realGateEnd theta)
  obtain ⟨nu, hnu⟩ :=
    D3LogicalSecondEigenvector.perpendicular_is_logical_eigenvector
      C.frame theta hpres hv heigen
  refine ⟨
    { frame := normalizedPhysicalFrame C.frame v hv
      span_eq := codeSpan_normalizedPhysicalFrame C.frame v hv
      eigenvalue := ![mu, nu]
      eigen := ?_ }⟩
  intro k
  fin_cases k
  · change MainTheory.RealGate.realGate theta
        (D3LogicalAction.synthesisLinear C.frame (normalized v)) =
      fun x ↦ mu * D3LogicalAction.synthesisLinear C.frame (normalized v) x
    exact realGate_synthesis_eigen C.frame theta hpres
      (logicalAction_normalized_eigen C.frame theta heigen)
  · change MainTheory.RealGate.realGate theta
        (D3LogicalAction.synthesisLinear C.frame
          (normalized (perpendicular v))) =
      fun x ↦ nu * D3LogicalAction.synthesisLinear C.frame
        (normalized (perpendicular v)) x
    exact realGate_synthesis_eigen C.frame theta hpres
      (logicalAction_normalized_eigen C.frame theta hnu)

/-- The formerly external raw-eigenframe extraction interface is now a
kernel theorem. -/
theorem logicalEigenframeExtraction :
    D3LogicalEigenframeGrouping.LogicalEigenframeExtractionPrinciple := by
  intro C theta hpres
  exact exists_logicalEigenframe C theta hpres

/-- Complete phase-sector extraction for every preserving real diagonal gate
on an exact six-qubit rank-two distance-three code. -/
theorem spectralExtraction :
    PhaseSectorBridge.SpectralExtractionPrinciple 6 2 3 :=
  D3LogicalEigenframeGrouping.spectralExtraction_of_logicalEigenframeExtraction
    logicalEigenframeExtraction

end

end MainTheory.D3LogicalSpectralExtraction
