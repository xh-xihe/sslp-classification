import MainTheory.D3LogicalPerpSpan

/-!
# The second logical eigenvector

For the concrete two-dimensional logical action induced by a preserving real
diagonal gate, this file turns one nonzero eigenvector into a second one.  The
proof uses only injectivity of the physical gate, preservation of the exact
coordinate Hermitian product, and the explicit description of the
one-dimensional orthogonal complement.
-/

namespace MainTheory.D3LogicalSecondEigenvector

variable {n d : ℕ}

open MainTheory
open MainTheory.D3LogicalCoordinateUnitary
open MainTheory.D3LogicalPerpSpan
open scoped BigOperators ComplexConjugate

noncomputable section

/-- Conjugate-linearity of the coordinate product in its first input. -/
theorem coordinateInner_smul_left (a : ℂ) (v z : Fin 2 → ℂ) :
    coordinateInner (a • v) z = star a * coordinateInner v z := by
  simp [coordinateInner, Fin.sum_univ_two, smul_eq_mul]
  ring

/-- The induced logical action is injective because synthesis and the
physical real diagonal gate are both injective. -/
theorem logicalAction_realGate_injective
    (F : CodeSpec.OrthonormalFrame n 2) (theta : Fin n → ℝ)
    (hpres : CodeSpec.CodePreserving F
      (PhaseSectorBridge.realGateEnd theta)) :
    Function.Injective
      (D3LogicalAction.logicalAction F
        (PhaseSectorBridge.realGateEnd theta)) := by
  intro v w hvw
  apply D3LogicalAction.synthesis_injective F
  apply D3RealGateUnitary.realGate_injective theta
  calc
    MainTheory.RealGate.realGate theta
        (D3LogicalAction.synthesisLinear F v) =
        D3LogicalAction.synthesisLinear F
          (D3LogicalAction.logicalAction F
            (PhaseSectorBridge.realGateEnd theta) v) := by
      symm
      simpa only [PhaseSectorBridge.realGateEnd_apply] using
        D3LogicalAction.synthesis_logicalAction F
          (PhaseSectorBridge.realGateEnd theta) hpres v
    _ = D3LogicalAction.synthesisLinear F
          (D3LogicalAction.logicalAction F
            (PhaseSectorBridge.realGateEnd theta) w) := by
      rw [hvw]
    _ = MainTheory.RealGate.realGate theta
        (D3LogicalAction.synthesisLinear F w) := by
      simpa only [PhaseSectorBridge.realGateEnd_apply] using
        D3LogicalAction.synthesis_logicalAction F
          (PhaseSectorBridge.realGateEnd theta) hpres w

/-- A nonzero logical eigenvector has nonzero eigenvalue for the induced
real-gate action. -/
theorem logical_eigenvalue_ne_zero
    (F : CodeSpec.OrthonormalFrame n 2) (theta : Fin n → ℝ)
    (hpres : CodeSpec.CodePreserving F
      (PhaseSectorBridge.realGateEnd theta))
    {mu : ℂ} {v : Fin 2 → ℂ} (hv : v ≠ 0)
    (heigen : D3LogicalAction.logicalAction F
      (PhaseSectorBridge.realGateEnd theta) v = mu • v) :
    mu ≠ 0 := by
  intro hmu
  apply hv
  apply logicalAction_realGate_injective F theta hpres
  have hzero : D3LogicalAction.logicalAction F
      (PhaseSectorBridge.realGateEnd theta) v = 0 := by
    simpa [hmu] using heigen
  simpa using hzero

/-- The explicit perpendicular vector is a second nonzero eigenvector of the
same logical action. -/
theorem perpendicular_is_logical_eigenvector
    (F : CodeSpec.OrthonormalFrame n 2) (theta : Fin n → ℝ)
    (hpres : CodeSpec.CodePreserving F
      (PhaseSectorBridge.realGateEnd theta))
    {mu : ℂ} {v : Fin 2 → ℂ} (hv : v ≠ 0)
    (heigen : D3LogicalAction.logicalAction F
      (PhaseSectorBridge.realGateEnd theta) v = mu • v) :
    ∃ nu : ℂ,
      D3LogicalAction.logicalAction F
          (PhaseSectorBridge.realGateEnd theta) (perpendicular v) =
        nu • perpendicular v := by
  let A := D3LogicalAction.logicalAction F
    (PhaseSectorBridge.realGateEnd theta)
  have himage : coordinateInner (A v) (A (perpendicular v)) = 0 := by
    change coordinateInner
        (D3LogicalAction.logicalAction F
          (PhaseSectorBridge.realGateEnd theta) v)
        (D3LogicalAction.logicalAction F
          (PhaseSectorBridge.realGateEnd theta) (perpendicular v)) = 0
    rw [coordinateInner_logicalAction_realGate F theta hpres]
    exact coordinateInner_perpendicular v
  have hfactor : star mu * coordinateInner v (A (perpendicular v)) = 0 := by
    rw [← coordinateInner_smul_left]
    rw [← heigen]
    exact himage
  have hstar : star mu ≠ 0 := by
    intro hs
    exact (logical_eigenvalue_ne_zero F theta hpres hv heigen)
      (star_eq_zero.mp hs)
  have horth : coordinateInner v (A (perpendicular v)) = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left hstar
  obtain ⟨nu, hnu⟩ :=
    eq_smul_perpendicular_of_coordinateInner_eq_zero hv horth
  exact ⟨nu, hnu⟩

end

end MainTheory.D3LogicalSecondEigenvector
