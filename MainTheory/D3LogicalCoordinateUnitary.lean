import MainTheory.D3RealGateUnitary

/-!
# The Hermitian structure on logical coordinates

The stored orthonormal code frame identifies `Fin 2 → ℂ` with the
physical code.  This file proves, in the kernel, that the identification
preserves the Hermitian product and that the logical action induced by the
real diagonal gate is therefore an isometry.  It also records the explicit
orthogonal-complement vector in complex dimension two.

No spectral decomposition is assumed here.
-/

namespace MainTheory.D3LogicalCoordinateUnitary

variable {n d : ℕ}

open MainTheory
open scoped BigOperators ComplexConjugate

noncomputable section

/-- The coordinate Hermitian product, conjugate-linear in its first input. -/
def coordinateInner (v w : Fin 2 → ℂ) : ℂ :=
  ∑ i, star (v i) * w i

/-- Expanding only the first synthesized vector against an arbitrary physical
state. -/
theorem innerC_synthesis_left
    (F : CodeSpec.OrthonormalFrame n 2) (v : Fin 2 → ℂ)
    (psi : SS.State n ℂ) :
    SS.innerC (D3LogicalAction.synthesisLinear F v) psi =
      ∑ i, star (v i) * SS.innerC (F.vec i) psi := by
  change SS.innerC (∑ i, v i • F.vec i) psi = _
  unfold SS.innerC
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, star_sum,
    star_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Synthesis by an orthonormal frame is an exact Hermitian isometry. -/
theorem innerC_synthesis
    (F : CodeSpec.OrthonormalFrame n 2) (v w : Fin 2 → ℂ) :
    SS.innerC (D3LogicalAction.synthesisLinear F v)
        (D3LogicalAction.synthesisLinear F w) =
      coordinateInner v w := by
  rw [innerC_synthesis_left]
  unfold coordinateInner
  apply Finset.sum_congr rfl
  intro i _
  have hi := congrFun (D3LogicalAction.analysis_synthesis F w) i
  change SS.innerC (F.vec i) (D3LogicalAction.synthesisLinear F w) = w i at hi
  rw [hi]

/-- The concrete logical action induced by a code-preserving real diagonal
gate preserves the coordinate Hermitian product. -/
theorem coordinateInner_logicalAction_realGate
    (F : CodeSpec.OrthonormalFrame n 2) (theta : Fin n → ℝ)
    (hpres : CodeSpec.CodePreserving F
      (PhaseSectorBridge.realGateEnd theta))
    (v w : Fin 2 → ℂ) :
    coordinateInner
        (D3LogicalAction.logicalAction F
          (PhaseSectorBridge.realGateEnd theta) v)
        (D3LogicalAction.logicalAction F
          (PhaseSectorBridge.realGateEnd theta) w) =
      coordinateInner v w := by
  calc
    coordinateInner
        (D3LogicalAction.logicalAction F
          (PhaseSectorBridge.realGateEnd theta) v)
        (D3LogicalAction.logicalAction F
          (PhaseSectorBridge.realGateEnd theta) w) =
        SS.innerC
          (D3LogicalAction.synthesisLinear F
            (D3LogicalAction.logicalAction F
              (PhaseSectorBridge.realGateEnd theta) v))
          (D3LogicalAction.synthesisLinear F
            (D3LogicalAction.logicalAction F
              (PhaseSectorBridge.realGateEnd theta) w)) :=
      (innerC_synthesis F _ _).symm
    _ = SS.innerC
        (PhaseSectorBridge.realGateEnd theta
          (D3LogicalAction.synthesisLinear F v))
        (PhaseSectorBridge.realGateEnd theta
          (D3LogicalAction.synthesisLinear F w)) := by
      rw [D3LogicalAction.synthesis_logicalAction F _ hpres v,
        D3LogicalAction.synthesis_logicalAction F _ hpres w]
    _ = SS.innerC (D3LogicalAction.synthesisLinear F v)
        (D3LogicalAction.synthesisLinear F w) := by
      simpa only [PhaseSectorBridge.realGateEnd_apply] using
        D3RealGateUnitary.innerC_realGate theta
          (D3LogicalAction.synthesisLinear F v)
          (D3LogicalAction.synthesisLinear F w)
    _ = coordinateInner v w := innerC_synthesis F v w

/-- The canonical orthogonal-complement vector to `(v₀,v₁)` in
complex dimension two. -/
def perpendicular (v : Fin 2 → ℂ) : Fin 2 → ℂ :=
  ![-star (v 1), star (v 0)]

/-- The explicit complement is Hermitian-orthogonal to the original vector. -/
@[simp] theorem coordinateInner_perpendicular (v : Fin 2 → ℂ) :
    coordinateInner v (perpendicular v) = 0 := by
  simp [coordinateInner, perpendicular, Fin.sum_univ_two]
  ring

/-- The complement of a nonzero vector is nonzero. -/
theorem perpendicular_ne_zero {v : Fin 2 → ℂ} (hv : v ≠ 0) :
    perpendicular v ≠ 0 := by
  intro hp
  apply hv
  funext i
  fin_cases i
  · have h := congrFun hp 1
    simp [perpendicular] at h
    exact h
  · have h := congrFun hp 0
    simp [perpendicular] at h
    exact h

/-- Taking the complement preserves the squared coordinate norm. -/
theorem coordinateInner_perpendicular_self (v : Fin 2 → ℂ) :
    coordinateInner (perpendicular v) (perpendicular v) =
      coordinateInner v v := by
  simp [coordinateInner, perpendicular, Fin.sum_univ_two]
  ring

end

end MainTheory.D3LogicalCoordinateUnitary
