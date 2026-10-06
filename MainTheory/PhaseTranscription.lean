import MainTheory.FiniteGateAsPhase
import MainTheory.GlobalClassificationBridge

/-!
# Reconciling the two transcriptions of a finite angle vector

The repository builds the local phase of a finite angle vector twice: once as
`GlobalClassificationBridge.finiteLocalPhase`, through `Cyclic.chi`, and once
as `FiniteGateAsPhase.phaseOfAngle`, through `rootPower`.  They are the same
function.  Recording that here lets the symmetry-group membership already
proved for a resolved generator be reused verbatim for `phaseOfAngle`.
-/

namespace MainTheory.PhaseTranscription

open MainTheory.ClassificationLevels
open MainTheory.FiniteGateAsPhase

variable {n q : ℕ} [NeZero q]

/-- **The two transcriptions of a finite angle vector agree.**

`GlobalClassificationBridge.finiteLocalPhase` builds the local phase from
`Cyclic.chi`; `phaseOfAngle` builds it from `rootPower`.  Both are the
`(a j)`-th power of `zeta` at site `j`, so they are the same local phase.  This
lets the membership already proved for a resolved generator
(`FiniteGeneratorResolution.intrinsicSymmetry`) be used for `phaseOfAngle`. -/
theorem phaseOfAngle_eq_finiteLocalPhase (zeta : ℂ)
    (hzeta : IsPrimitiveRoot zeta q) (a : Fin n → ZMod q) :
    phaseOfAngle zeta hzeta.pow_eq_one a
      = GlobalClassificationBridge.finiteLocalPhase zeta hzeta a := by
  funext j
  refine Subtype.ext ?_
  simp [phaseOfAngle, GlobalClassificationBridge.coe_residueUnitary,
    GlobalClassificationBridge.finiteLocalPhase, Cyclic.chi]

end MainTheory.PhaseTranscription
