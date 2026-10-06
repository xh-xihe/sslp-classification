import MainTheory.FiniteGateAsPhase
import MainTheory.IntrinsicClassBridge
import MainTheory.IntrinsicTransport

/-!
# Projective agreement of finite gates gives equal intrinsic classes

The entrance states its conclusions as `CodeSpec.SameProjectiveOnCode` between
`Module.End` objects.  `MainTheory/IntrinsicClassBridge.lean` states the class
equality in terms of `diagonalAction` on the projector range.  With
`FiniteGateAsPhase.gate_eq_diagonalAction` and
`GlobalClassificationBridge.inProjectorRange_ofFrame_iff` the two descriptions
are the same, and this file records the resulting bridge.

It is the step that turns the entrance's projective statements into equalities
in the level-(i) quotient, which is what the bounded-lift cover is about.
-/

namespace MainTheory.SameProjectiveClass

variable {n d : ℕ}

open MainTheory.ClassificationLevels
open MainTheory.FiniteGateAsPhase

variable {q r : ℕ} [NeZero q] [NeZero r]

/-- **Projective agreement on the code is equality of intrinsic classes.**

Stated for finite gates, which is the form the entrance produces. -/
theorem intrinsicClass_eq_of_sameProjective
    (F : CodeSpec.OrthonormalFrame n 2)
    (zeta : ℂ) (hz : zeta ^ q = 1) (a : Fin n → ZMod q)
    (xi : ℂ) (hx : xi ^ r = 1) (b : Fin n → ZMod r)
    (hu : phaseOfAngle zeta hz a ∈ diagonalSymmetryGroup (CodeProjector.ofFrame F))
    (hv : phaseOfAngle xi hx b ∈ diagonalSymmetryGroup (CodeProjector.ofFrame F))
    (h : CodeSpec.SameProjectiveOnCode F
      (RankTwoGlobal.finiteGateEnd zeta a) (RankTwoGlobal.finiteGateEnd xi b)) :
    intrinsicClass (CodeProjector.ofFrame F) ⟨phaseOfAngle zeta hz a, hu⟩
      = intrinsicClass (CodeProjector.ofFrame F) ⟨phaseOfAngle xi hx b, hv⟩ := by
  obtain ⟨lam, hlam, hact⟩ := h
  refine IntrinsicClassBridge.intrinsicClass_eq_of_sameProjective
    (CodeProjector.ofFrame F) _ _ lam hlam (fun phi hphi => ?_)
  have hmem : phi ∈ CodeSpec.codeSpan F :=
    (GlobalClassificationBridge.inProjectorRange_ofFrame_iff F phi).1 hphi
  have hthis := hact phi hmem
  simp only [RankTwoGlobal.finiteGateEnd, LinearMap.coe_mk, AddHom.coe_mk] at hthis
  rw [gate_eq_diagonalAction zeta hz a phi, gate_eq_diagonalAction xi hx b phi] at hthis
  exact hthis

end MainTheory.SameProjectiveClass
