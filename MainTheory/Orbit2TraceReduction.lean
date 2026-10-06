import SixQubit.ParityLogicalState
import MainTheory.OrderTwoScalarBridge

/-! # Physical trace zeros preceding the orbit-2 purity reduction

These are actual encoder statements: odd active transverse parity vanishes,
and every active-only Pauli containing at least two Z letters vanishes. No
flatness, auxiliary partial isometry or quartic certificate is assumed.
-/

namespace MainTheory.Orbit2TraceReduction

open MainTheory.OrderTwoScalarBridge MainTheory.CubeCompletionTransport
open MainTheory.DirectoryEnumeratorImages
open SixQubit.ParityPauliScalars SixQubit.ParityLogicalState SS.MacWilliams

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

abbrev Encoder := Completion (angleFibers SixQubit.OpenLOrbit2.angle)

def shift (P : SS.PauliString 6) : SS.PauliString 6 := ⟨P.x, SS.bxor P.z orbit2Mask⟩

theorem shifted_even_trace_zero (W : Encoder) (P : SS.PauliString 6)
    (hwt : P.wt ≤ 2) (heven : SS.bdot orbit2Mask P.x = false) :
    trProj W.states (shift P) = 0 := by
  have hc : chi orbit2Mask (shift P).x = 1 := by
    change chi orbit2Mask P.x = 1
    rw [chi_bdot, heven]
    rfl
  rw [trProj_eq, ← superposition_commuting W.states (orbit2_parity W) (shift P) hc]
  change Complex.I ^ (shift P).numY *
    mel (superposition W.states) (superposition W.states)
      ⟨P.x, SS.bxor P.z orbit2Mask⟩ = 0
  rw [superposition_twisted_kl_zero W.states (orbit2_parity W) P (W.hasDistance P hwt),
    mul_zero]

theorem shift_involution (P : SS.PauliString 6) : shift (shift P) = P := by
  cases P with
  | mk px pz =>
    change SS.PauliString.mk px (SS.bxor (SS.bxor pz orbit2Mask) orbit2Mask) = _
    rw [SS.bxor_assoc, SS.bxor_self, SS.bxor_zero]

def ActiveOnly (P : SS.PauliString 6) : Prop :=
  ∀ i : Fin 6, orbit2Mask i = false → P.x i = false ∧ P.z i = false

instance (P : SS.PauliString 6) : Decidable (ActiveOnly P) := by
  unfold ActiveOnly
  infer_instance

def activeZCount (P : SS.PauliString 6) : ℕ :=
  (Finset.univ.filter (fun i => orbit2Mask i = true ∧ P.x i = false ∧ P.z i = true)).card

theorem shifted_weight_bound : ∀ P : SS.PauliString 6,
    ActiveOnly P → 2 ≤ activeZCount P → (shift P).wt ≤ 2 := by
  decide +kernel

theorem active_many_Z_trace_zero (W : Encoder) (P : SS.PauliString 6)
    (hs : ActiveOnly P) (hz : 2 ≤ activeZCount P) : trProj W.states P = 0 := by
  cases hp : SS.bdot orbit2Mask P.x
  · have h := shifted_even_trace_zero W (shift P) (shifted_weight_bound P hs hz) hp
    rw [shift_involution] at h
    exact h
  · apply odd_trace_zero (orbit2_parity W) P
    rw [chi_bdot, hp]
    rfl

end MainTheory.Orbit2TraceReduction
