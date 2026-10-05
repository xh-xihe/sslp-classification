import MainTheory.Generated.Orbit31PrintedSupportOrbits
import MainTheory.Orbit31PhysicalSupportFilters
import MainTheory.Orbit31PermanentAlgebra

/-! Actual signed-phase propagation for the literal SI support type 1.
Every path is checked in the actual support graph; no final no-go is used. -/
set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 1000000
namespace MainTheory.Generated.Orbit31DirectTriangles.Type01
open MainTheory.Orbit31PhaseRatios
open MainTheory.Orbit31CanonicalPhase
open MainTheory.Orbit31SignedSupport
open MainTheory.Orbit31PermanentAlgebra
open MainTheory.SignedPhaseSupport
open scoped BigOperators
noncomputable section
def mask : ℕ := 52284
def anchor : Fin 16 := ⟨2,by decide⟩
def colors : Fin 16 → Bool := ![false,false,false,false,true,true,false,false,false,false,false,false,false,false,false,false]
def reached : Fin 16 → Bool := ![false,false,true,true,true,true,false,false,false,false,true,true,false,false,true,true]
def paths : Fin 16 → List (Bool × Fin 16) := ![[],[],[],[(false,⟨11,by decide⟩),(true,⟨4,by decide⟩),(true,⟨10,by decide⟩),(false,⟨2,by decide⟩)],[(true,⟨10,by decide⟩),(false,⟨2,by decide⟩)],[(true,⟨10,by decide⟩),(false,⟨2,by decide⟩)],[],[],[],[],[(false,⟨2,by decide⟩)],[(true,⟨4,by decide⟩),(true,⟨10,by decide⟩),(false,⟨2,by decide⟩)],[],[],[(false,⟨2,by decide⟩)],[(true,⟨4,by decide⟩),(true,⟨10,by decide⟩),(false,⟨2,by decide⟩)]]
theorem printed_binding : mask =
    (MainTheory.Generated.Orbit31PrintedSupportOrbits.representatives ⟨0,by decide⟩).val := by decide +kernel
theorem checked : ∀ v, reached v=true →
    ValidWalk (edges mask) v (paths v) ∧
    finish v (paths v)=anchor ∧ parity (paths v)=colors v := by decide +kernel

theorem phase_pattern {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d)
    (hs : CrossSystem c d) (hm : AmplitudeSupport mask c) (v : Fin 16)
    (hv : reached v=true) : sigma c d v = sign (colors v) (sigma c d anchor) := by
  have hw := checked v hv
  have he := walk_equation (graph_assignment hp hs hm) hw.1
  rw [hw.2.1,hw.2.2] at he
  exact he

theorem anchor_nonzero {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d)
    (hm : AmplitudeSupport mask c) : sigma c d anchor ≠ 0 :=
  nonzero hp ((hm anchor).mp (by decide +kernel))

end
end MainTheory.Generated.Orbit31DirectTriangles.Type01
