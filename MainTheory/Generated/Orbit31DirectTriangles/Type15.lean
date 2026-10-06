import MainTheory.Generated.Orbit31PrintedSupportOrbits
import MainTheory.Orbit31PhysicalSupportFilters
import MainTheory.Orbit31PermanentAlgebra

/-! Actual signed-phase propagation for the literal SI support type 15.
Every path is checked in the actual support graph; no final no-go is used. -/
set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 1000000
namespace MainTheory.Generated.Orbit31DirectTriangles.Type15
open MainTheory.Orbit31PhaseRatios
open MainTheory.Orbit31CanonicalPhase
open MainTheory.Orbit31SignedSupport
open MainTheory.Orbit31PermanentAlgebra
open MainTheory.SignedPhaseSupport
open scoped BigOperators
noncomputable section
def mask : ℕ := 61439
def anchor : Fin 16 := ⟨0,by decide⟩
def colors : Fin 16 → Bool := ![false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true]
def reached : Fin 16 → Bool := ![true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,true]
def paths : Fin 16 → List (Bool × Fin 16) := ![[],[(false,⟨13,by decide⟩),(true,⟨4,by decide⟩),(false,⟨0,by decide⟩)],[(false,⟨14,by decide⟩),(true,⟨4,by decide⟩),(false,⟨0,by decide⟩)],[(false,⟨15,by decide⟩),(true,⟨4,by decide⟩),(false,⟨0,by decide⟩)],[(false,⟨0,by decide⟩)],[(false,⟨1,by decide⟩),(false,⟨13,by decide⟩),(true,⟨4,by decide⟩),(false,⟨0,by decide⟩)],[(false,⟨2,by decide⟩),(false,⟨14,by decide⟩),(true,⟨4,by decide⟩),(false,⟨0,by decide⟩)],[(false,⟨3,by decide⟩),(false,⟨15,by decide⟩),(true,⟨4,by decide⟩),(false,⟨0,by decide⟩)],[(false,⟨0,by decide⟩)],[(false,⟨1,by decide⟩),(false,⟨13,by decide⟩),(true,⟨4,by decide⟩),(false,⟨0,by decide⟩)],[(false,⟨2,by decide⟩),(false,⟨14,by decide⟩),(true,⟨4,by decide⟩),(false,⟨0,by decide⟩)],[(false,⟨3,by decide⟩),(false,⟨15,by decide⟩),(true,⟨4,by decide⟩),(false,⟨0,by decide⟩)],[],[(true,⟨4,by decide⟩),(false,⟨0,by decide⟩)],[(true,⟨4,by decide⟩),(false,⟨0,by decide⟩)],[(true,⟨4,by decide⟩),(false,⟨0,by decide⟩)]]
theorem printed_binding : mask =
    (MainTheory.Generated.Orbit31PrintedSupportOrbits.representatives ⟨14,by decide⟩).val := by decide +kernel
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

theorem permanent_0 {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d)
    (hs : CrossSystem c d) (hm : AmplitudeSupport mask c) :
    permanent c ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩=0 := by
  have he := rectangle_phase hp hs ⟨0,by decide⟩ ⟨3,by decide⟩
  dsimp only at he
  norm_num [rowPairs,colPairs,B,Fin.succ] at he
  have hp0 := phase_pattern hp hs hm ⟨5,by decide⟩ (by decide +kernel)
  have hp1 := phase_pattern hp hs hm ⟨10,by decide⟩ (by decide +kernel)
  have hp2 := phase_pattern hp hs hm ⟨6,by decide⟩ (by decide +kernel)
  have hp3 := phase_pattern hp hs hm ⟨9,by decide⟩ (by decide +kernel)
  simp only [hp0,hp1,hp2,hp3] at he
  norm_num [colors,sign,Fin.succ] at he
  have hf : (2 : ℂ)*sigma c d anchor*permanent c ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩=0 := by
    unfold permanent
    conv_lhs => norm_num [B,Fin.succ]
    linear_combination (-1 : ℂ)*he
  exact (mul_eq_zero.mp hf).resolve_left (mul_ne_zero (by norm_num) (anchor_nonzero hp hm))

theorem permanent_1 {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d)
    (hs : CrossSystem c d) (hm : AmplitudeSupport mask c) :
    permanent c ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩=0 := by
  have he := rectangle_phase hp hs ⟨1,by decide⟩ ⟨3,by decide⟩
  dsimp only at he
  norm_num [rowPairs,colPairs,B,Fin.succ] at he
  have hp0 := phase_pattern hp hs hm ⟨5,by decide⟩ (by decide +kernel)
  have hp1 := phase_pattern hp hs hm ⟨14,by decide⟩ (by decide +kernel)
  have hp2 := phase_pattern hp hs hm ⟨6,by decide⟩ (by decide +kernel)
  have hp3 := phase_pattern hp hs hm ⟨13,by decide⟩ (by decide +kernel)
  simp only [hp0,hp1,hp2,hp3] at he
  norm_num [colors,sign,Fin.succ] at he
  have hf : (2 : ℂ)*sigma c d anchor*permanent c ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩=0 := by
    unfold permanent
    conv_lhs => norm_num [B,Fin.succ]
    linear_combination (-1 : ℂ)*he
  exact (mul_eq_zero.mp hf).resolve_left (mul_ne_zero (by norm_num) (anchor_nonzero hp hm))

theorem permanent_2 {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d)
    (hs : CrossSystem c d) (hm : AmplitudeSupport mask c) :
    permanent c ⟨1,by decide⟩ ⟨2,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩=0 := by
  have he := rectangle_phase hp hs ⟨2,by decide⟩ ⟨3,by decide⟩
  dsimp only at he
  norm_num [rowPairs,colPairs,B,Fin.succ] at he
  have hp0 := phase_pattern hp hs hm ⟨9,by decide⟩ (by decide +kernel)
  have hp1 := phase_pattern hp hs hm ⟨14,by decide⟩ (by decide +kernel)
  have hp2 := phase_pattern hp hs hm ⟨10,by decide⟩ (by decide +kernel)
  have hp3 := phase_pattern hp hs hm ⟨13,by decide⟩ (by decide +kernel)
  simp only [hp0,hp1,hp2,hp3] at he
  norm_num [colors,sign,Fin.succ] at he
  have hf : (2 : ℂ)*sigma c d anchor*permanent c ⟨1,by decide⟩ ⟨2,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩=0 := by
    unfold permanent
    conv_lhs => norm_num [B,Fin.succ]
    linear_combination (-1 : ℂ)*he
  exact (mul_eq_zero.mp hf).resolve_left (mul_ne_zero (by norm_num) (anchor_nonzero hp hm))

theorem no_go {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d)
    (hs : CrossSystem c d) (hm : AmplitudeSupport mask c) : False := by
  apply odd_permanent_triangle (fun i => c (B i ⟨1,by decide⟩)) (fun i => c (B i ⟨2,by decide⟩))
  · intro i
    fin_cases i <;> exact (hm _).mp (by decide +kernel)
  · intro i
    fin_cases i <;> exact (hm _).mp (by decide +kernel)
  · exact permanent_0 hp hs hm
  · exact permanent_1 hp hs hm
  · exact permanent_2 hp hs hm

theorem physical_no_go (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit31.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit31.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3)
    (hm : AmplitudeSupport mask (C c)) : False :=
  no_go (physical_equal_probabilities c d hc hd hnc hnd hkl)
    (MainTheory.Orbit31PhysicalSupportFilters.physical_cross_system c d hc hd hkl) hm

end
end MainTheory.Generated.Orbit31DirectTriangles.Type15
