import SixQubit.Orbit36Class

set_option autoImplicit false

namespace MainTheory.Orbit36Antiunitary

open SixQubit.Orbit36 SixQubit.Orbit36Enum

def theta (c : SS.State 6 ℂ) (x : SS.BitString 6) : ℂ :=
  SS.signC (Bool.xor (x 4) (x 5)) (star (c (SS.complement x)))

def xAll : SS.PauliString 6 := ⟨fun _ => true, fun _ => false⟩
def zLastTwo : SS.PauliString 6 := ⟨fun _ => false, ![false,false,false,false,true,true]⟩

theorem physical_action (c : SS.State 6 ℂ) :
    theta c = SS.pauliAct zLastTwo (SS.pauliAct xAll (fun x => star (c x))) := by
  have hx : xAll.numY = 0 := by decide
  have hz : zLastTwo.numY = 0 := by decide
  have hxx : ∀ x : SS.BitString 6, SS.bxor x xAll.x = SS.complement x := by decide
  have hzz : ∀ x : SS.BitString 6, SS.bxor x zLastTwo.x = x := by decide
  have hb0 : ∀ x : SS.BitString 6, SS.bdot xAll.z x = false := by decide
  have hb : ∀ x : SS.BitString 6, SS.bdot zLastTwo.z x = Bool.xor (x 4) (x 5) := by decide
  funext x
  simp only [theta, SS.pauliAct, hx, hz, hzz, hxx, hb0, hb, pow_zero, one_mul,
    SS.signC_false]

theorem complement_mem_iff : ∀ x : SS.BitString 6, SS.complement x ∈ S0 ↔ x ∈ S1 := by decide

theorem topForm_one_eq_theta (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (h : TopForm c d 1) : d = theta c := by
  funext x
  by_cases hx : x ∈ S1
  · simp only [S1, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [h.t0,h.t1,h.t2,h.t3,h.t4,h.t5,h.t6,h.t7,h.t8,h.t9,h.t10,h.t11, one_mul]
    all_goals simp only [theta, zc0,zc1,zc2,zc3,zc4,zc5,zc6,zc7,zc8,zc9,zc10,zc11,
      SS.complement_complement]
    all_goals simp [SS.signC, SS.complement, y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11, bs]
  · have hc0 : c (SS.complement x) = 0 := hc _ (fun hm => hx ((complement_mem_iff x).mp hm))
    simp [hd x hx, theta, hc0, SS.signC]

theorem canonical_top : SixQubit.Orbit36Code.d36 = theta SixQubit.Orbit36Code.c36 := by
  apply topForm_one_eq_theta
  · intro x hx
    exact SixQubit.Orbit36Code.c36_vanishes_off_S0 x (by simpa [SixQubit.Orbit36Class.S0_eq] using hx)
  · intro x hx
    exact SixQubit.Orbit36Code.d36_vanishes_off_S1 x (by simpa [SixQubit.Orbit36Class.S1_eq] using hx)
  · exact SixQubit.Orbit36Class.canonical_topForm

end MainTheory.Orbit36Antiunitary
