import MainTheory.CitedFamilyOneBody
import SixQubit.MacWilliams

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace MainTheory.CitedConstructionAlpha

open SixQubit.Realize SS.MacWilliams MainTheory.CitedAncillaFamily MainTheory.CitedFamilyOneBody

def ancillaZ : SS.PauliString 6 := ⟨nbit 0,nbit 32⟩

theorem ancilla_weight : ancillaZ.wt=1 := by decide +kernel

theorem mask_iff (P : SS.PauliString 6) : num P.x=0 ∧ num P.z=32 ↔ P=ancillaZ := by
  constructor
  · intro h
    have hx : P.x=ancillaZ.x := by
      change P.x=nbit 0
      simpa only [h.1] using (nbit_num P.x).symm
    have hz : P.z=ancillaZ.z := by
      change P.z=nbit 32
      simpa only [h.2] using (nbit_num P.z).symm
    cases P
    cases hx
    cases hz
    rfl
  · rintro rfl
    decide +kernel

theorem trace_single (theta : ℝ) (P : SS.PauliString 6) (hw : P.wt=1) :
    trProj (code theta) P=if num P.x=0 ∧ num P.z=32 then 2*(Real.cos theta : ℂ) else 0 := by
  simp only [trProj,Fin.sum_univ_two,family_single theta P hw]
  by_cases h : num P.x=0 ∧ num P.z=32 <;>
    simp only [and_true,h,if_true,if_false,zero_add,two_mul]

theorem raw_A1 (theta : ℝ) : Aco (code theta) 1=4*Real.cos theta^2 := by
  classical
  unfold Aco
  rw [Finset.sum_eq_single ancillaZ]
  · rw [trace_single theta ancillaZ ancilla_weight,if_pos ((mask_iff ancillaZ).2 rfl)]
    rw [Complex.normSq_mul,Complex.normSq_ofReal]
    norm_num
    ring
  · intro P hP hne
    have hw := (Finset.mem_filter.mp hP).2
    rw [trace_single theta P hw,if_neg (fun h => hne ((mask_iff P).1 h))]
    simp
  · intro h
    exact False.elim (h (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ancilla_weight⟩))

theorem alpha (theta : ℝ) : Aco (code theta) 1/4=Real.cos theta^2 := by
  rw [raw_A1]
  ring

theorem normalized (theta : ℝ) (i : Fin 2) : SS.innerC (code theta i) (code theta i)=1 := by
  simpa using family_gram theta i i

end MainTheory.CitedConstructionAlpha
