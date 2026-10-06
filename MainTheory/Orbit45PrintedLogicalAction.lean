import MainTheory.SixthRootCoefficients
import MainTheory.PhaseSector
import MainTheory.Orbit45PrintedFibers

/-! The literal sixth-root diagonal gate acts as logical Z on every
supported completion, including boundary supports. -/
set_option autoImplicit false
namespace MainTheory.Orbit45PrintedLogicalAction
open SixQubit.Orbit45Support
noncomputable section

theorem root_cube : SixthRootCoefficients.root^3= -1 := by
  simpa [SixthRootCoefficients.powers] using SixthRootCoefficients.power_formula ⟨3,by decide⟩

theorem physical_logical_action (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0) :
    Gate.gate SixthRootCoefficients.root av c=c ∧
    Gate.gate SixthRootCoefficients.root av d= -d := by
  have h0 : SS.SSConditionState av 0 c := by
    intro x hx
    have hm : x ∈ S0 := by by_contra hn; exact hx (hc x hn)
    rw [← S0_eq_fiber] at hm
    exact (Finset.mem_filter.mp hm).2
  have h1 : SS.SSConditionState av 3 d := by
    intro x hx
    have hm : x ∈ S1 := by by_contra hn; exact hx (hd x hn)
    rw [← S1_eq_fiber] at hm
    exact (Finset.mem_filter.mp hm).2
  have e0 := PhaseSector.eigen_of_ssCondition SixthRootCoefficients.root av c 0 h0
  have e1 := PhaseSector.eigen_of_ssCondition SixthRootCoefficients.root av d 3 h1
  constructor
  · simpa using e0
  · have hv : (3 : ZMod 6).val=3 := by decide +kernel
    rw [hv,root_cube] at e1
    simpa using e1
end
end MainTheory.Orbit45PrintedLogicalAction
