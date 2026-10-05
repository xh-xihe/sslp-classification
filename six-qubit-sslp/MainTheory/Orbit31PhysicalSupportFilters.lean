import MainTheory.Orbit31CrossConsequences
import MainTheory.Orbit31CanonicalPhase

/-! Actual normalized complex codewords satisfy both support-audit filters.
All canonical cross equations come from weight-at-most-two physical Paulis.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit31PhysicalSupportFilters
open MainTheory.MatrixPositiveSupportCertificates
open MainTheory.Orbit31SupportBase (probabilities)
open MainTheory.Orbit31SupportSemantics (maskSet mem_maskSet)
open MainTheory.Orbit31PhaseRatios
open MainTheory.Orbit31SignedSupport
open MainTheory.Orbit31CanonicalPhase
open MainTheory.SignedPhaseSupport
open SixQubit.Orbit31
noncomputable section

theorem physical_cross_system (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hkl : SS.HasDistance ![c,d] 3) : CrossSystem (C c) (D d) :=
  ⟨MainTheory.Orbit31CrossConsequences.physical_reciprocal c d hc hd hkl,
    MainTheory.Orbit31CrossConsequences.physical_weight_one_sum c d hc hd hkl,
    MainTheory.Orbit31CrossConsequences.physical_rectangles c d hc hd hkl⟩

theorem amplitude_support_of_probability_support (c : SS.State 6 ℂ) (mask : ℕ)
    (hs : ExactSupport (maskSet mask) (probabilities c)) : AmplitudeSupport mask (C c) := by
  intro v
  change mask.testBit v.val = true ↔ C c v ≠ 0
  rw [← mem_maskSet,← hs v]
  exact Complex.normSq_pos

theorem physical_filters (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hkl : SS.HasDistance ![c,d] 3) (mask : ℕ)
    (hm : ExactSupport (maskSet mask) (probabilities c)) :
    NoSingleton mask ∧ Assignment (maskSet mask) (edges mask) (sigma (C c) (D d)) := by
  have hp := physical_equal_probabilities c d hc hd hnc hnd hkl
  have hs := physical_cross_system c d hc hd hkl
  have ha := amplitude_support_of_probability_support c mask hm
  exact ⟨no_singleton hp hs ha,graph_assignment hp hs ha⟩

theorem physical_graph_compatible (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hkl : SS.HasDistance ![c,d] 3) (mask : ℕ)
    (hm : ExactSupport (maskSet mask) (probabilities c)) : GraphCompatible mask :=
  ⟨sigma (C c) (D d),(physical_filters c d hc hd hnc hnd hkl mask hm).2⟩

end
end MainTheory.Orbit31PhysicalSupportFilters
