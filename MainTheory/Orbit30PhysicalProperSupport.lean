import MainTheory.Orbit30PhysicalMask
import MainTheory.Orbit30ProperGraphExclusion
import MainTheory.Orbit30PhysicalFullSupport
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit30PhysicalProperSupport
open MainTheory.Orbit30PhysicalMask MainTheory.Orbit30ProperGraphExclusion
open MainTheory.Orbit30PhysicalRows MainTheory.Orbit30PhysicalHafnians
open MainTheory.Orbit30GraphMaskEncoding MainTheory.Orbit30GraphClassification
open SixQubit.Orbit30
noncomputable section

theorem literal_hafnians (c : SS.State 6 ℂ) (i : Fin 5) :
    MainTheory.Orbit30ProperGraphTables.hafnian (amplitudes c) i=
      MainTheory.Orbit30VertexScaling.hafnian (edgeMatrix c) i := by
  fin_cases i <;> simp +decide [MainTheory.Orbit30ProperGraphTables.hafnian,
    MainTheory.Orbit30VertexScaling.hafnian,amplitudes,endpoints,edgeMatrix,
    edgeC,edgeIndexMatrix]

theorem actual_missing (c : SS.State 6 ℂ) :
    MainTheory.Orbit30ProperGraphTables.Missing (amplitudes c) (mask c) := by
  classical
  intro e
  have h := decoded (zeroPattern c) e
  change Nat.testBit (mask c).val e.val=zeroPattern c e at h
  rw [h]
  simp [zeroPattern]

variable (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1) (hkl : SS.HasDistance ![c,d] 3)
include hc hd hnc hnd hkl in
theorem actual_proper_support_no_go (hp : ∃ i j,i≠j ∧ edgeC c i j=0) : False := by
  apply proper_no_go (amplitudes c) (mask c)
    (actual_admissible c d hc hd hnc hnd hkl hp) (actual_missing c)
  intro i
  rw [literal_hafnians]
  exact actual_hafnians c d hc hd hnc hnd hkl i

include hc hd hnc hnd hkl in
theorem physical_printed_no_go : False := by
  classical
  by_cases hf : ∀ i j : Fin 5,i≠j → edgeC c i j≠0
  · exact MainTheory.Orbit30PhysicalFullSupport.actual_full_support_no_go c d hc hd hnc hnd hkl hf
  · push_neg at hf
    exact actual_proper_support_no_go c d hc hd hnc hnd hkl hf
end
end MainTheory.Orbit30PhysicalProperSupport
