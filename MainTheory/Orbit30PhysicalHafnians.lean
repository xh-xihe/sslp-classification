import MainTheory.Orbit30PhysicalGraph
import MainTheory.Orbit30VertexScaling
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit30PhysicalHafnians
open SixQubit.Orbit30
open MainTheory.Orbit30PrintedMoments MainTheory.Orbit30ProbabilityLabels
open MainTheory.Orbit30PhysicalRows MainTheory.Orbit30PhysicalPhases MainTheory.Orbit30PhysicalGraph
noncomputable section
theorem almost_full_set : ∀ S : Finset (Fin 5),4 ≤ S.card →
    ∀ i j,i≠j → i ∈ S ∨ j ∈ S := by decide +kernel
theorem edge_index_symmetric : ∀ i j,edgeIndexMatrix i j=edgeIndexMatrix j i := by decide +kernel
variable (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1) (hkl : SS.HasDistance ![c,d] 3)
include hc hd hnc hnd hkl in
theorem actual_regular_points (i j : Fin 5) (hij : i≠j) : pointC c i≠0 ∨ pointC c j≠0 := by
  let D := physicalData c d hc hd hnc hnd hkl
  have he := almost_full_set D.A (actual_four_active c d hc hd hnc hnd hkl) i j hij
  rcases he with hi | hj
  · left
    exact Complex.normSq_pos.mp ((D.mem_A).mp hi)
  · right
    exact Complex.normSq_pos.mp ((D.mem_A).mp hj)
include hc hd hnc hnd hkl in
theorem actual_all_edge_phases (i j : Fin 5) (hij : i≠j) (he : edgeC c i j≠0) :
    phase c d (edgeIndexMatrix i j)=-phase c d ⟨15,by decide⟩ := by
  rcases actual_regular_points c d hc hd hnc hnd hkl i j hij with hi | hj
  · have he' : edgeC c j i≠0 := by rwa [edge_symmetric c j i]
    have h := actual_edge_phase c d hc hd hnc hnd hkl j i hij.symm hi he'
    rwa [edge_index_symmetric j i] at h
  · exact actual_edge_phase c d hc hd hnc hnd hkl i j hij hj he
include hc hd hnc hnd hkl in
theorem actual_edge_reconstruction (i j : Fin 5) :
    edgeV d i j=-phase c d ⟨15,by decide⟩*star (edgeC c i j) := by
  by_cases hij : i=j
  · simp [edgeV,edgeC,hij]
  · by_cases he : edgeC c i j=0
    · rw [zero_edge_top c d hc hd hnc hnd hkl i j he,he]
      simp
    · have h := actual_all_edge_phases c d hc hd hnc hnd hkl i j hij he
      have hp : MainTheory.PhysicalPhaseQuotients.rho (edgeC c i j) (edgeV d i j)=
          -phase c d ⟨15,by decide⟩ := by
        simpa only [phase,edgeC,edgeV,if_neg hij] using h
      have hmul : MainTheory.PhysicalPhaseQuotients.rho (edgeC c i j) (edgeV d i j)*
          star (edgeC c i j)=edgeV d i j := div_mul_cancel₀ _ (star_ne_zero.mpr he)
      rw [hp] at hmul
      exact hmul.symm
def edgeMatrix : Matrix (Fin 5) (Fin 5) ℂ := edgeC c
include hc hd hnc hnd hkl in
theorem actual_matching_factor (i : Fin 5) :
    matchingSum c d i=2*(-phase c d ⟨15,by decide⟩)*
      star (MainTheory.Orbit30VertexScaling.hafnian (edgeMatrix c) i) := by
  fin_cases i <;>
    simp +decide [matchingSum,MainTheory.Orbit30VertexScaling.hafnian,edgeMatrix,edgeU,
      actual_edge_reconstruction c d hc hd hnc hnd hkl,star_add,star_mul,
      edgeC,edgeIndexMatrix,bottom] <;> ring
include hc hd hnc hnd hkl in
theorem actual_hafnians : ∀ i,MainTheory.Orbit30VertexScaling.hafnian (edgeMatrix c) i=0 := by
  intro i
  have hn : phase c d ⟨15,by decide⟩≠0 := by
    have hu := actual_unit_phase c d hc hd hnc hnd hkl ⟨15,by decide⟩
      (by simpa [bottom] using (actual_anchor_nonzero c d hc hd hnc hnd hkl).1)
    intro h
    rw [h] at hu
    norm_num at hu
  have hm := (physical_rows c d hc hd hkl).2.2.2 i
  rw [actual_matching_factor c d hc hd hnc hnd hkl] at hm
  exact star_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left
    (mul_ne_zero (by norm_num) (neg_ne_zero.mpr hn)))
end
end MainTheory.Orbit30PhysicalHafnians
