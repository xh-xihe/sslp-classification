import MainTheory.Orbit30PhysicalPhases
import MainTheory.Orbit30SupportGraph
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit30PhysicalGraph
open SixQubit.Orbit30
open MainTheory.Orbit30PrintedMoments MainTheory.Orbit30ProbabilityLabels
open MainTheory.Orbit30PhysicalRows MainTheory.Orbit30PhysicalPhases
open scoped BigOperators
noncomputable section
variable (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1) (hkl : SS.HasDistance ![c,d] 3)

include hc hd hnc hnd hkl in
theorem zero_edge_top (i j : Fin 5) (he : edgeC c i j=0) : edgeV d i j=0 := by
  by_cases hij : i=j
  · simp [edgeV,hij]
  · have h := actual_equal_norms c d hc hd hnc hnd hkl (edgeIndexMatrix i j)
    have hz : c (bottom (edgeIndexMatrix i j))=0 := by simpa only [edgeC,if_neg hij] using he
    rw [hz,Complex.normSq_zero] at h
    simpa only [edgeV,if_neg hij] using Complex.normSq_eq_zero.mp h
include hc hd hnc hnd hkl in
theorem synchronized_term (i j : Fin 5) :
    pointU c j*edgeV d i j=-phase c d ⟨15,by decide⟩*star (pointC c j*edgeC c i j) := by
  by_cases hij : i=j
  · simp [pointU,edgeC,edgeV,hij]
  · by_cases hj : pointC c j=0
    · simp [pointU,hj]
    · by_cases he : edgeC c i j=0
      · rw [zero_edge_top c d hc hd hnc hnd hkl i j he,he]
        simp
      · have hn : c (bottom (edgeIndexMatrix i j))≠0 := by simpa only [edgeC,if_neg hij] using he
        have h := reciprocal_product c d (vertexIndex j) (edgeIndexMatrix i j) hn
        rw [actual_edge_phase c d hc hd hnc hnd hkl i j hij hj he] at h
        simpa only [pointU,pointC,edgeV,edgeC,if_neg hij] using h

theorem literal_star_sum (i : Fin 5) : starSum c d i=∑ j,pointU c j*edgeV d i j := by
  fin_cases i <;>
    norm_num [starSum,pointU,pointC,edgeV,edgeIndexMatrix,vertexIndex,
      bottom,top,complementIndex,Fin.sum_univ_succ,Fin.succ] <;> ring
include hc hd hnc hnd hkl in
theorem bilinear_row (i : Fin 5) : (∑ j,pointC c j*edgeC c i j)=0 := by
  have hp := actual_unit_phase c d hc hd hnc hnd hkl ⟨15,by decide⟩
    (by simpa [bottom] using (actual_anchor_nonzero c d hc hd hnc hnd hkl).1)
  have hpn : phase c d ⟨15,by decide⟩≠0 := by
    intro h
    rw [h] at hp
    norm_num at hp
  have hs : -phase c d ⟨15,by decide⟩*star (∑ j,pointC c j*edgeC c i j)=0 := by
    calc
      _ = ∑ j,pointU c j*edgeV d i j := by
        rw [star_sum,Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => (synchronized_term c d hc hd hnc hnd hkl i j).symm)
      _ = starSum c d i := (literal_star_sum c d i).symm
      _ = 0 := (physical_rows c d hc hd hkl).2.2.1 i
  exact star_eq_zero.mp ((mul_eq_zero.mp hs).resolve_left (neg_ne_zero.mpr hpn))
include hc hd hnc hnd hkl in
theorem bilinear_erase_row (i : Fin 5) :
    (∑ j ∈ Finset.univ.erase i,pointC c j*edgeC c i j)=0 := by
  have he : (∑ j ∈ Finset.univ.erase i,pointC c j*edgeC c i j)=
      ∑ j,pointC c j*edgeC c i j := by
    apply Finset.sum_subset (Finset.erase_subset _ _) ?_
    intro j _ hj
    have hji : j=i := by simpa using hj
    subst j
    simp [edgeC]
  rw [he]
  exact bilinear_row c d hc hd hnc hnd hkl i
theorem edge_symmetric (i j : Fin 5) : edgeC c i j=edgeC c j i := by
  fin_cases i <;> fin_cases j <;> norm_num [edgeC,edgeIndexMatrix]
include hc hd hnc hnd hkl in
theorem degree_norm (i : Fin 5) :
    (∑ j,Complex.normSq (edgeC c i j))=Complex.normSq (pointC c i)+1/8 := by
  have h := (physical_probabilities c d hc hd hnc hnd hkl).2.1 i
  fin_cases i <;>
    norm_num [edgeC,edgeIndexMatrix,pointC,vertexIndex,pointMass,degreeMass,
      bottomProbability,bottom,Fin.sum_univ_succ,Fin.succ] at h ⊢ <;> linarith only [h]
include c d hc hd hnc hnd hkl in
def physicalData : MainTheory.Orbit30.Data where
  b := pointC c
  c := edgeC c
  c_symm := edge_symmetric c
  c_diag := by intro i; simp [edgeC]
  degree := degree_norm c d hc hd hnc hnd hkl
  total_point := by
    simpa only [pointMass,bottomProbability,pointC] using
      (physical_probabilities c d hc hd hnc hnd hkl).2.2.1
  row := bilinear_erase_row c d hc hd hnc hnd hkl
theorem actual_three_active : 3 ≤ (physicalData c d hc hd hnc hnd hkl).A.card :=
  (physicalData c d hc hd hnc hnd hkl).three_le_card_A
theorem actual_four_active : 4 ≤ (physicalData c d hc hd hnc hnd hkl).A.card :=
  (physicalData c d hc hd hnc hnd hkl).four_le_card_A
end
end MainTheory.Orbit30PhysicalGraph
