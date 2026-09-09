import MainTheory.Orbit9MomentDisplays

set_option autoImplicit false
set_option maxRecDepth 100000

namespace MainTheory.Orbit9FlipDisplays

open SixQubit.Orbit9Universal

noncomputable def A (c d : SS.State 6 ℂ) (i j : Fin 6) : ℂ :=
  star (xamp c j)*camp d i j
noncomputable def B (c d : SS.State 6 ℂ) (i j : Fin 6) : ℂ :=
  star (damp c i j)*yamp d j

theorem low_shell_index (i : Fin 6) :
    (flipInter i).filter (fun y => hwt y=2)=(Finset.univ.erase i).image (pair i) := by
  fin_cases i <;> decide

theorem pair_left_injective (i : Fin 6) : Function.Injective (pair i) := by
  intro j k hjk
  apply one_injective
  have h := congrArg (SS.bxor (one i)) hjk
  simpa [pair,← SS.bxor_assoc] using h

theorem low_sum (c d : SS.State 6 ℂ) (i : Fin 6) :
    flipLow c d i=∑ j ∈ Finset.univ.erase i,A c d i j := by
  classical
  unfold flipLow
  rw [← Finset.sum_filter,low_shell_index,Finset.sum_image (pair_left_injective i).injOn]
  apply Finset.sum_congr rfl
  intro j hj
  have hji := Finset.ne_of_mem_erase hj
  unfold flipTerm
  rw [pair_flip_xor i j hji]
  simp [A,xamp,camp,Ne.symm hji]

theorem high_sum (c d : SS.State 6 ℂ) (i : Fin 6) :
    flipHigh c d i=∑ j ∈ Finset.univ.erase i,B c d i j := flipHigh_eq_companion_sum c d i

variable (c d : SS.State 6 ℂ) (H : FullKL c d)
include H

theorem undressed_flip (i : Fin 6) :
    (∑ j ∈ Finset.univ.erase i,(A c d i j+B c d i j))=0 := by
  obtain ⟨hL,hH⟩ := single_flip_shell_sums c d H.support0 H.support1 H.distance i
  rw [Finset.sum_add_distrib,← low_sum,← high_sum,hL,hH,add_zero]

theorem dressed_flip (i j : Fin 6) (hji : j ≠ i) :
    (∑ k ∈ Finset.univ.erase i,A c d i k)-2*A c d i j-
      (∑ k ∈ Finset.univ.erase i,B c d i k)+2*B c d i j=0 := by
  have h := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d H.support0 H.support1
    H.distance (SS.stdBasis i) (SS.stdBasis j) (flip_wt_dressed i j)
  rw [offSum_dressed_expansion c d i j hji,low_sum,high_sum] at h
  have ha : A c d i j=star (c (one j))*d (pair i j) := by
    simp [A,xamp,camp,Ne.symm hji]
  have hb : B c d i j=star (c (SS.complement (pair i j)))*d (SS.complement (one j)) := by
    simp [B,damp,yamp,Ne.symm hji]
  rw [ha,hb]
  linear_combination h

theorem single_flip_normal_form (i j : Fin 6) (hji : j ≠ i) :
    A c d i j=B c d i j ∧ (∑ k ∈ Finset.univ.erase i,A c d i k)=0 := by
  constructor
  · simpa [A,B,xamp,yamp,camp,damp,Ne.symm hji] using
      single_flip_edge c d H.support0 H.support1 H.distance i j hji
  · rw [← low_sum]
    exact (single_flip_shell_sums c d H.support0 H.support1 H.distance i).1

theorem edge_balance_both (i j : Fin 6) (hji : j ≠ i) :
    p c j*s d i j=q d j*r c i j ∧ p c i*s d i j=q d i*r c i j := by
  refine ⟨edge_balance c d H.support0 H.support1 H.distance i j hji,?_⟩
  have h := edge_balance c d H.support0 H.support1 H.distance j i (Ne.symm hji)
  simpa [s_symm d j i,r_symm c j i] using h

theorem phase_sync (i j : Fin 6) (hji : j ≠ i) (hi : 0 < p c i) (hj : 0 < p c j) :
    camp d i j=rho c d i*star (damp c i j) ∧
    camp d i j=rho c d j*star (damp c i j) := by
  constructor
  · have h := camp_eq_rho_mul_star_damp c d H.support0 H.support1 H.distance j i
      (Ne.symm hji) hi
    simpa [camp_symm d j i,damp_symm c j i] using h
  · exact camp_eq_rho_mul_star_damp c d H.support0 H.support1 H.distance i j hji hj

end MainTheory.Orbit9FlipDisplays
