import SixQubit.Orbit9ComponentPhase

set_option autoImplicit false

namespace MainTheory.Orbit9MomentDisplays

open SixQubit.Orbit9Universal

theorem fiber_residues : ∀ x : SS.BitString 6,
    (x ∈ S0 ↔ SS.hammingWt x % 3=1) ∧ (x ∈ S1 ↔ SS.hammingWt x % 3=2) := by decide

theorem probability_definitions (c d : SS.State 6 ℂ) (i j : Fin 6) :
    p c i=Complex.normSq (xamp c i) ∧ q d i=Complex.normSq (yamp d i) ∧
    r c i j=Complex.normSq (damp c i j) ∧ s d i j=Complex.normSq (camp d i j) := by
  refine ⟨rfl,rfl,?_,?_⟩ <;> by_cases hij : i=j <;> simp [r,s,damp,camp,hij]

theorem degree_definitions (c d : SS.State 6 ℂ) (i : Fin 6) :
    Rdeg c i=(∑ j : Fin 6,if j ≠ i then r c i j else 0) ∧
    Sdeg d i=(∑ j : Fin 6,if j ≠ i then s d i j else 0) := by
  constructor <;> apply Finset.sum_congr rfl <;> intro j _ <;>
    by_cases hji : j=i <;> simp [r,s,hji]

theorem total_definitions (c d : SS.State 6 ℂ) :
    Pmass c=(∑ i,p c i) ∧ Qmass d=(∑ i,q d i) := ⟨rfl,rfl⟩

variable (c d : SS.State 6 ℂ) (H : FullKL c d)
include H

theorem mean_weight : 4-3*Pmass c=2+3*Qmass d := by
  obtain ⟨hP,_,_,hQ⟩ := global_masses c d H.support0 H.support1 H.norm0 H.norm1 H.distance
  rw [hP,hQ]
  norm_num

theorem second_weight_moment : 6*(1-Pmass c)=1+9*Qmass d := by
  obtain ⟨hP,_,_,hQ⟩ := global_masses c d H.support0 H.support1 H.norm0 H.norm1 H.distance
  rw [hP,hQ]
  norm_num

theorem one_coordinate (i : Fin 6) : p c i+2/3-Rdeg c i=Sdeg d i+1/3-q d i := by
  obtain ⟨hR,hS⟩ := degree_normal_form c d H.support0 H.support1 H.norm0 H.norm1 H.distance i
  linarith

theorem two_coordinate_sum (i : Fin 6) : 2-3*Rdeg c i=Sdeg d i+4/3-4*q d i := by
  obtain ⟨hR,hS⟩ := degree_normal_form c d H.support0 H.support1 H.norm0 H.norm1 H.distance i
  linarith

theorem factor_equation (i : Fin 6) : (p c i-q d i)*(1+9*p c i+9*q d i)=0 := by
  obtain ⟨hR,hS⟩ := degree_normal_form c d H.support0 H.support1 H.norm0 H.norm1 H.distance i
  have hb := degree_balance c d H.support0 H.support1 H.distance i
  rw [hR,hS] at hb
  nlinarith

theorem half_occupation (i : Fin 6) : p c i+2/3-Rdeg c i=(1/2 : ℝ) := by
  have h := (pq_degree c d H.support0 H.support1 H.norm0 H.norm1 H.distance i).2.1
  linarith

end MainTheory.Orbit9MomentDisplays
