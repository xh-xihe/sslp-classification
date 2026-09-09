import MainTheory.Orbit9ComponentDisplays
import MainTheory.Orbit9SmallMatrixDisplays
import SixQubit.Orbit9K4Bridge

set_option autoImplicit false

namespace MainTheory.Orbit9K4Displays

open SixQubit.Orbit9Universal MainTheory.Orbit9ComponentDisplays

theorem normal_form (c d : SS.State 6 ℂ) (H : FullKL c d)
    (i j k l : Fin 6) (K : ActiveK4 c d i j k l)
    (hex : ActiveExactly4 c i j k l) :
    m c i j=m c k l ∧ m c i k=m c j l ∧ m c i l=m c j k ∧
    m c i j+m c i k+m c i l=0 ∧
    (m c i j)^2+(m c i k)^2+(m c i l)^2=0 ∧
    m c i j ≠ 0 ∧ m c i k ≠ 0 ∧ m c i l ≠ 0 := by
  have hi := samePhase_self c d i K.active_i
  have hj := samePhase_of_active_edge c d H i j K.hij K.active_i K.active_j K.edge_ij
  have hk := samePhase_of_active_edge c d H i k K.hik K.active_i K.active_k K.edge_ik
  have hl := samePhase_of_active_edge c d H i l K.hil K.active_i K.active_l K.edge_il
  have h := active_k4_normal_form c d H i j k l K hex
  simp only [componentMatrix,hi,hj,hk,hl,and_self,ite_true] at h
  refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2,?_,?_,?_⟩
  · exact mul_ne_zero (mul_ne_zero K.edge_ij (xamp_ne_zero_of_active c i K.active_i))
      (xamp_ne_zero_of_active c j K.active_j)
  · exact mul_ne_zero (mul_ne_zero K.edge_ik (xamp_ne_zero_of_active c i K.active_i))
      (xamp_ne_zero_of_active c k K.active_k)
  · exact mul_ne_zero (mul_ne_zero K.edge_il (xamp_ne_zero_of_active c i K.active_i))
      (xamp_ne_zero_of_active c l K.active_l)

noncomputable def z (c : SS.State 6 ℂ) (t i : Fin 6) : ℂ := damp c t i*xamp c i

theorem cross_matrix (c d : SS.State 6 ℂ) (H : FullKL c d)
    (i j k l t : Fin 6) (K : ActiveK4 c d i j k l)
    (hex : ActiveExactly4 c i j k l)
    (hti : t ≠ i) (htj : t ≠ j) (htk : t ≠ k) (htl : t ≠ l) :
    (MainTheory.Orbit9SmallMatrixDisplays.cross (m c i j) (m c i k) (m c i l)).mulVec
      ![z c t i,z c t j,z c t k,z c t l]=0 := by
  have hi := samePhase_self c d i K.active_i
  have hj := samePhase_of_active_edge c d H i j K.hij K.active_i K.active_j K.edge_ij
  have hk := samePhase_of_active_edge c d H i k K.hik K.active_i K.active_k K.edge_ik
  have hl := samePhase_of_active_edge c d H i l K.hil K.active_i K.active_l K.edge_il
  obtain ⟨hA,hB,hC,_,_,_,_,_⟩ := normal_form c d H i j k l K hex
  have raw0 := damp_hafnian_one_outside c d H i t i j k hi hj hk hti htj htk
    K.hij K.hik K.hjk
  have raw1 := damp_hafnian_one_outside c d H i t i j l hi hj hl hti htj htl
    K.hij K.hil K.hjl
  have raw2 := damp_hafnian_one_outside c d H i t i k l hi hk hl hti htk htl
    K.hik K.hil K.hkl
  have raw3 := damp_hafnian_one_outside c d H i t j k l hj hk hl htj htk htl
    K.hjk K.hjl K.hkl
  have e0 : m c i l*z c t i+m c i k*z c t j+m c i j*z c t k=0 := by
    rw [hC]
    dsimp [m,z]
    linear_combination (xamp c i*xamp c j*xamp c k)*raw0
  have e1 : m c i k*z c t i+m c i l*z c t j+m c i j*z c t l=0 := by
    rw [hB]
    dsimp [m,z]
    linear_combination (xamp c i*xamp c j*xamp c l)*raw1
  have e2 : m c i j*z c t i+m c i l*z c t k+m c i k*z c t l=0 := by
    rw [hA]
    dsimp [m,z]
    linear_combination (xamp c i*xamp c k*xamp c l)*raw2
  have e3 : m c i j*z c t j+m c i k*z c t k+m c i l*z c t l=0 := by
    rw [hA,hB,hC]
    dsimp [m,z]
    linear_combination (xamp c j*xamp c k*xamp c l)*raw3
  funext a
  fin_cases a <;>
    simp [MainTheory.Orbit9SmallMatrixDisplays.cross,Matrix.mulVec,dotProduct,
      Fin.sum_univ_succ]
  · linear_combination e0
  · linear_combination e1
  · linear_combination e2
  · linear_combination e3

theorem z_sum (c d : SS.State 6 ℂ) (H : FullKL c d)
    (i j k l t : Fin 6) (K : ActiveK4 c d i j k l)
    (hex : ActiveExactly4 c i j k l) : z c t i+z c t j+z c t k+z c t l=0 := by
  exact companion_four_sum c d H i t i j k l K hex
    (samePhase_self c d i K.active_i)
    (samePhase_of_active_edge c d H i j K.hij K.active_i K.active_j K.edge_ij)
    (samePhase_of_active_edge c d H i k K.hik K.active_i K.active_k K.edge_ik)
    (samePhase_of_active_edge c d H i l K.hil K.active_i K.active_l K.edge_il)

end MainTheory.Orbit9K4Displays
