import MainTheory.Orbit9FlipDisplays

set_option autoImplicit false

namespace MainTheory.Orbit9ConnectedComponents

open SixQubit.Orbit9Universal

noncomputable def graph (c : SS.State 6 ℂ) : SimpleGraph (Fin 6) where
  Adj i j := i ≠ j ∧ Active c i ∧ Active c j ∧ damp c i j ≠ 0
  symm := by
    intro i j h
    exact ⟨Ne.symm h.1,h.2.2.1,h.2.1,by simpa [damp_symm c j i] using h.2.2.2⟩
  loopless := by intro i h; exact h.1 rfl

noncomputable def component (c : SS.State 6 ℂ) (a : Fin 6) : Finset (Fin 6) := by
  classical
  exact Finset.univ.filter ((graph c).Reachable a)

theorem component_phase (c d : SS.State 6 ℂ) (H : FullKL c d)
    (a : Fin 6) (ha : Active c a) (i : Fin 6) (hi : i ∈ component c a) :
    SamePhase c d a i := by
  classical
  have hr : (graph c).Reachable a i := (Finset.mem_filter.mp hi).2
  have ht := ((graph c).reachable_iff_reflTransGen a i).mp hr
  clear hi hr
  induction ht with
  | refl => exact ⟨ha,rfl⟩
  | @tail b e _ hedge ih =>
    have he : b ≠ e ∧ Active c b ∧ Active c e ∧ damp c b e ≠ 0 := hedge
    exact ⟨he.2.2.1,(rho_sync c d H.support0 H.support1 H.distance b e
      he.1 he.2.1 he.2.2.1 he.2.2.2).symm.trans ih.2⟩

theorem outside_matrix_zero (c d : SS.State 6 ℂ) (a i j : Fin 6)
    (hi : i ∈ component c a) (hj : j ∉ component c a) : componentMatrix c d a i j=0 := by
  classical
  by_cases hp : SamePhase c d a i ∧ SamePhase c d a j
  · have he : damp c i j=0 := by
      by_contra hn
      have hij : i ≠ j := by rintro rfl; exact hj hi
      have hr : (graph c).Reachable a i := (Finset.mem_filter.mp hi).2
      have hadj : (graph c).Adj i j := ⟨hij,hp.1.1,hp.2.1,hn⟩
      apply hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr.trans hadj.reachable⟩
    simp [componentMatrix,hp,he]
  · simp [componentMatrix,hp]

theorem component_m_row (c d : SS.State 6 ℂ) (H : FullKL c d)
    (a : Fin 6) (ha : Active c a) (i : Fin 6) (hi : i ∈ component c a) :
    (∑ j ∈ component c a,damp c i j*xamp c i*xamp c j)=0 := by
  classical
  have hsum : (∑ j ∈ component c a,componentMatrix c d a i j)=
      ∑ j,componentMatrix c d a i j := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    exact outside_matrix_zero c d a i j hi hj
  rw [componentMatrix_row c d H a ha i] at hsum
  have hpi := component_phase c d H a ha i hi
  convert hsum using 1
  apply Finset.sum_congr rfl
  intro j hj
  simp [componentMatrix,hpi,component_phase c d H a ha j hj]

theorem component_kernel (c d : SS.State 6 ℂ) (H : FullKL c d)
    (a : Fin 6) (ha : Active c a) (i : Fin 6) (hi : i ∈ component c a) :
    (∑ j ∈ component c a,damp c i j*xamp c j)=0 := by
  have h := component_m_row c d H a ha i hi
  have he : xamp c i*(∑ j ∈ component c a,damp c i j*xamp c j)=0 := by
    rw [Finset.mul_sum]
    simpa only [mul_left_comm,mul_assoc] using h
  exact (mul_eq_zero.mp he).resolve_left
    (xamp_ne_zero_of_active c i (component_phase c d H a ha i hi).1)

theorem component_hafnian (c d : SS.State 6 ℂ) (H : FullKL c d)
    (a : Fin 6) (ha : Active c a) (i j k l : Fin 6)
    (hi : i ∈ component c a) (hj : j ∈ component c a)
    (hk : k ∈ component c a) (hl : l ∈ component c a)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    damp c i j*damp c k l+damp c i k*damp c j l+damp c i l*damp c j k=0 :=
  damp_hafnian_same_phase c d H a i j k l
    (component_phase c d H a ha i hi) (component_phase c d H a ha j hj)
    (component_phase c d H a ha k hk) (component_phase c d H a ha l hl)
    hij hik hil hjk hjl hkl

end MainTheory.Orbit9ConnectedComponents
