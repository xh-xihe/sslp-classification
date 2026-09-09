import SixQubit.Orbit8UniversalMagnitudes

set_option autoImplicit false

namespace MainTheory.Orbit8OccupationDisplays

open SixQubit SixQubit.Orbit8Universal

theorem incident_row (d : SS.State 6 ℂ) (i : Fin 6) :
    D d i=∑ j : Fin 6,if j ≠ i then w d i j else 0 := by
  calc
    D d i = (∑ j : Fin 6, if j < i then w d j i else if i < j then w d i j else 0) := by
      fin_cases i <;> simp [D,incidentPairs,Finset.sum_filter,pairs6_eq,Fin.sum_univ_succ]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j < i
      · simp only [if_pos hji,if_pos (ne_of_lt hji)]
        exact (w_swap d j i).symm
      · rw [if_neg hji]
        by_cases hij : i < j
        · simp [hij,Ne.symm (ne_of_lt hij)]
        · have he : j=i := by omega
          subst j
          simp

theorem one_occupation (d : SS.State 6 ℂ) (i : Fin 6) :
    occOn S1 d i=p d i+∑ ij ∈ awayPairs i,w d ij.1 ij.2 := by
  change (∑ x ∈ oneFiber i,Complex.normSq (d x))=_
  rw [oneFiber_image,Finset.sum_insert (singleton_not_edge_image i)]
  rw [Finset.sum_image (edgeState_injective_on.mono
    (show awayPairs i ⊆ pairs6 from Finset.filter_subset _ _))]
  rfl

theorem two_occupation (d : SS.State 6 ℂ) (ij : Pair6) :
    occ2On S1 d ij.1.1 ij.1.2=∑ kl ∈ awayPairs2 ij.1,w d kl.1 kl.2 := by
  change (∑ x ∈ twoFiber ij.1,Complex.normSq (d x))=_
  rw [twoFiber_image ij.1 ij.2]
  rw [Finset.sum_image (edgeState_injective_on.mono
    (show awayPairs2 ij.1 ⊆ pairs6 from Finset.filter_subset _ _))]
  rfl

variable (c d : SS.State 6 ℂ)
  (hc : ∀ x,SS.weight av x ≠ 0 → c x=0)
  (hd : ∀ x,SS.weight av x ≠ 1 → d x=0)
  (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
  (hcode : SS.HasDistance ![c,d] 3)

include hc hd hnc hnd hcode

theorem one_display (i : Fin 6) : occOn S1 d i=p d i+5/6-D d i := by
  have hm := (rigid_shells c d hc hd hnc hnd hcode).2.2.2.2.2
  rw [shell4_edge_mass] at hm
  have he := edge_mass_partition d i
  rw [one_occupation]
  linarith

theorem two_display (ij : Pair6) :
    occ2On S1 d ij.1.1 ij.1.2=5/6-D d ij.1.1-D d ij.1.2+w d ij.1.1 ij.1.2 := by
  have hm := (rigid_shells c d hc hd hnc hnd hcode).2.2.2.2.2
  rw [shell4_edge_mass] at hm
  have he := edge_inclusion_identity d ij
  rw [two_occupation]
  linarith

end MainTheory.Orbit8OccupationDisplays
