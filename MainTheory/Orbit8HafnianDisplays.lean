import SixQubit.Orbit8UniversalHafnianExplicit

set_option autoImplicit false

namespace MainTheory.Orbit8HafnianDisplays

open SixQubit.Orbit8Universal

def remaining : Fin 6 → Fin 6 → Fin 4 → Fin 6 :=
  ![![![1,2,3,4],
    ![2,3,4,5],
    ![1,3,4,5],
    ![1,2,4,5],
    ![1,2,3,5],
    ![1,2,3,4]],
    ![![2,3,4,5],
    ![0,2,3,4],
    ![0,3,4,5],
    ![0,2,4,5],
    ![0,2,3,5],
    ![0,2,3,4]],
    ![![1,3,4,5],
    ![0,3,4,5],
    ![0,1,3,4],
    ![0,1,4,5],
    ![0,1,3,5],
    ![0,1,3,4]],
    ![![1,2,4,5],
    ![0,2,4,5],
    ![0,1,4,5],
    ![0,1,2,4],
    ![0,1,2,5],
    ![0,1,2,4]],
    ![![1,2,3,5],
    ![0,2,3,5],
    ![0,1,3,5],
    ![0,1,2,5],
    ![0,1,2,3],
    ![0,1,2,3]],
    ![![1,2,3,4],
    ![0,2,3,4],
    ![0,1,3,4],
    ![0,1,2,4],
    ![0,1,2,3],
    ![0,1,2,3]]]

theorem remaining_spec : ∀ i j : Fin 6,i ≠ j →
    Function.Injective (remaining i j) ∧
    Finset.univ.image (remaining i j)=(Finset.univ.erase i).erase j := by decide

theorem remaining_swap : ∀ i j : Fin 6,remaining i j=remaining j i := by decide

theorem hafnian_sorted (d : SS.State 6 ℂ) (i j : Fin 6) (hij : i < j) :
    compHaf d i j=
      v d (remaining i j 0) (remaining i j 1)*v d (remaining i j 2) (remaining i j 3)+
      v d (remaining i j 0) (remaining i j 2)*v d (remaining i j 1) (remaining i j 3)+
      v d (remaining i j 0) (remaining i j 3)*v d (remaining i j 1) (remaining i j 2) := by
  fin_cases i <;> fin_cases j <;> simp [remaining] at hij ⊢

theorem hafnian_formula (d : SS.State 6 ℂ) (i j : Fin 6) (hij : i ≠ j) :
    compHaf d i j=
      v d (remaining i j 0) (remaining i j 1)*v d (remaining i j 2) (remaining i j 3)+
      v d (remaining i j 0) (remaining i j 2)*v d (remaining i j 1) (remaining i j 3)+
      v d (remaining i j 0) (remaining i j 3)*v d (remaining i j 1) (remaining i j 2) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact hafnian_sorted d i j h
  · rw [compHaf_swap d i j,remaining_swap i j]
    exact hafnian_sorted d j i h

end MainTheory.Orbit8HafnianDisplays
