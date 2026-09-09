import MainTheory.Orbit8LadderAdjoint
import SixQubit.Orbit8UniversalLow

set_option autoImplicit false

namespace MainTheory.Orbit8QDisplay

open SixQubit.Orbit8Universal MainTheory.Orbit8LadderMatrices

theorem off_diagonal_sum (F : Fin 6 → Fin 6 → ℂ) :
    (∑ i,∑ j,if i=j then 0 else F i j)=
      ∑ ij ∈ pairs6,(F ij.1 ij.2+F ij.2 ij.1) := by
  rw [sum_ordered_decompose]
  simp only [ite_true,Finset.sum_const_zero,zero_add]
  apply Finset.sum_congr rfl
  intro ij hij
  have hlt := (Finset.mem_filter.mp hij).2
  simp [ne_of_lt hlt,Ne.symm (ne_of_lt hlt)]

theorem operator_expansion (ud : Fin 6 → ℂ) (f : SS.State 6 ℂ) :
    Qact ud f=fun x =>
      (∑ i,(Complex.normSq (ud i) : ℂ)*(f x-SS.pauliAct (Pz i) f x)/2)+
      ∑ i,∑ j,if i=j then 0 else ud i*star (ud j)*(plus i*minus j).mulVec f x := by
  simp only [MainTheory.Orbit8LadderAdjoint.product_action]
  rw [Qact_expand]
  funext x
  rw [sum_ordered_decompose,off_diagonal_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [congrFun (diag_group ud f i) x]
  ring

end MainTheory.Orbit8QDisplay
