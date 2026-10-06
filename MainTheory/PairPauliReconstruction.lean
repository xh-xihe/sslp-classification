import MainTheory.PairPauliPurity

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace MainTheory.PairPauliReconstruction

open MainTheory.PairPauliPurity

theorem expansion (A : PairMat) :
    (∑ p : Fin 4,∑ q : Fin 4,((1/4 : ℂ)*(pairPauli p q*A).trace) • pairPauli p q)=A := by
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [pairPauli,MainTheory.PauliTransferTwo.pauli,Matrix.trace,Matrix.diag_apply,
      Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_four,Fin.sum_univ_two] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem ext_traces (A B : PairMat)
    (h : ∀ p q : Fin 4,(pairPauli p q*A).trace=(pairPauli p q*B).trace) : A=B := by
  rw [← expansion A,← expansion B]
  simp_rw [h]

end MainTheory.PairPauliReconstruction
