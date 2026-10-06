import MainTheory.PauliTransferTwo
import SixQubit.MacWilliams

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

namespace MainTheory.PairPauliPurity

abbrev PairMat := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

noncomputable def pairPauli (p q : Fin 4) : PairMat :=
  fun i j => MainTheory.PauliTransferTwo.pauli p i.1 j.1*
    MainTheory.PauliTransferTwo.pauli q i.2 j.2

theorem parseval (A : PairMat) :
    ((∑ p : Fin 4,∑ q : Fin 4,Complex.normSq ((pairPauli p q*A).trace) : ℝ) : ℂ) =
      4*(A.conjTranspose*A).trace := by
  simp only [Complex.ofReal_sum,← SixQubit.star_mul_self]
  simp [pairPauli,MainTheory.PauliTransferTwo.pauli,Matrix.trace,Matrix.diag_apply,
    Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type,
    Fin.sum_univ_four,Fin.sum_univ_two]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem hermitian_purity (A : PairMat) (hA : A.conjTranspose=A) :
    ((∑ p : Fin 4,∑ q : Fin 4,Complex.normSq ((pairPauli p q*A).trace) : ℝ) : ℂ) =
      4*(A*A).trace := by
  rw [parseval,hA]

end MainTheory.PairPauliPurity
