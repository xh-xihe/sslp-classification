import MainTheory.PauliTransferTwo
import SixQubit.MacWilliams

set_option autoImplicit false

namespace MainTheory.OneQubitPauliPurity

open MainTheory.PauliTransferTwo

theorem nonidentity_purity (A : Mat2) (hA : A.conjTranspose=A) (ht : A.trace=1) :
    ((Complex.normSq ((pauli 1*A).trace)+Complex.normSq ((pauli 2*A).trace)+
      Complex.normSq ((pauli 3*A).trace) : ℝ) : ℂ) = 2*(A*A).trace-1 := by
  have h := coefficient_inner A A
  have hs : star A=A := hA
  rw [hs] at h
  simp only [Fin.sum_univ_four,coefficient,pauli_zero,Matrix.one_mul,ht] at h
  simp only [Complex.ofReal_add,← SixQubit.star_mul_self]
  simp at h
  simp only [Complex.star_def]
  linear_combination 4*h

end MainTheory.OneQubitPauliPurity
