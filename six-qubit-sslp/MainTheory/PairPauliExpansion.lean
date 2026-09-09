import MainTheory.PairPauliPurity

set_option autoImplicit false

namespace MainTheory.PairPauliExpansion

open MainTheory.PairPauliPurity

def nonidentity : Finset (Fin 4 × Fin 4) := Finset.univ.erase (0,0)

theorem pair_identity : pairPauli 0 0=(1 : PairMat) := by
  ext p q
  rcases p with ⟨p1,p2⟩
  rcases q with ⟨q1,q2⟩
  by_cases h1 : p1=q1 <;> by_cases h2 : p2=q2 <;>
    simp [pairPauli,MainTheory.PauliTransferTwo.pauli_zero,Matrix.one_apply,h1,h2]

theorem normalized_expansion (A : PairMat) (hA : A.conjTranspose=A) (ht : A.trace=1) :
    4*(A*A).trace = 1+
      ((∑ r ∈ nonidentity,Complex.normSq ((pairPauli r.1 r.2*A).trace) : ℝ) : ℂ) := by
  have htotal : ((∑ r : Fin 4 × Fin 4,Complex.normSq ((pairPauli r.1 r.2*A).trace) : ℝ) : ℂ)=
      4*(A*A).trace := by
    simpa only [Fintype.sum_prod_type] using hermitian_purity A hA
  have hzero : Complex.normSq ((pairPauli 0 0*A).trace)=1 := by
    rw [pair_identity,Matrix.one_mul,ht]
    norm_num
  have hs := Finset.sum_erase_add (Finset.univ : Finset (Fin 4 × Fin 4))
    (fun r => Complex.normSq ((pairPauli r.1 r.2*A).trace)) (a := (0,0)) (Finset.mem_univ _)
  change (∑ r ∈ nonidentity,Complex.normSq ((pairPauli r.1 r.2*A).trace))+
    Complex.normSq ((pairPauli 0 0*A).trace)=_ at hs
  rw [hzero] at hs
  have hsC : ((∑ r ∈ nonidentity,Complex.normSq ((pairPauli r.1 r.2*A).trace) : ℝ) : ℂ)+1=
      ((∑ r : Fin 4 × Fin 4,Complex.normSq ((pairPauli r.1 r.2*A).trace) : ℝ) : ℂ) := by
    exact_mod_cast hs
  rw [← htotal,← hsC]
  ring

end MainTheory.PairPauliExpansion
