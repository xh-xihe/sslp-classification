import MainTheory.OrderTwoLabelScalars

/-! The individual B-A inequality has an exact sum-of-squares witness. -/

namespace MainTheory.Orbit3PrintedScalarInequality
noncomputable section
open MainTheory.OrderTwoLabelScalars SS.MacWilliams
open scoped BigOperators

theorem difference (psi : Fin 2 → SS.State 6 ℂ) (P : SS.PauliString 6) :
    4*(b psi P-a psi P)=
      Complex.normSq (SS.innerC (psi 0) (SS.pauliAct P (psi 0))-
        SS.innerC (psi 1) (SS.pauliAct P (psi 1)))+
      2*Complex.normSq (SS.innerC (psi 0) (SS.pauliAct P (psi 1)))+
      2*Complex.normSq (SS.innerC (psi 1) (SS.pauliAct P (psi 0))) := by
  simp only [a,b,frob,trProj,Fin.sum_univ_two, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  ring

theorem a_le_b (psi : Fin 2 → SS.State 6 ℂ) (P : SS.PauliString 6) :
    a psi P ≤ b psi P := by
  have hd := difference psi P
  have h0 := Complex.normSq_nonneg (SS.innerC (psi 0) (SS.pauliAct P (psi 0))-
    SS.innerC (psi 1) (SS.pauliAct P (psi 1)))
  have h1 := Complex.normSq_nonneg (SS.innerC (psi 0) (SS.pauliAct P (psi 1)))
  have h2 := Complex.normSq_nonneg (SS.innerC (psi 1) (SS.pauliAct P (psi 0)))
  linarith

end
end MainTheory.Orbit3PrintedScalarInequality
