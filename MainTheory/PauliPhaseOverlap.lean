import SS.HilbertKL

set_option autoImplicit false

namespace MainTheory.PauliPhaseOverlap

theorem overlap {n : ℕ} (psi phi : SS.State n ℂ) (P : SS.PauliString n) (kappa : ℕ) :
    SS.innerC psi (fun x =>
      ((Complex.I ^ kappa) / (Complex.I ^ P.numY)) * SS.pauliAct P phi x) =
      (Complex.I ^ kappa) * ∑ x,
        SS.signC (SS.bdot P.z x) (star (psi (SS.bxor x P.x)) * phi x) := by
  have hscalar (a : ℂ) (v : SS.State n ℂ) :
      SS.innerC psi (fun x => a*v x) = a*SS.innerC psi v := by
    simp only [SS.innerC, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hscalar, SS.innerC_pauliAct]
  have hn : Complex.I ^ P.numY ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
  field_simp

end MainTheory.PauliPhaseOverlap
