import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MainTheory.DeterminantOneCyclicConvention

noncomputable def G (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![z,z⁻¹]

theorem determinant (z : ℂ) (hz : z ≠ 0) : (G z).det=1 := by
  simp [G,Matrix.det_diagonal,Fin.prod_univ_two,hz]

theorem power_iff (z : ℂ) (k : ℕ) : (G z)^k=1 ↔ z^k=1 := by
  constructor
  · intro h
    have h0 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
    simpa [G,Matrix.diagonal_pow] using h0
  · intro h
    ext i j
    fin_cases i <;> fin_cases j <;> simp [G,Matrix.diagonal_pow,inv_pow,h]

theorem generator_order (m : ℕ) (z : ℂ) (hz : IsPrimitiveRoot z (2*m)) :
    orderOf (G z)=2*m := by
  have h : orderOf (G z)=orderOf z := orderOf_eq_orderOf_iff.mpr (power_iff z)
  exact h.trans hz.eq_orderOf.symm

theorem projective_ratio (m : ℕ) (hm : 0 < m) (z : ℂ)
    (hz : IsPrimitiveRoot z (2*m)) : IsPrimitiveRoot (z/z⁻¹) m := by
  have h : z/z⁻¹=z^2 := by simp [div_eq_mul_inv,pow_two]
  rw [h]
  exact hz.pow (by omega) rfl

theorem unitary (z : ℂ) (hn : ‖z‖=1) : (G z).conjTranspose*G z=1 := by
  have hs : Complex.normSq z=1 := by rw [Complex.normSq_eq_norm_sq,hn,one_pow]
  have hi : z⁻¹=star z := by simp [Complex.inv_def,hs]
  have hstar : (starRingEnd ℂ) z*z=1 := by
    rw [← Complex.normSq_eq_conj_mul_self,hs]
    norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [G,Matrix.mul_apply,Fin.sum_univ_two,hi,hstar,mul_comm z ((starRingEnd ℂ) z)]

theorem convention (m : ℕ) (hm : 0 < m) (z : ℂ) (hz : IsPrimitiveRoot z (2*m)) :
    (G z).det=1 ∧ (G z).conjTranspose*G z=1 ∧
    orderOf (G z)=2*m ∧ orderOf (z/z⁻¹)=m := by
  exact ⟨determinant z (hz.ne_zero (by omega)),unitary z (hz.norm'_eq_one (by omega)),
    generator_order m z hz,(projective_ratio m hm z hz).eq_orderOf.symm⟩

theorem exists_convention (m : ℕ) (hm : 0 < m) : ∃ z : ℂ,
    (G z).det=1 ∧ (G z).conjTranspose*G z=1 ∧
    orderOf (G z)=2*m ∧ orderOf (z/z⁻¹)=m := by
  exact ⟨_,convention m hm _ (Complex.isPrimitiveRoot_exp (2*m) (by omega))⟩

end MainTheory.DeterminantOneCyclicConvention
