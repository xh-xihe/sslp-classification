import Mathlib

/-! The manuscript phase quotient d/conjugate(c), with all cancellation
hypotheses explicit. Unit modulus and reciprocal opposition are independent
of any final exclusion theorem. -/
set_option autoImplicit false
namespace MainTheory.PhysicalPhaseQuotients
noncomputable section
def rho (c d : ℂ) : ℂ := d/star c
theorem nonzero (c d : ℂ) (hc : c≠0) (hd : d≠0) : rho c d≠0 :=
  div_ne_zero hd (star_ne_zero.2 hc)
theorem unit (c d : ℂ) (hc : c≠0) (hm : Complex.normSq d=Complex.normSq c) :
    Complex.normSq (rho c d)=1 := by
  rw [rho,Complex.normSq_div]
  change Complex.normSq d/Complex.normSq ((starRingEnd ℂ) c)=1
  rw [Complex.normSq_conj,hm]
  exact div_self (mt Complex.normSq_eq_zero.1 hc)
theorem opposition (c d b e : ℂ) (hc : c≠0) (hb : b≠0)
    (hr : star c*e+star b*d=0) : rho c d+rho b e=0 := by
  rw [rho,rho,div_add_div _ _ (star_ne_zero.2 hc) (star_ne_zero.2 hb)]
  have he : d*star b+star c*e=0 := by linear_combination hr
  rw [he,zero_div]
theorem equality (c d b e : ℂ) (hc : c≠0) (hb : b≠0)
    (hr : star c*e=star b*d) : rho c d=rho b e := by
  apply (div_eq_div_iff (star_ne_zero.2 hc) (star_ne_zero.2 hb)).2
  linear_combination -hr
end
end MainTheory.PhysicalPhaseQuotients
