import Mathlib

set_option autoImplicit false

namespace MainTheory.ComplementPhaseRatios

noncomputable def rho (c d : ℂ) := d/star c
noncomputable def z (c d : ℂ) := star c*d

theorem unit_norm (c d : ℂ) (hc : c ≠ 0) (h : Complex.normSq c=Complex.normSq d) :
    ‖rho c d‖=1 := by
  have hn : ‖c‖=‖d‖ := by
    have h1 := Complex.sq_norm c
    have h2 := Complex.sq_norm d
    nlinarith [norm_nonneg c,norm_nonneg d]
  simp only [rho,norm_div,norm_star]
  rw [← hn,div_self (norm_ne_zero_iff.mpr hc)]

theorem factor (a b d : ℂ) (hb : b ≠ 0) : z a d=rho b d*star (a*b) := by
  have hb' : star b ≠ 0 := star_ne_zero.mpr hb
  simp only [z,rho,star_mul']
  field_simp

theorem antisymmetric (a b u v : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : z a v+z b u=0) : rho b v= -rho a u := by
  have ha' : star a ≠ 0 := star_ne_zero.mpr ha
  have hb' : star b ≠ 0 := star_ne_zero.mpr hb
  change v/star b= -(u/star a)
  field_simp [ha',hb']
  change star a*v+star b*u=0 at h
  linear_combination h

theorem symmetric (a b u v : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : z a v-z b u=0) : rho b v=rho a u := by
  have ha' : star a ≠ 0 := star_ne_zero.mpr ha
  have hb' : star b ≠ 0 := star_ne_zero.mpr hb
  change v/star b=u/star a
  field_simp [ha',hb']
  change star a*v-star b*u=0 at h
  linear_combination h

end MainTheory.ComplementPhaseRatios
