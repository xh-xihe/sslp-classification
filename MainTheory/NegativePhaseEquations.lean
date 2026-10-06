import MainTheory.ComplementPhaseRatios
import MainTheory.OrderSeven58PhaseAlgebra

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MainTheory.NegativePhaseEquations

theorem from_anchor (a b u v : ℂ) (hb : b ≠ 0)
    (h : star b*u+star a*v=0) : u= -MainTheory.ComplementPhaseRatios.rho b v*star a := by
  have hb' : star b ≠ 0 := star_ne_zero.mpr hb
  change u= -(v/star b)*star a
  field_simp [hb']
  linear_combination h

theorem four_binomial (r a b c d u v w x : ℂ) (hr : r ≠ 0)
    (hu : u= -r*star a) (hv : v= -r*star b)
    (hw : w= -r*star c) (hx : x= -r*star d)
    (h : star a*v+star c*x+star d*w+star b*u=0) : a*b+c*d=0 := by
  apply MainTheory.OrderSeven58PhaseAlgebra.fatal_equation (-r) _ _ _ _ (neg_ne_zero.mpr hr)
  rw [hu,hv,hw,hx] at h
  simp only [star_mul']
  linear_combination h

theorem binomial_magnitudes (a b c d : ℂ) (h : a*b+c*d=0) :
    Complex.normSq a*Complex.normSq b=Complex.normSq c*Complex.normSq d := by
  have he : a*b= -(c*d) := eq_neg_of_add_eq_zero_left h
  have hn := congrArg Complex.normSq he
  simpa only [Complex.normSq_mul,Complex.normSq_neg] using hn

theorem ratio (a b c d : ℂ) (hb : b ≠ 0) (hd : d ≠ 0)
    (h : a*d+b*c=0) : a/b= -(c/d) := by
  field_simp [hb,hd]
  linear_combination h

theorem odd_binomials (a b c d e f : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0) (hf : f ≠ 0)
    (h1 : a*f+b*e=0) (h2 : c*f+d*e=0) (h3 : a*d+b*c=0) : False := by
  have hpos : a/b=c/d := (ratio a b e f hb hf h1).trans (ratio c d e f hd hf h2).symm
  have hneg := ratio a b c d hb hd h3
  have hz : a/b=0 := by linear_combination (hpos+hneg)/2
  exact div_ne_zero ha hb hz

end MainTheory.NegativePhaseEquations
