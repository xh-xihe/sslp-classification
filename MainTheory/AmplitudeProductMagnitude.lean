import MainTheory.ComplementPhaseRatios

set_option autoImplicit false

namespace MainTheory.AmplitudeProductMagnitude

theorem equal_products {n : ℕ} (c d : Fin n → ℂ) (p : Fin n → ℝ)
    (hc : ∀ i,Complex.normSq (c i)=p i) (hd : ∀ i,Complex.normSq (d i)=p i)
    (a b e f : Fin n) (h : star (c e)*d f= -(star (c a)*d b)) :
    p a*p b=p e*p f := by
  have hn := congrArg Complex.normSq h
  simp only [Complex.normSq_neg,Complex.normSq_mul,Complex.star_def,Complex.normSq_conj,hc,hd] at hn
  exact hn.symm

end MainTheory.AmplitudeProductMagnitude
