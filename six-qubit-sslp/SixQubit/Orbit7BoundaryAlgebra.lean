import SixQubit.Orbit7UniversalScalar

/-!
# Orbit 7: division-free boundary-support contradictions

Both non-star proper-support templates reduce three hafnian equations to the
same six-nonzero-scalar pattern.  The certificate below is polynomial: it
uses no division by an amplitude.
-/

namespace SixQubit.Orbit7BoundaryAlgebra

open scoped BigOperators
open SixQubit.Orbit7Universal

/-- Three alternating two-term equations with six nonzero factors are
inconsistent.  Multiplying the equations by `f`, `-c`, and `d` respectively
gives `2*a*d*f = 0`. -/
theorem three_two_term_contradiction
    (a b c d e f : ℂ)
    (ha : a ≠ 0) (hd : d ≠ 0) (hf : f ≠ 0)
    (h1 : a*d + b*c = 0)
    (h2 : e*d + b*f = 0)
    (h3 : e*c + a*f = 0) : False := by
  have hz : 2*a*d*f = 0 := by
    linear_combination f*h1 - c*h2 + d*h3
  exact (mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) ha) hd) hf) hz

/-- The star support is incompatible with the scalar normal form once the
chosen spinor component has mass at least `1/2`.  This is the manuscript's
`x`-mass argument, stated without choosing a spinor basis here. -/
theorem star_mass_contradiction
    (c : SS.State 6 ℂ) (x : Fin 5 → Fin 5 → ℂ) (s : Fin 5)
    (hzero : ∀ e ∈ edgePairs, e ∉ incidentPairs s → x e.1 e.2 = 0)
    (hle : ∀ e ∈ edgePairs,
      Complex.normSq (x e.1 e.2) ≤ aMass c e.1 e.2)
    (hlarge : (1/2 : ℝ) ≤
      ∑ e ∈ edgePairs, Complex.normSq (x e.1 e.2))
    (hdeg : degreeA c s = 1/3) : False := by
  have heq :
      (∑ e ∈ edgePairs, Complex.normSq (x e.1 e.2)) =
        ∑ e ∈ incidentPairs s, Complex.normSq (x e.1 e.2) := by
    symm
    apply Finset.sum_subset (incident_subset s)
    intro e he hnot
    rw [hzero e he hnot, Complex.normSq_zero]
  have hsum :
      (∑ e ∈ incidentPairs s, Complex.normSq (x e.1 e.2)) ≤
        ∑ e ∈ incidentPairs s, aMass c e.1 e.2 := by
    apply Finset.sum_le_sum
    intro e he
    exact hle e ((incident_subset s) he)
  change (∑ e ∈ incidentPairs s, aMass c e.1 e.2) = 1/3 at hdeg
  rw [heq] at hlarge
  linarith

end SixQubit.Orbit7BoundaryAlgebra
