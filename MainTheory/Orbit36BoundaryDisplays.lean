import Mathlib

set_option autoImplicit false

namespace MainTheory.Orbit36BoundaryDisplays

theorem two_active_degree_sum {D1 D2 p1 p2 : ℝ}
    (h1 : D1 = p1+1/10) (h2 : D2 = p2+1/10) (hp : p1+p2 = 2/5) :
    D1+D2 = p1+p2+1/5 ∧ D1+D2 = 3/5 := by constructor <;> linarith

theorem missing_edge_ratios {a b c d r s : ℂ} (hs : s ≠ 0)
    (h1 : a*r+c*s=0) (h2 : b*r+d*s=0) : c = -a*r/s ∧ d = -b*r/s := by
  constructor
  · apply (eq_div_iff hs).mpr
    linear_combination h1
  · apply (eq_div_iff hs).mpr
    linear_combination h2

theorem missing_edge_matching {a b c d r s : ℂ} (hs : s ≠ 0)
    (h1 : a*r+c*s=0) (h2 : b*r+d*s=0) (hm : a*d+b*c=0) : -2*a*b*r/s=0 := by
  apply (div_eq_iff hs).mpr
  linear_combination s*hm-a*h2-b*h1

theorem multiplicity_one_equations {a b delta : ℝ}
    (h1 : a+b+delta=a+3*b) (h2 : a*b+a*delta+b*delta=1/10)
    (he2 : 3*a*b+3*b^2=2/5) :
    delta=2*b ∧ 3*a*b+2*b^2=1/10 ∧ 3*a*b+3*b^2=2/5 := by
  have hd : delta=2*b := by linarith
  rw [hd] at h2
  exact ⟨hd, by nlinarith, he2⟩

theorem multiplicity_two_equations {a b delta : ℝ}
    (h1 : a+b+delta=2*a+2*b) (h2 : a*b+a*delta+b*delta=1/10)
    (he2 : a^2+4*a*b+b^2=2/5) :
    delta=a+b ∧ a^2+3*a*b+b^2=1/10 ∧ a^2+4*a*b+b^2=2/5 := by
  have hd : delta=a+b := by linarith
  rw [hd] at h2
  exact ⟨hd, by nlinarith, he2⟩

theorem multiplicity_one_impossible {a b : ℝ} (ha : 0<a) (hb : 0<b)
    (h1 : 3*a*b+2*b^2=1/10) (h2 : 3*a*b+3*b^2=2/5) : False := by
  nlinarith [mul_pos ha hb]

theorem multiplicity_two_impossible {a b : ℝ}
    (h1 : a^2+3*a*b+b^2=1/10) (h2 : a^2+4*a*b+b^2=2/5) : False := by
  nlinarith [sq_nonneg a, sq_nonneg b]

end MainTheory.Orbit36BoundaryDisplays
