import Mathlib

set_option autoImplicit false

namespace MainTheory.AntisymmetricTriangleRatios

theorem edge_ratio (a b u v : ℂ) (hb : b ≠ 0) (hv : v ≠ 0) :
    star b*u+star a*v=0 ↔ u/v= -(star a/star b) := by
  have hb' : star b ≠ 0 := star_ne_zero.mpr hb
  field_simp
  constructor <;> intro h <;> linear_combination h

theorem positive (a b c u v w : ℂ) (hb : b ≠ 0) (hv : v ≠ 0)
    (h1 : u/v= -(star a/star b)) (h2 : v/w= -(star b/star c)) :
    u/w=star a/star c := by
  calc
    u/w=(u/v)*(v/w) := by field_simp
    _=(-(star a/star b))*(-(star b/star c)) := by rw [h1,h2]
    _=star a/star c := by
      have hb' : star b ≠ 0 := star_ne_zero.mpr hb
      field_simp

theorem incompatible (a c u w : ℂ) (ha : a ≠ 0) (hc : c ≠ 0)
    (hp : u/w=star a/star c) (hm : u/w= -(star a/star c)) : False := by
  have h : star a/star c=0 := by linear_combination (hm-hp)/2
  exact (div_ne_zero (star_ne_zero.mpr ha) (star_ne_zero.mpr hc)) h

end MainTheory.AntisymmetricTriangleRatios
