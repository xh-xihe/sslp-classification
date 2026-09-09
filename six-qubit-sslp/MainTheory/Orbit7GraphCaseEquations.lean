import SixQubit.Orbit7Boundary

set_option autoImplicit false

namespace MainTheory.Orbit7GraphCaseEquations

open SixQubit.Orbit7Universal

theorem bipartite_equations (x : Fin 5 × Fin 5 → ℂ)
    (hH : ∀ i, Hafnian5 x i = 0)
    (h23 : x (2,3)=0) (h24 : x (2,4)=0) (h34 : x (3,4)=0) :
    x (0,3)*x (1,4)+x (0,4)*x (1,3)=0 ∧
    x (0,2)*x (1,4)+x (0,4)*x (1,2)=0 ∧
    x (0,2)*x (1,3)+x (0,3)*x (1,2)=0 := by
  exact ⟨by simpa [Hafnian5,h34] using hH 2,
    by simpa [Hafnian5,h24] using hH 3,
    by simpa [Hafnian5,h23] using hH 4⟩

theorem missing_edge_equations (x : Fin 5 × Fin 5 → ℂ)
    (hH : ∀ i, Hafnian5 x i = 0) (h34 : x (3,4)=0) :
    x (1,3)*x (2,4)+x (1,4)*x (2,3)=0 ∧
    x (0,3)*x (2,4)+x (0,4)*x (2,3)=0 ∧
    x (0,3)*x (1,4)+x (0,4)*x (1,3)=0 := by
  exact ⟨by simpa [Hafnian5,h34] using hH 0,
    by simpa [Hafnian5,h34] using hH 1,
    by simpa [Hafnian5,h34] using hH 2⟩

theorem ratio_from_two_rows (a b c d e f : ℂ)
    (hb : b ≠ 0) (hd : d ≠ 0) (hf : f ≠ 0)
    (h1 : a*f+e*c=0) (h2 : b*f+e*d=0) : a/b=c/d := by
  have hz : f*(a*d-b*c)=0 := by linear_combination d*h1-c*h2
  have hp : a*d-b*c=0 := (mul_eq_zero.mp hz).resolve_left hf
  field_simp
  linear_combination hp

theorem negative_ratio_from_third (a b c d : ℂ)
    (hb : b ≠ 0) (hd : d ≠ 0) (h : b*c+a*d=0) : a/b= -c/d := by
  field_simp
  linear_combination h

end MainTheory.Orbit7GraphCaseEquations
