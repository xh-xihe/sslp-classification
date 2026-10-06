import SixQubit.Orbit7FullTangent

set_option autoImplicit false

namespace MainTheory.Orbit7VertexScaling

open SixQubit.Orbit7Universal

abbrev Edge := Fin 5 × Fin 5

noncomputable def scale (v : Fin 5 → ℂ) (x : Edge → ℂ) (e : Edge) : ℂ :=
  v e.1*v e.2*x e

noncomputable def tangent (x : Edge → ℂ) (r : Fin 5 → ℂ) (e : Edge) : ℂ :=
  (r e.1+r e.2)*x e

theorem scale_hafnian (v : Fin 5 → ℂ) (x : Edge → ℂ) (i : Fin 5) :
    Hafnian5 (scale v x) i = (∏ j : Fin 5, if j=i then 1 else v j)*Hafnian5 x i := by
  fin_cases i <;> simp [Hafnian5,scale,Fin.prod_univ_succ] <;> ring

theorem scale_preserves (v : Fin 5 → ℂ) (x : Edge → ℂ) (h : ∀ i, Hafnian5 x i=0) :
    ∀ i, Hafnian5 (scale v x) i=0 := by
  intro i
  rw [scale_hafnian,h i,mul_zero]

theorem scale_iff (v : Fin 5 → ℂ) (hv : ∀ i, v i ≠ 0) (x : Edge → ℂ) :
    (∀ i, Hafnian5 (scale v x) i=0) ↔ ∀ i, Hafnian5 x i=0 := by
  constructor
  · intro h i
    have hp : (∏ j : Fin 5, if j=i then (1 : ℂ) else v j) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro j _
      split_ifs <;> simp_all
    have hi := h i
    rw [scale_hafnian] at hi
    exact (mul_eq_zero.mp hi).resolve_left hp
  · exact scale_preserves v x

theorem tangent_hafnian (x : Edge → ℂ) (r : Fin 5 → ℂ) (i : Fin 5) :
    PolarHafnian5 x (tangent x r) i =
      (∑ j : Fin 5, if j=i then 0 else r j)*Hafnian5 x i := by
  fin_cases i <;> simp [Hafnian5,PolarHafnian5,tangent,Fin.sum_univ_succ] <;> ring

theorem tangent_preserves (x : Edge → ℂ) (h : ∀ i,Hafnian5 x i=0) (r : Fin 5 → ℂ) :
    ∀ i, PolarHafnian5 x (tangent x r) i=0 := by
  intro i
  rw [tangent_hafnian,h i,mul_zero]

theorem tangent_injective (x : Edge → ℂ) (hx : FullEdgeSupport x) (r s : Fin 5 → ℂ)
    (h : ∀ e ∈ edgePairs, tangent x r e = tangent x s e) : r=s := by
  have hs (e : Edge) (he : e ∈ edgePairs) : r e.1+r e.2=s e.1+s e.2 := by
    have hh := h e he
    exact (mul_right_cancel₀ (hx e he)) hh
  have h01 := hs (0,1) (by decide)
  have h02 := hs (0,2) (by decide)
  have h03 := hs (0,3) (by decide)
  have h04 := hs (0,4) (by decide)
  have h12 := hs (1,2) (by decide)
  have h0 : r 0=s 0 := by linear_combination (h01+h02-h12)/2
  funext i
  fin_cases i
  · exact h0
  · change r 1 = s 1
    linear_combination h01-h0
  · change r 2 = s 2
    linear_combination h02-h0
  · change r 3 = s 3
    linear_combination h03-h0
  · change r 4 = s 4
    linear_combination h04-h0

end MainTheory.Orbit7VertexScaling
