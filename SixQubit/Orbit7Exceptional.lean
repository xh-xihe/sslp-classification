import SixQubit.Orbit7FullTangent

/-!
# Orbit 7: the affine-polar and exceptional-vertex algebra

This file contains the purely algebraic part of the full-support branch.  In
particular, the normal form used below is obtained from `full_hafnian_chart`;
none of its coordinates, nor the equal-product conclusion, is assumed by the
public exceptional-vertex theorem.
-/

open scoped BigOperators ComplexConjugate

namespace SixQubit.Orbit7Universal

noncomputable section

set_option maxHeartbeats 4000000

/-- The exact conclusion supplied by `full_hafnian_chart`, separated as a
predicate so the polynomial exceptional-vertex bridge can be audited on its
own. -/
def HasFullHafnianChart (x : Fin 5 × Fin 5 → ℂ) : Prop :=
  ∃ tau omega : ℂ,
    tau ≠ 0 ∧ 1 + omega + omega^2 = 0 ∧
    x (1,2) / (x (0,1) * x (0,2)) = tau ∧
    x (3,4) / (x (0,3) * x (0,4)) = tau ∧
    x (1,3) / (x (0,1) * x (0,3)) = tau * omega ∧
    x (2,4) / (x (0,2) * x (0,4)) = tau * omega ∧
    x (1,4) / (x (0,1) * x (0,4)) = tau * omega^2 ∧
    x (2,3) / (x (0,2) * x (0,3)) = tau * omega^2

theorem has_full_hafnian_chart (x : Fin 5 × Fin 5 → ℂ)
    (hx : FullEdgeSupport x) (hH : ∀ v, Hafnian5 x v = 0) :
    HasFullHafnianChart x :=
  full_hafnian_chart x hx hH

/-- If the second tangent vector is an affine combination of the first one
and the base point, the mixed `y,z` polar equations force all five hafnians
of `y` to vanish.  This is the exact polynomial content of
Eq. (o7Hyzero), without division by an edge coordinate. -/
theorem hafnian_y_zero_of_affine_polar
    (x y z : Fin 5 × Fin 5 → ℂ) (mu nu : ℂ)
    (hz : ∀ e, z e = mu * y e + nu * x e)
    (hmu : mu ≠ 0)
    (hxy : ∀ v, PolarHafnian5 x y v = 0)
    (hyz : ∀ v, PolarHafnian5 y z v = 0) :
    ∀ v, Hafnian5 y v = 0 := by
  intro v
  have hxyv := hxy v
  have hyzv := hyz v
  have hz01 := hz (0, 1)
  have hz02 := hz (0, 2)
  have hz03 := hz (0, 3)
  have hz04 := hz (0, 4)
  have hz12 := hz (1, 2)
  have hz13 := hz (1, 3)
  have hz14 := hz (1, 4)
  have hz23 := hz (2, 3)
  have hz24 := hz (2, 4)
  have hz34 := hz (3, 4)
  fin_cases v <;>
    simp [PolarHafnian5, Hafnian5] at hxyv hyzv ⊢ <;>
    simp only [hz01, hz02, hz03, hz04, hz12, hz13, hz14,
      hz23, hz24, hz34] at hyzv
  · have hfac : (2 * mu) *
        (y (1,2) * y (3,4) + y (1,3) * y (2,4) +
          y (1,4) * y (2,3)) = 0 := by
      linear_combination hyzv - nu * hxyv
    exact (mul_eq_zero.mp hfac).resolve_left
      (mul_ne_zero (by norm_num) hmu)
  · have hfac : (2 * mu) *
        (y (0,2) * y (3,4) + y (0,3) * y (2,4) +
          y (0,4) * y (2,3)) = 0 := by
      linear_combination hyzv - nu * hxyv
    exact (mul_eq_zero.mp hfac).resolve_left
      (mul_ne_zero (by norm_num) hmu)
  · have hfac : (2 * mu) *
        (y (0,1) * y (3,4) + y (0,3) * y (1,4) +
          y (0,4) * y (1,3)) = 0 := by
      linear_combination hyzv - nu * hxyv
    exact (mul_eq_zero.mp hfac).resolve_left
      (mul_ne_zero (by norm_num) hmu)
  · have hfac : (2 * mu) *
        (y (0,1) * y (2,4) + y (0,2) * y (1,4) +
          y (0,4) * y (1,2)) = 0 := by
      linear_combination hyzv - nu * hxyv
    exact (mul_eq_zero.mp hfac).resolve_left
      (mul_ne_zero (by norm_num) hmu)
  · have hfac : (2 * mu) *
        (y (0,1) * y (2,3) + y (0,2) * y (1,3) +
          y (0,3) * y (1,2)) = 0 := by
      linear_combination hyzv - nu * hxyv
    exact (mul_eq_zero.mp hfac).resolve_left
      (mul_ne_zero (by norm_num) hmu)

/-- Kernel row reduction of the five equations in the normalized hafnian
chart.  The inputs are exactly the five normalized `H_i(y)=0` equations;
the six pair products are conclusions, not hypotheses. -/
theorem equal_products_of_normalized_hafnians
    (omega r0 r1 r2 r3 r4 : ℂ)
    (homega : 1 + omega + omega^2 = 0)
    (h0 : (r1+r2)*(r3+r4) + omega^2*(r1+r3)*(r2+r4) +
      omega^4*(r1+r4)*(r2+r3) = 0)
    (h1 : (r0+r2)*(r3+r4) + omega*(r0+r3)*(r2+r4) +
      omega^2*(r0+r4)*(r2+r3) = 0)
    (h2 : (r0+r1)*(r3+r4) + omega^2*(r0+r3)*(r1+r4) +
      omega*(r0+r4)*(r1+r3) = 0)
    (h3 : omega*(r0+r1)*(r2+r4) + omega^2*(r0+r2)*(r1+r4) +
      (r0+r4)*(r1+r2) = 0)
    (h4 : omega^2*(r0+r1)*(r2+r3) + omega*(r0+r2)*(r1+r3) +
      (r0+r3)*(r1+r2) = 0) :
    let x0 := r0-r4
    let x1 := r1-r4
    let x2 := r2-r4
    let x3 := r3-r4
    x0*x1 = x0*x2 ∧ x0*x1 = x0*x3 ∧
      x0*x1 = x1*x2 ∧ x0*x1 = x1*x3 ∧ x0*x1 = x2*x3 := by
  dsimp
  have e0 :
      -(r1-r4)*(r2-r4) + (omega+1)*(r1-r4)*(r3-r4) -
        omega*(r2-r4)*(r3-r4) = 0 := by
    linear_combination h0 -
      (r1*r2*omega^2-r1*r2*omega+r1*r2+
       r1*r3*omega^2-r1*r3*omega+r1*r4+r2*r3+
       r2*r4*omega^2-r2*r4*omega+r3*r4*omega^2-r3*r4*omega+r3*r4) * homega
  have e1 :
      -(r0-r4)*(r2-r4) - omega*(r0-r4)*(r3-r4) +
        (omega+1)*(r2-r4)*(r3-r4) = 0 := by
    linear_combination h1 - (r0+r4)*(r2+r3) * homega
  have e2 :
      -(r0-r4)*(r1-r4) + (omega+1)*(r0-r4)*(r3-r4) -
        omega*(r1-r4)*(r3-r4) = 0 := by
    linear_combination h2 - (r0+r3)*(r1+r4) * homega
  have e3 :
      -omega*(r0-r4)*(r1-r4) + (omega+1)*(r0-r4)*(r2-r4) -
        (r1-r4)*(r2-r4) = 0 := by
    linear_combination h3 - (r0+r2)*(r1+r4) * homega
  have e4 :
      (omega+1)*(r0-r4)*(r1-r4) - omega*(r0-r4)*(r2-r4) -
        (r0-r4)*(r3-r4) - (r1-r4)*(r2-r4) -
        omega*(r1-r4)*(r3-r4) + (omega+1)*(r2-r4)*(r3-r4) = 0 := by
    linear_combination h4 - (r0+r1)*(r2+r3) * homega
  constructor
  · linear_combination
      (-1/6-omega/3)*e0 + (1/3+omega/6)*e1 +
      (-1/6+omega/6)*e2 + (1/3+2*omega/3)*e3 +
      (-1/6-omega/3)*e4 +
      ((r0-r4)*(r1-r4)-(r0-r4)*(r2-r4)+(r1-r4)*(r3-r4)/6-
        (r2-r4)*(r3-r4)/6) * homega
  constructor
  · linear_combination
      (-1/3-omega/6)*e0 + (-1/3-omega/6)*e1 +
      (-1/3+omega/3)*e2 + (1/6+omega/3)*e3 +
      (1/6-omega/6)*e4 +
      ((r0-r4)*(r1-r4)/2-(r0-r4)*(r2-r4)/2-
        (r0-r4)*(r3-r4)/2+(r1-r4)*(r3-r4)/3+
        (r2-r4)*(r3-r4)/6) * homega
  constructor
  · linear_combination
      (1/6-omega/6)*e0 + (1/6+omega/3)*e1 +
      (-1/3-omega/6)*e2 + (2/3+omega/3)*e3 +
      (1/6-omega/6)*e4 +
      ((r0-r4)*(r1-r4)/2-(r0-r4)*(r2-r4)/2+
        (r0-r4)*(r3-r4)/2-(r1-r4)*(r3-r4)/6-
        (r2-r4)*(r3-r4)/3) * homega
  constructor
  · linear_combination
      (-1/6+omega/6)*e0 + (-1/6+omega/6)*e1 +
      (-2/3-omega/3)*e2 + (1/3+omega/6)*e3 +
      (-1/6-omega/3)*e4 +
      ((r0-r4)*(r1-r4)/2-(r0-r4)*(r2-r4)/2+
        (r0-r4)*(r3-r4)/2-5*(r1-r4)*(r3-r4)/6+
        (r2-r4)*(r3-r4)/3) * homega
  · linear_combination
      (-1/2-omega/2)*e0 + (omega/2)*e1 + (-1/2)*e2 +
      (1/2+omega/2)*e3 +
      ((r0-r4)*(r1-r4)/2-(r0-r4)*(r2-r4)/2+
        (r0-r4)*(r3-r4)/2+(r1-r4)*(r3-r4)/2-
        (r2-r4)*(r3-r4)) * homega

/-- The normalized chart supplied by `full_hafnian_chart`, together with the
genuine vertex-tangent representation and the five equations `H_i(y)=0`,
forces one exceptional vertex.  The witness `r` returned here is the actual
witness representing `y`, not a chart coordinate introduced as a premise. -/
theorem exceptional_vertex_of_full_chart
    (x y : Fin 5 × Fin 5 → ℂ)
    (hx : FullEdgeSupport x)
    (ht : IsVertexTangent x y)
    (hHy : ∀ v, Hafnian5 y v = 0)
    (hchart : HasFullHafnianChart x) :
    ∃ r : Fin 5 → ℂ, (∀ e ∈ edgePairs,
        y e = (r e.1 + r e.2) * x e) ∧
      ∃ s : Fin 5, ∃ R : ℂ, ∀ i, i ≠ s → r i = R := by
  rcases ht with ⟨r, hr⟩
  rcases hchart with
    ⟨tau, omega, htau, homega, ht12, ht34, ht13, ht24, ht14, ht23⟩
  have hx01 : x (0,1) ≠ 0 := hx (0,1) (by decide)
  have hx02 : x (0,2) ≠ 0 := hx (0,2) (by decide)
  have hx03 : x (0,3) ≠ 0 := hx (0,3) (by decide)
  have hx04 : x (0,4) ≠ 0 := hx (0,4) (by decide)
  have xx12 : x (1,2) = tau * (x (0,1) * x (0,2)) :=
    (div_eq_iff (mul_ne_zero hx01 hx02)).mp ht12
  have xx34 : x (3,4) = tau * (x (0,3) * x (0,4)) :=
    (div_eq_iff (mul_ne_zero hx03 hx04)).mp ht34
  have xx13 : x (1,3) = (tau*omega) * (x (0,1) * x (0,3)) :=
    (div_eq_iff (mul_ne_zero hx01 hx03)).mp ht13
  have xx24 : x (2,4) = (tau*omega) * (x (0,2) * x (0,4)) :=
    (div_eq_iff (mul_ne_zero hx02 hx04)).mp ht24
  have xx14 : x (1,4) = (tau*omega^2) * (x (0,1) * x (0,4)) :=
    (div_eq_iff (mul_ne_zero hx01 hx04)).mp ht14
  have xx23 : x (2,3) = (tau*omega^2) * (x (0,2) * x (0,3)) :=
    (div_eq_iff (mul_ne_zero hx02 hx03)).mp ht23
  have hy01 := hr (0,1) (by decide)
  have hy02 := hr (0,2) (by decide)
  have hy03 := hr (0,3) (by decide)
  have hy04 := hr (0,4) (by decide)
  have hy12 := hr (1,2) (by decide)
  have hy13 := hr (1,3) (by decide)
  have hy14 := hr (1,4) (by decide)
  have hy23 := hr (2,3) (by decide)
  have hy24 := hr (2,4) (by decide)
  have hy34 := hr (3,4) (by decide)
  have h0 := hHy 0
  have h1 := hHy 1
  have h2 := hHy 2
  have h3 := hHy 3
  have h4 := hHy 4
  simp [Hafnian5] at h0 h1 h2 h3 h4
  simp only [hy01, hy02, hy03, hy04, hy12, hy13, hy14, hy23,
    hy24, hy34, xx12, xx34, xx13, xx24, xx14, xx23] at h0 h1 h2 h3 h4
  have hf0 :
      (tau^2*x (0,1)*x (0,2)*x (0,3)*x (0,4)) *
        ((r 1+r 2)*(r 3+r 4) + omega^2*(r 1+r 3)*(r 2+r 4) +
          omega^4*(r 1+r 4)*(r 2+r 3)) = 0 := by
    linear_combination h0
  have hf1 :
      (tau*x (0,2)*x (0,3)*x (0,4)) *
        ((r 0+r 2)*(r 3+r 4) + omega*(r 0+r 3)*(r 2+r 4) +
          omega^2*(r 0+r 4)*(r 2+r 3)) = 0 := by
    linear_combination h1
  have hf2 :
      (tau*x (0,1)*x (0,3)*x (0,4)) *
        ((r 0+r 1)*(r 3+r 4) + omega^2*(r 0+r 3)*(r 1+r 4) +
          omega*(r 0+r 4)*(r 1+r 3)) = 0 := by
    linear_combination h2
  have hf3 :
      (tau*x (0,1)*x (0,2)*x (0,4)) *
        (omega*(r 0+r 1)*(r 2+r 4) + omega^2*(r 0+r 2)*(r 1+r 4) +
          (r 0+r 4)*(r 1+r 2)) = 0 := by
    linear_combination h3
  have hf4 :
      (tau*x (0,1)*x (0,2)*x (0,3)) *
        (omega^2*(r 0+r 1)*(r 2+r 3) + omega*(r 0+r 2)*(r 1+r 3) +
          (r 0+r 3)*(r 1+r 2)) = 0 := by
    linear_combination h4
  have hn0 := (mul_eq_zero.mp hf0).resolve_left
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (pow_ne_zero 2 htau) hx01) hx02) hx03) hx04)
  have hn1 := (mul_eq_zero.mp hf1).resolve_left
    (mul_ne_zero (mul_ne_zero (mul_ne_zero htau hx02) hx03) hx04)
  have hn2 := (mul_eq_zero.mp hf2).resolve_left
    (mul_ne_zero (mul_ne_zero (mul_ne_zero htau hx01) hx03) hx04)
  have hn3 := (mul_eq_zero.mp hf3).resolve_left
    (mul_ne_zero (mul_ne_zero (mul_ne_zero htau hx01) hx02) hx04)
  have hn4 := (mul_eq_zero.mp hf4).resolve_left
    (mul_ne_zero (mul_ne_zero (mul_ne_zero htau hx01) hx02) hx03)
  have hp := equal_products_of_normalized_hafnians omega
    (r 0) (r 1) (r 2) (r 3) (r 4) homega hn0 hn1 hn2 hn3 hn4
  rcases hp with ⟨hp01, hp02, hp12, hp13, hp23⟩
  have hcases := equal_pair_products
    (r 0-r 4) (r 1-r 4) (r 2-r 4) (r 3-r 4)
    hp01 hp02 hp12 hp13 hp23
  refine ⟨r, hr, ?_⟩
  rcases hcases with h012 | h013 | h023 | h123 | hall
  · refine ⟨3, r 4, ?_⟩
    intro i hi
    have he0 : r 0 = r 4 := sub_eq_zero.mp h012.1
    have he1 : r 1 = r 4 := sub_eq_zero.mp h012.2.1
    have he2 : r 2 = r 4 := sub_eq_zero.mp h012.2.2
    fin_cases i
    · exact he0
    · exact he1
    · exact he2
    · exact (hi rfl).elim
    · rfl
  · refine ⟨2, r 4, ?_⟩
    intro i hi
    have he0 : r 0 = r 4 := sub_eq_zero.mp h013.1
    have he1 : r 1 = r 4 := sub_eq_zero.mp h013.2.1
    have he3 : r 3 = r 4 := sub_eq_zero.mp h013.2.2
    fin_cases i
    · exact he0
    · exact he1
    · exact (hi rfl).elim
    · exact he3
    · rfl
  · refine ⟨1, r 4, ?_⟩
    intro i hi
    have he0 : r 0 = r 4 := sub_eq_zero.mp h023.1
    have he2 : r 2 = r 4 := sub_eq_zero.mp h023.2.1
    have he3 : r 3 = r 4 := sub_eq_zero.mp h023.2.2
    fin_cases i
    · exact he0
    · exact (hi rfl).elim
    · exact he2
    · exact he3
    · rfl
  · refine ⟨0, r 4, ?_⟩
    intro i hi
    have he1 : r 1 = r 4 := sub_eq_zero.mp h123.1
    have he2 : r 2 = r 4 := sub_eq_zero.mp h123.2.1
    have he3 : r 3 = r 4 := sub_eq_zero.mp h123.2.2
    fin_cases i
    · exact (hi rfl).elim
    · exact he1
    · exact he2
    · exact he3
    · rfl
  · refine ⟨4, r 0, ?_⟩
    have he1 : r 1 = r 0 := by linear_combination -hall.1
    have he2 : r 2 = r 0 := by linear_combination -hall.2.1
    have he3 : r 3 = r 0 := by linear_combination -hall.2.2
    intro i hi
    fin_cases i
    · rfl
    · exact he1
    · exact he2
    · exact he3
    · exact (hi rfl).elim

/-- Public full-support exceptional-vertex theorem.  Its hypotheses are only
full support, the genuine five hafnian equations for `x` and `y`, and an
actual `IsVertexTangent` witness.  The normalized chart is produced inside
the proof by `full_hafnian_chart`. -/
theorem exceptional_vertex_of_full_tangent
    (x y : Fin 5 × Fin 5 → ℂ)
    (hx : FullEdgeSupport x)
    (hHx : ∀ v, Hafnian5 x v = 0)
    (ht : IsVertexTangent x y)
    (hHy : ∀ v, Hafnian5 y v = 0) :
    ∃ r : Fin 5 → ℂ, (∀ e ∈ edgePairs,
        y e = (r e.1 + r e.2) * x e) ∧
      ∃ s : Fin 5, ∃ R : ℂ, ∀ i, i ≠ s → r i = R :=
  exceptional_vertex_of_full_chart x y hx ht hHy
    (has_full_hafnian_chart x hx hHx)

end

end SixQubit.Orbit7Universal
