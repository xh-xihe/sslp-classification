import SixQubit.Orbit7Boundary
import SixQubit.Orbit7HafnianAlgebra

/-!
# Orbit 7 universal converse, V: the full-support tangent chart

This file is the full-support counterpart of the graph reduction.  The
support coordinate is the covariant coordinate `xcoord = v† a` introduced in
`Orbit7Boundary`; hence all equations used below are consequences of the
genuine Knill--Laflamme predicate.

The first part is a division-free certificate for the normalized tangent
system.  The second part transports that certificate to an arbitrary
full-support hafnian point.  The separate `Orbit7PhysicalTangent` module
derives the required polarized equations from the actual `2 × 2` one-flip
matrix and invokes this algebraic result.
-/

namespace SixQubit.Orbit7Universal

open scoped BigOperators ComplexConjugate
open SixQubit SixQubit.Realize

noncomputable section

set_option maxHeartbeats 4000000

/-- Polarization of the five complementary four-vertex hafnians. -/
def PolarHafnian5 (x y : Fin 5 × Fin 5 → ℂ) : Fin 5 → ℂ :=
  ![x (1,2) * y (3,4) + y (1,2) * x (3,4) +
      x (1,3) * y (2,4) + y (1,3) * x (2,4) +
      x (1,4) * y (2,3) + y (1,4) * x (2,3),
    x (0,2) * y (3,4) + y (0,2) * x (3,4) +
      x (0,3) * y (2,4) + y (0,3) * x (2,4) +
      x (0,4) * y (2,3) + y (0,4) * x (2,3),
    x (0,1) * y (3,4) + y (0,1) * x (3,4) +
      x (0,3) * y (1,4) + y (0,3) * x (1,4) +
      x (0,4) * y (1,3) + y (0,4) * x (1,3),
    x (0,1) * y (2,4) + y (0,1) * x (2,4) +
      x (0,2) * y (1,4) + y (0,2) * x (1,4) +
      x (0,4) * y (1,2) + y (0,4) * x (1,2),
    x (0,1) * y (2,3) + y (0,1) * x (2,3) +
      x (0,2) * y (1,3) + y (0,2) * x (1,3) +
      x (0,3) * y (1,2) + y (0,3) * x (1,2)]

/-! ## Exact tangent kernel on the normalized chart -/

/-- Every solution of the five normalized tangent rows has vertex-scaling
form.  This is the explicit elimination certificate needed from the
Jacobian argument in the manuscript. -/
theorem ratio_tangent_vertex
    (omega t01 t02 t03 t04 t12 t13 t14 t23 t24 t34 : ℂ)
    (homega : 1 + omega + omega^2 = 0)
    (e0 : (t12 + t34) + omega^2 * (t13 + t24) +
      omega^4 * (t14 + t23) = 0)
    (e1 : (t02 + t34) + omega * (t03 + t24) +
      omega^2 * (t04 + t23) = 0)
    (e2 : (t01 + t34) + omega^2 * (t03 + t14) +
      omega * (t04 + t13) = 0)
    (e3 : omega * (t01 + t24) + omega^2 * (t02 + t14) +
      (t04 + t12) = 0)
    (e4 : omega^2 * (t01 + t23) + omega * (t02 + t13) +
      (t03 + t12) = 0) :
    ∃ r0 r1 r2 r3 r4 : ℂ,
      t01 = r0 + r1 ∧ t02 = r0 + r2 ∧
      t03 = r0 + r3 ∧ t04 = r0 + r4 ∧
      t12 = r1 + r2 ∧ t13 = r1 + r3 ∧
      t14 = r1 + r4 ∧ t23 = r2 + r3 ∧
      t24 = r2 + r4 ∧ t34 = r3 + r4 := by
  have h13 : t13 = t03 - t02 + t12 := by
    linear_combination
      (-1/6 + omega/6) * e0 + (1/3 + omega/6) * e1 +
      (-1/6 - omega/3) * e2 + (-1/6 + omega/6) * e3 +
      (-2/3 - omega/3) * e4 -
      (t01*(-omega/3 - 1/6) + t02*(omega/6 - 2/3) +
       t03*(1/3 - omega/3) + t04*(omega/6 - 1/6) +
       t13*(omega/6 - 1) + t14*(omega^3/6 - omega^2/3) +
       t23*(omega^3/6 - omega^2/3) + t24*omega/6) * homega
  have h14 : t14 = t04 - t02 + t12 := by
    linear_combination
      (-1/3 - omega/6) * e0 + (1/6 - omega/6) * e1 +
      (1/6 + omega/3) * e2 + (-1/3 + omega/3) * e3 +
      (-1/3 - omega/6) * e4 -
      (t01*(1/6 - omega/6) + t02*(omega/3 - 5/6) +
       t03*(omega/3 - 1/3) + t04*(2/3 - omega/6) - t13*omega/6 +
       t14*(-omega^3/6 - omega^2/6 + omega - 1) +
       t23*(-omega^3/6 - omega^2/6) - t24*omega/6) * homega
  have h23 : t23 = t03 - t01 + t12 := by
    linear_combination
      (-1/3 - omega/6) * e0 + (1/6 + omega/3) * e1 +
      (1/6 - omega/6) * e2 + (-1/3 - omega/6) * e3 +
      (-1/3 + omega/3) * e4 -
      (t01*(omega/3 - 5/6) + t02*(1/6 - omega/6) +
       t03*(2/3 - omega/6) + t04*(omega/3 - 1/3) - t13*omega/6 +
       t14*(-omega^3/6 - omega^2/6) +
       t23*(-omega^3/6 - omega^2/6 + omega - 1) - t24*omega/6) * homega
  have h24 : t24 = t04 - t01 + t12 := by
    linear_combination
      (-1/6 + omega/6) * e0 + (-1/6 - omega/3) * e1 +
      (1/3 + omega/6) * e2 + (-2/3 - omega/3) * e3 +
      (-1/6 + omega/6) * e4 -
      (t01*(omega/6 - 2/3) + t02*(-omega/3 - 1/6) +
       t03*(omega/6 - 1/6) + t04*(1/3 - omega/3) + t13*omega/6 +
       t14*(omega^3/6 - omega^2/3) +
       t23*(omega^3/6 - omega^2/3) + t24*(omega/6 - 1)) * homega
  have h34 : t34 = t03 + t04 - t01 - t02 + t12 := by
    linear_combination
      (1/2) * e1 + (1/2) * e2 - (1/2) * e3 - (1/2) * e4 -
      (-t01/2 - t02/2 + t03/2 + t04/2) * homega
  let r0 : ℂ := (t01 + t02 - t12) / 2
  let r1 : ℂ := t01 - r0
  let r2 : ℂ := t02 - r0
  let r3 : ℂ := t03 - r0
  let r4 : ℂ := t04 - r0
  refine ⟨r0, r1, r2, r3, r4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [r0, r1, r2, r3, r4]
  · ring
  · ring
  · ring
  · ring
  · ring
  · linear_combination h13
  · linear_combination h14
  · linear_combination h23
  · linear_combination h24
  · linear_combination h34

/-! ## Passing an arbitrary full-support hafnian point to the chart -/

/-- Nonvanishing on all ten canonical edges. -/
def FullEdgeSupport (x : Fin 5 × Fin 5 → ℂ) : Prop :=
  ∀ e ∈ edgePairs, x e ≠ 0

/-- An edge array is an infinitesimal algebraic vertex scaling of `x`. -/
def IsVertexTangent (x y : Fin 5 × Fin 5 → ℂ) : Prop :=
  ∃ r : Fin 5 → ℂ, ∀ e ∈ edgePairs,
    y e = (r e.1 + r e.2) * x e

/-- Turn the ten edge-ratio identities into an intrinsic vertex tangent. -/
private theorem vertex_tangent_of_ratio_witness (x y : Fin 5 × Fin 5 → ℂ)
    (hx : FullEdgeSupport x)
    (h : ∃ r0 r1 r2 r3 r4 : ℂ,
      y (0,1) / x (0,1) = r0 + r1 ∧
      y (0,2) / x (0,2) = r0 + r2 ∧
      y (0,3) / x (0,3) = r0 + r3 ∧
      y (0,4) / x (0,4) = r0 + r4 ∧
      y (1,2) / x (1,2) = r1 + r2 ∧
      y (1,3) / x (1,3) = r1 + r3 ∧
      y (1,4) / x (1,4) = r1 + r4 ∧
      y (2,3) / x (2,3) = r2 + r3 ∧
      y (2,4) / x (2,4) = r2 + r4 ∧
      y (3,4) / x (3,4) = r3 + r4) :
    IsVertexTangent x y := by
  rcases h with ⟨r0, r1, r2, r3, r4, h01, h02, h03, h04,
    h12, h13, h14, h23, h24, h34⟩
  refine ⟨![r0, r1, r2, r3, r4], ?_⟩
  rintro ⟨i, j⟩ he
  fin_cases i <;> fin_cases j <;> simp_all [edgePairs]
  all_goals first
    | exact (div_eq_iff (hx (0,1) (by decide))).mp h01
    | exact (div_eq_iff (hx (0,2) (by decide))).mp h02
    | exact (div_eq_iff (hx (0,3) (by decide))).mp h03
    | exact (div_eq_iff (hx (0,4) (by decide))).mp h04
    | exact (div_eq_iff (hx (1,2) (by decide))).mp h12
    | exact (div_eq_iff (hx (1,3) (by decide))).mp h13
    | exact (div_eq_iff (hx (1,4) (by decide))).mp h14
    | exact (div_eq_iff (hx (2,3) (by decide))).mp h23
    | exact (div_eq_iff (hx (2,4) (by decide))).mp h24
    | exact (div_eq_iff (hx (3,4) (by decide))).mp h34

/-- Full-support solutions of the five hafnians have the normalized
`(tau, omega)` chart.  No root of unity is selected in advance. -/
theorem full_hafnian_chart (x : Fin 5 × Fin 5 → ℂ)
    (hx : FullEdgeSupport x) (hH : ∀ v, Hafnian5 x v = 0) :
    ∃ tau omega : ℂ,
      tau ≠ 0 ∧ 1 + omega + omega^2 = 0 ∧
      x (1,2) / (x (0,1) * x (0,2)) = tau ∧
      x (3,4) / (x (0,3) * x (0,4)) = tau ∧
      x (1,3) / (x (0,1) * x (0,3)) = tau * omega ∧
      x (2,4) / (x (0,2) * x (0,4)) = tau * omega ∧
      x (1,4) / (x (0,1) * x (0,4)) = tau * omega^2 ∧
      x (2,3) / (x (0,2) * x (0,3)) = tau * omega^2 := by
  have hx01 : x (0,1) ≠ 0 := hx (0,1) (by decide)
  have hx02 : x (0,2) ≠ 0 := hx (0,2) (by decide)
  have hx03 : x (0,3) ≠ 0 := hx (0,3) (by decide)
  have hx04 : x (0,4) ≠ 0 := hx (0,4) (by decide)
  let X12 := x (1,2) / (x (0,1) * x (0,2))
  let X13 := x (1,3) / (x (0,1) * x (0,3))
  let X14 := x (1,4) / (x (0,1) * x (0,4))
  let X23 := x (2,3) / (x (0,2) * x (0,3))
  let X24 := x (2,4) / (x (0,2) * x (0,4))
  let X34 := x (3,4) / (x (0,3) * x (0,4))
  have h0 := hH 0
  have h1 := hH 1
  have h2 := hH 2
  have h3 := hH 3
  have h4 := hH 4
  simp [Hafnian5] at h0 h1 h2 h3 h4
  have h123 : X12 + X13 + X23 = 0 := by
    dsimp [X12, X13, X23]
    field_simp [hx01, hx02, hx03]
    linear_combination h4
  have h124 : X12 + X14 + X24 = 0 := by
    dsimp [X12, X14, X24]
    field_simp [hx01, hx02, hx04]
    linear_combination h3
  have h134 : X13 + X14 + X34 = 0 := by
    dsimp [X13, X14, X34]
    field_simp [hx01, hx03, hx04]
    linear_combination h2
  have h234 : X23 + X24 + X34 = 0 := by
    dsimp [X23, X24, X34]
    field_simp [hx02, hx03, hx04]
    linear_combination h1
  have hzero : X12 * X34 + X13 * X24 + X14 * X23 = 0 := by
    dsimp [X12, X13, X14, X23, X24, X34]
    field_simp [hx01, hx02, hx03, hx04]
    linear_combination h0
  have hX12 : X12 ≠ 0 := by
    dsimp [X12]
    exact div_ne_zero (hx (1,2) (by decide)) (mul_ne_zero hx01 hx02)
  obtain ⟨tau, omega, htau, homega, h12, h34', h13, h24, h14, h23⟩ :=
    normalized_hafnian_form X12 X13 X14 X23 X24 X34 hX12
      h123 h124 h134 h234 hzero
  exact ⟨tau, omega, htau, homega, h12, h34', h13, h24, h14, h23⟩

/-- At every full-support point of the five-hafnian variety, every common
tangent is an infinitesimal vertex scaling. -/
theorem full_hafnian_tangent_is_vertex (x y : Fin 5 × Fin 5 → ℂ)
    (hx : FullEdgeSupport x)
    (hH : ∀ v, Hafnian5 x v = 0)
    (hT : ∀ v, PolarHafnian5 x y v = 0) :
    IsVertexTangent x y := by
  have hx01 : x (0,1) ≠ 0 := hx (0,1) (by decide)
  have hx02 : x (0,2) ≠ 0 := hx (0,2) (by decide)
  have hx03 : x (0,3) ≠ 0 := hx (0,3) (by decide)
  have hx04 : x (0,4) ≠ 0 := hx (0,4) (by decide)
  have hx12 : x (1,2) ≠ 0 := hx (1,2) (by decide)
  have hx13 : x (1,3) ≠ 0 := hx (1,3) (by decide)
  have hx14 : x (1,4) ≠ 0 := hx (1,4) (by decide)
  have hx23 : x (2,3) ≠ 0 := hx (2,3) (by decide)
  have hx24 : x (2,4) ≠ 0 := hx (2,4) (by decide)
  have hx34 : x (3,4) ≠ 0 := hx (3,4) (by decide)
  rcases full_hafnian_chart x hx hH with
    ⟨tau, omega, htau, homega, h12, h34, h13, h24, h14, h23⟩
  have homega0 : omega ≠ 0 := by
    intro hz
    rw [hz] at homega
    norm_num at homega
  have xx12 : x (1,2) = tau * (x (0,1) * x (0,2)) :=
    (div_eq_iff (mul_ne_zero hx01 hx02)).mp h12
  have xx13 : x (1,3) = (tau * omega) * (x (0,1) * x (0,3)) :=
    (div_eq_iff (mul_ne_zero hx01 hx03)).mp h13
  have xx14 : x (1,4) = (tau * omega^2) * (x (0,1) * x (0,4)) :=
    (div_eq_iff (mul_ne_zero hx01 hx04)).mp h14
  have xx23 : x (2,3) = (tau * omega^2) * (x (0,2) * x (0,3)) :=
    (div_eq_iff (mul_ne_zero hx02 hx03)).mp h23
  have xx24 : x (2,4) = (tau * omega) * (x (0,2) * x (0,4)) :=
    (div_eq_iff (mul_ne_zero hx02 hx04)).mp h24
  have xx34 : x (3,4) = tau * (x (0,3) * x (0,4)) :=
    (div_eq_iff (mul_ne_zero hx03 hx04)).mp h34
  let t01 := y (0,1) / x (0,1)
  let t02 := y (0,2) / x (0,2)
  let t03 := y (0,3) / x (0,3)
  let t04 := y (0,4) / x (0,4)
  let t12 := y (1,2) / x (1,2)
  let t13 := y (1,3) / x (1,3)
  let t14 := y (1,4) / x (1,4)
  let t23 := y (2,3) / x (2,3)
  let t24 := y (2,4) / x (2,4)
  let t34 := y (3,4) / x (3,4)
  have yy01 : y (0,1) = t01 * x (0,1) := by
    dsimp [t01]
    field_simp [hx01]
  have yy02 : y (0,2) = t02 * x (0,2) := by
    dsimp [t02]
    field_simp [hx02]
  have yy03 : y (0,3) = t03 * x (0,3) := by
    dsimp [t03]
    field_simp [hx03]
  have yy04 : y (0,4) = t04 * x (0,4) := by
    dsimp [t04]
    field_simp [hx04]
  have yy12 : y (1,2) = t12 * x (1,2) := by
    dsimp [t12]
    field_simp [hx12]
  have yy13 : y (1,3) = t13 * x (1,3) := by
    dsimp [t13]
    field_simp [hx13]
  have yy14 : y (1,4) = t14 * x (1,4) := by
    dsimp [t14]
    field_simp [hx14]
  have yy23 : y (2,3) = t23 * x (2,3) := by
    dsimp [t23]
    field_simp [hx23]
  have yy24 : y (2,4) = t24 * x (2,4) := by
    dsimp [t24]
    field_simp [hx24]
  have yy34 : y (3,4) = t34 * x (3,4) := by
    dsimp [t34]
    field_simp [hx34]
  have T0 := hT 0
  have T1 := hT 1
  have T2 := hT 2
  have T3 := hT 3
  have T4 := hT 4
  simp [PolarHafnian5] at T0 T1 T2 T3 T4
  simp only [yy01, yy02, yy03, yy04, yy12, yy13, yy14, yy23, yy24, yy34,
    xx12, xx13, xx14, xx23, xx24, xx34] at T0 T1 T2 T3 T4
  have e0 : (t12 + t34) + omega^2 * (t13 + t24) +
      omega^4 * (t14 + t23) = 0 := by
    have hfac : tau^2 * x (0,1) * x (0,2) * x (0,3) * x (0,4) ≠ 0 := by
      have htau2 : tau^2 ≠ 0 := pow_ne_zero 2 htau
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero htau2 hx01) hx02) hx03) hx04
    have hprod :
        (tau^2 * x (0,1) * x (0,2) * x (0,3) * x (0,4)) *
          ((t12 + t34) + omega^2 * (t13 + t24) + omega^4 * (t14 + t23)) = 0 := by
      linear_combination T0
    exact (mul_eq_zero.mp hprod).resolve_left hfac
  have e1 : (t02 + t34) + omega * (t03 + t24) +
      omega^2 * (t04 + t23) = 0 := by
    have hfac : tau * x (0,2) * x (0,3) * x (0,4) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero htau hx02) hx03) hx04
    have hprod : (tau * x (0,2) * x (0,3) * x (0,4)) *
        ((t02 + t34) + omega * (t03 + t24) + omega^2 * (t04 + t23)) = 0 := by
      linear_combination T1
    exact (mul_eq_zero.mp hprod).resolve_left hfac
  have e2 : (t01 + t34) + omega^2 * (t03 + t14) +
      omega * (t04 + t13) = 0 := by
    have hfac : tau * x (0,1) * x (0,3) * x (0,4) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero htau hx01) hx03) hx04
    have hprod : (tau * x (0,1) * x (0,3) * x (0,4)) *
        ((t01 + t34) + omega^2 * (t03 + t14) + omega * (t04 + t13)) = 0 := by
      linear_combination T2
    exact (mul_eq_zero.mp hprod).resolve_left hfac
  have e3 : omega * (t01 + t24) + omega^2 * (t02 + t14) +
      (t04 + t12) = 0 := by
    have hfac : tau * x (0,1) * x (0,2) * x (0,4) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero htau hx01) hx02) hx04
    have hprod : (tau * x (0,1) * x (0,2) * x (0,4)) *
        (omega * (t01 + t24) + omega^2 * (t02 + t14) + (t04 + t12)) = 0 := by
      linear_combination T3
    exact (mul_eq_zero.mp hprod).resolve_left hfac
  have e4 : omega^2 * (t01 + t23) + omega * (t02 + t13) +
      (t03 + t12) = 0 := by
    have hfac : tau * x (0,1) * x (0,2) * x (0,3) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero htau hx01) hx02) hx03
    have hprod : (tau * x (0,1) * x (0,2) * x (0,3)) *
        (omega^2 * (t01 + t23) + omega * (t02 + t13) + (t03 + t12)) = 0 := by
      linear_combination T4
    exact (mul_eq_zero.mp hprod).resolve_left hfac
  exact vertex_tangent_of_ratio_witness x y hx
    (ratio_tangent_vertex omega
      t01 t02 t03 t04 t12 t13 t14 t23 t24 t34
      homega e0 e1 e2 e3 e4)

end

end SixQubit.Orbit7Universal
