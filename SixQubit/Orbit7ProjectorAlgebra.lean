import Mathlib

/-!
# Orbit 7: polynomial projector-entry certificates

This file contains the division-free algebra behind the full-support
projector comparison.  The variables `c,d` are written in `ℂ`; the caller
establishes the displayed cleared entry equations from its real gauge.
-/

namespace SixQubit.Orbit7ProjectorAlgebra

open scoped ComplexConjugate

noncomputable section

/-- Comparing the `(0,0)` and `(0,1)` entries of
`P_a(t)+P_b(p)=P_u+P_v`, after clearing the common positive denominator,
forces the circle equation and `p = star t`.  This is the exact polynomial
certificate; no square root, phase choice, or division is used. -/
theorem projector_entries_force_conj
    (c d t p : ℂ)
    (hunit : c * c + d * d = 1) (hc : c ≠ 0)
    (h00 : (c - d * t) * (c - d * star t) + 1 =
      (1 + t * star t) * (1 + c * c))
    (h01 : (c - d * t) * (d + c * star t) - p =
      (1 + t * star t) * (c * d)) :
    2 * c * (t * star t) + d * (t + star t) = 0 ∧ p = star t := by
  have hcircleMul :
      c * (2 * c * (t * star t) + d * (t + star t)) = 0 := by
    linear_combination -h00 + (t * star t) * hunit
  have hcircle : 2 * c * (t * star t) + d * (t + star t) = 0 :=
    (mul_eq_zero.mp hcircleMul).resolve_left hc
  have hp : p = star t := by
    linear_combination -h01 - d * hcircle + star t * hunit
  exact ⟨hcircle, hp⟩

/-- Two circle equations and the disjoint-edge relation have exactly the
three factors used in the manuscript: equal parameters, or one of the two
endpoint values.  The statement keeps the endpoint equations in
division-free form `c*T+d=0`. -/
theorem disjoint_circle_three_cases
    (c d T N Ts Ns : ℂ) (hd : d ≠ 0)
    (hT : 2 * c * (T * Ts) + d * (T + Ts) = 0)
    (hN : 2 * c * (N * Ns) + d * (N + Ns) = 0)
    (hdis : d * (T - N + Ns - Ts) + c * (T * Ns - N * Ts) = 0) :
    T = N ∨ c * T + d = 0 ∨ c * N + d = 0 := by
  have hfactor :
      (2 * d) * ((T - N) * (c * T + d) * (c * N + d)) = 0 := by
    linear_combination
      ((2 * c * T + d) * (2 * c * N + d)) * hdis
      - ((c * T + d) * (2 * c * T + d)) * hN
      + ((c * N + d) * (2 * c * N + d)) * hT
  have h2d : (2 * d : ℂ) ≠ 0 := mul_ne_zero (by norm_num) hd
  have hprod : (T - N) * (c * T + d) * (c * N + d) = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left h2d
  rcases mul_eq_zero.mp hprod with hleft | hNend
  · rcases mul_eq_zero.mp hleft with hTN | hTend
    · exact Or.inl (sub_eq_zero.mp hTN)
    · exact Or.inr (Or.inl hTend)
  · exact Or.inr (Or.inr hNend)

/-! ## Gauge-covariant projector algebra -/

/-- The same projector-entry calculation without choosing phases that make
the two anchor coordinates real.  Here `C,D,ts,ps` are intended to be the
complex conjugates of `c,d,t,p`, but the certificate itself only needs the
displayed polynomial equations. -/
theorem covariant_projector_entries
    (c C d D t ts ps : ℂ)
    (hunit : c * C + d * D = 1)
    (h00 : (c - t * D) * (C - ts * d) + 1 =
      (1 + t * ts) * (1 + c * C))
    (h10 : (d + t * C) * (C - ts * d) - ps =
      (1 + t * ts) * (d * C)) :
    C * D * t + c * d * ts + 2 * c * C * t * ts = 0 ∧
      c * ps = C * t := by
  have hcircle : C * D * t + c * d * ts + 2 * c * C * t * ts = 0 := by
    linear_combination -h00 + (t * ts) * hunit
  have hphase : c * ps = C * t := by
    linear_combination -c * h10 - d * hcircle + (C * t) * hunit
  exact ⟨hcircle, hphase⟩

/-- Covariant version of the manuscript's three-factor calculation.  It
uses the circle equations at two edge types and the actual disjoint-edge
equation; no division or phase normalization occurs. -/
theorem covariant_disjoint_circle_three_cases
    (c C d D T Ts N Ns : ℂ)
    (hc : c ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (hT : C * D * T + c * d * Ts + 2 * c * C * T * Ts = 0)
    (hN : C * D * N + c * d * Ns + 2 * c * C * N * Ns = 0)
    (hdis : c * d * (Ts - Ns) + C * D * (N - T) +
      c * C * (Ts * N - Ns * T) = 0) :
    T = N ∨ C * T + d = 0 ∨ C * N + d = 0 := by
  have hfactor :
      (2 * c^2 * C * D) *
        ((T - N) * (C * T + d) * (C * N + d)) = 0 := by
    linear_combination
      c^2 * (C * N + d) * (2 * C * N + d) * hT
      - c^2 * (C * T + d) * (2 * C * T + d) * hN
      - (c * (d + 2 * C * T)) * (c * (d + 2 * C * N)) * hdis
  have hpref : (2 * c^2 * C * D : ℂ) ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hc)) hC) hD
  have hprod : (T - N) * (C * T + d) * (C * N + d) = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left hpref
  rcases mul_eq_zero.mp hprod with hleft | hNend
  · rcases mul_eq_zero.mp hleft with hTN | hTend
    · exact Or.inl (sub_eq_zero.mp hTN)
    · exact Or.inr (Or.inl hTend)
  · exact Or.inr (Or.inr hNend)

end

end SixQubit.Orbit7ProjectorAlgebra
