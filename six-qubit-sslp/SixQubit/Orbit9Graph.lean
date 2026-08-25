import Mathlib
import SixQubit.K5

/-!
# Orbit 9: division-free support-graph algebra

This module isolates the algebra used by the orbit-9 active-support reduction.
The fifteen edge variables form a symmetric zero-diagonal six-by-six matrix.
Every row sums to zero and every four-set has vanishing hafnian.  We record
three exact consequences: triangles close, a five-vertex connected component
is impossible, and a six-vertex component is impossible.  No amplitude,
bit-string, or numerical solver occurs in this layer.
-/

namespace SixQubit.Orbit9Graph

noncomputable section

/-- Row-kernel and four-set hafnian equations for a symmetric graph on six
labelled vertices. -/
structure Sys
    (c01 c02 c03 c04 c05 c12 c13 c14 c15 c23 c24 c25 c34 c35 c45 : ℂ) : Prop where
  r0 : c01 + c02 + c03 + c04 + c05 = 0
  r1 : c01 + c12 + c13 + c14 + c15 = 0
  r2 : c02 + c12 + c23 + c24 + c25 = 0
  r3 : c03 + c13 + c23 + c34 + c35 = 0
  r4 : c04 + c14 + c24 + c34 + c45 = 0
  r5 : c05 + c15 + c25 + c35 + c45 = 0
  h0123 : c01 * c23 + c02 * c13 + c03 * c12 = 0
  h0124 : c01 * c24 + c02 * c14 + c04 * c12 = 0
  h0125 : c01 * c25 + c02 * c15 + c05 * c12 = 0
  h0134 : c01 * c34 + c03 * c14 + c04 * c13 = 0
  h0135 : c01 * c35 + c03 * c15 + c05 * c13 = 0
  h0145 : c01 * c45 + c04 * c15 + c05 * c14 = 0
  h0234 : c02 * c34 + c03 * c24 + c04 * c23 = 0
  h0235 : c02 * c35 + c03 * c25 + c05 * c23 = 0
  h0245 : c02 * c45 + c04 * c25 + c05 * c24 = 0
  h0345 : c03 * c45 + c04 * c35 + c05 * c34 = 0
  h1234 : c12 * c34 + c13 * c24 + c14 * c23 = 0
  h1235 : c12 * c35 + c13 * c25 + c15 * c23 = 0
  h1245 : c12 * c45 + c14 * c25 + c15 * c24 = 0
  h1345 : c13 * c45 + c14 * c35 + c15 * c34 = 0
  h2345 : c23 * c45 + c24 * c35 + c25 * c34 = 0

variable {c01 c02 c03 c04 c05 c12 c13 c14 c15 c23 c24 c25 c34 c35 c45 : ℂ}

/-- Summing the three hafnians through a triangle and using the row kernel
gives the triangle relation. -/
theorem triangle012
    (h : Sys c01 c02 c03 c04 c05 c12 c13 c14 c15 c23 c24 c25 c34 c35 c45) :
    c01 * c02 + c01 * c12 + c02 * c12 = 0 := by
  linear_combination (1 / 2 : ℂ) *
      (c01 * h.r2 + c02 * h.r1 + c12 * h.r0
        - h.h0123 - h.h0124 - h.h0125)

/-- Two adjacent active edges force the third edge of their triangle to be
active.  This is the division-free clique-closing step. -/
theorem triangle_closes
    (h : Sys c01 c02 c03 c04 c05 c12 c13 c14 c15 c23 c24 c25 c34 c35 c45)
    (h01 : c01 ≠ 0) (h02 : c02 ≠ 0) : c12 ≠ 0 := by
  intro h12
  have ht := triangle012 h
  rw [h12] at ht
  simp only [mul_zero, add_zero] at ht
  exact (mul_ne_zero h01 h02) ht

/-- A clique on vertices `0,1,2,3,4` cannot be a connected component.  The
five zero crossing edges turn the six row equations into the five kernel rows
of `SixQubit.K5.dets0`; its exact determinant certificate kills a product of
five nonzero edges. -/
theorem no_K5_component
    (h : Sys c01 c02 c03 c04 c05 c12 c13 c14 c15 c23 c24 c25 c34 c35 c45)
    (z05 : c05 = 0) (z15 : c15 = 0) (z25 : c25 = 0)
    (z35 : c35 = 0) (z45 : c45 = 0)
    (n01 : c01 ≠ 0) (n23 : c23 ≠ 0)
    (n24 : c24 ≠ 0) (n34 : c34 ≠ 0) : False := by
  have s0 : (1 : ℂ) * c01 + 1 * c02 + 1 * c03 + 1 * c04 = 0 := by
    linear_combination h.r0 - z05
  have s1 : (1 : ℂ) * c01 + 1 * c12 + 1 * c13 + 1 * c14 = 0 := by
    linear_combination h.r1 - z15
  have s2 : (1 : ℂ) * c02 + 1 * c12 + 1 * c23 + 1 * c24 = 0 := by
    linear_combination h.r2 - z25
  have s3 : (1 : ℂ) * c03 + 1 * c13 + 1 * c23 + 1 * c34 = 0 := by
    linear_combination h.r3 - z35
  have s4 : (1 : ℂ) * c04 + 1 * c14 + 1 * c24 + 1 * c34 = 0 := by
    linear_combination h.r4 - z45
  have hd := SixQubit.K5.dets0 s0 s1 s2 s3 s4
    h.h1234 h.h0234 h.h0134 h.h0124 h.h0123 (by norm_num : (1 : ℂ) ≠ 0)
  have hp : c23 * c24 * c34 * c01 * c01 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero n23 n24) n34) n01) n01
  exact hp hd.1

/-- The ten four-set equations through vertex zero are the triangle-versus-edge
incidence system of `K_5`.  The first row of its exact inverse shows
`c12*c03*c04*c05 = 0`; hence a six-vertex clique is impossible. -/
theorem no_K6
    (h : Sys c01 c02 c03 c04 c05 c12 c13 c14 c15 c23 c24 c25 c34 c35 c45)
    (n03 : c03 ≠ 0) (n04 : c04 ≠ 0) (n05 : c05 ≠ 0) (n12 : c12 ≠ 0) : False := by
  have hz : c12 * c03 * c04 * c05 = 0 := by
    linear_combination
      (c04 * c05 / 3 : ℂ) * h.h0123
      + (c03 * c05 / 3 : ℂ) * h.h0124
      + (c03 * c04 / 3 : ℂ) * h.h0125
      - (c02 * c05 / 6 : ℂ) * h.h0134
      - (c02 * c04 / 6 : ℂ) * h.h0135
      - (c02 * c03 / 6 : ℂ) * h.h0145
      - (c01 * c05 / 6 : ℂ) * h.h0234
      - (c01 * c04 / 6 : ℂ) * h.h0235
      - (c01 * c03 / 6 : ℂ) * h.h0245
      + (c01 * c02 / 3 : ℂ) * h.h0345
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero n12 n03) n04) n05) hz

end

end SixQubit.Orbit9Graph
