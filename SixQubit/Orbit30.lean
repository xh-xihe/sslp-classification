import Mathlib

import SS.FullKL
import SixQubit.Common
import SixQubit.K5

/-!
# Six-qubit no-go for moment orbit 30

Orbit 30 of `six_qubit_sslp.tex`: q = 4, angle vector
a = (1, 1, 1, 1, 2, 3).  The projective order is m = 4, so the residue that has to
be excluded is delta = q/m = 1: `S0` is the residue-0 fiber, `S1` the
residue-1 fiber, and the two are complementary.


The residue-0 fiber has sixteen strings and is parametrised by
`x(u) = (u, t(wt u))` for `u` in `F_2^4`, with `t(0) = t(4) = 00`,
`t(1) = 01`, `t(2) = 10`, `t(3) = 11`.  One string is the distinguished
`star = x(1111)`, five are the *points* `v_i`, and ten are the *edges*
`e_ij` of `K_5`; the residue-1 fiber is the complementary set.

Writing `u p = star (c y_p)`, `v q = d z_(top q)`, `a = u star`,
`s = v star`, the ten admissible flip masks reduce, by exact Walsh row
reduction, to

  * `R_i`   :  a * v(v_i) + u(v_i) * s = 0                     (weight two),
  * `D_ij`  :  u(v_j) * v(e_ij) = u(e_ij) * v(v_j)             (weight one),
  * `T_i`   :  sum_{j != i} u(v_j) * v(e_ij) = 0               (weight one),
  * `M_i`   :  the all-plus sum over the three perfect matchings of
               `V \ {i}` of the two edge-edge monomials         (weight two).

Setting `k_ij = a * v(e_ij) + u(e_ij) * s`, these give `b_p * k_ij = 0` for
both endpoints of every edge, `s * (C b)_i = 0` hence `C b = 0`, and an
identity whose right-hand side is `2 s H_i`.  Together with the exact moment
data (`p_star = 1/8`, `deg_i = |b_i|^2 + 1/8`, total point mass `3/8`, total
edge mass `1/2`) that is exactly `SixQubit.K5.Sys`, which is contradictory.

Everything computational is decided by the Lean kernel; `native_decide`
is not used.
-/

namespace SixQubit.Orbit30

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

/-! ## The two fibers -/

def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]

def y0 : SS.BitString 6 := bs false false false false false false  -- 000000
def y1 : SS.BitString 6 := bs false false false true  false true   -- 000101
def y2 : SS.BitString 6 := bs false false true  false false true   -- 001001
def y3 : SS.BitString 6 := bs false false true  true  true  false  -- 001110
def y4 : SS.BitString 6 := bs false true  false false false true   -- 010001
def y5 : SS.BitString 6 := bs false true  false true  true  false  -- 010110
def y6 : SS.BitString 6 := bs false true  true  false true  false  -- 011010
def y7 : SS.BitString 6 := bs false true  true  true  true  true   -- 011111
def y8 : SS.BitString 6 := bs true  false false false false true   -- 100001
def y9 : SS.BitString 6 := bs true  false false true  true  false  -- 100110
def y10 : SS.BitString 6 := bs true  false true  false true  false  -- 101010
def y11 : SS.BitString 6 := bs true  false true  true  true  true   -- 101111
def y12 : SS.BitString 6 := bs true  true  false false true  false  -- 110010
def y13 : SS.BitString 6 := bs true  true  false true  true  true   -- 110111
def y14 : SS.BitString 6 := bs true  true  true  false true  true   -- 111011
def y15 : SS.BitString 6 := bs true  true  true  true  false false  -- 111100

def z0 : SS.BitString 6 := bs false false false false true  true   -- 000011
def z1 : SS.BitString 6 := bs false false false true  false false  -- 000100
def z2 : SS.BitString 6 := bs false false true  false false false  -- 001000
def z3 : SS.BitString 6 := bs false false true  true  false true   -- 001101
def z4 : SS.BitString 6 := bs false true  false false false false  -- 010000
def z5 : SS.BitString 6 := bs false true  false true  false true   -- 010101
def z6 : SS.BitString 6 := bs false true  true  false false true   -- 011001
def z7 : SS.BitString 6 := bs false true  true  true  true  false  -- 011110
def z8 : SS.BitString 6 := bs true  false false false false false  -- 100000
def z9 : SS.BitString 6 := bs true  false false true  false true   -- 100101
def z10 : SS.BitString 6 := bs true  false true  false false true   -- 101001
def z11 : SS.BitString 6 := bs true  false true  true  true  false  -- 101110
def z12 : SS.BitString 6 := bs true  true  false false false true   -- 110001
def z13 : SS.BitString 6 := bs true  true  false true  true  false  -- 110110
def z14 : SS.BitString 6 := bs true  true  true  false true  false  -- 111010
def z15 : SS.BitString 6 := bs true  true  true  true  true  true   -- 111111

def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15}
def S1 : Finset (SS.BitString 6) := {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15}

def av : Fin 6 -> ZMod 4 := ![1, 1, 1, 1, 2, 3]

theorem S0_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 0) = S0 := by
  decide

theorem S1_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 1) = S1 := by
  decide

/-! ## Flip masks, incidences and signs -/

def ef0 : SS.BitString 6 := bs false false false false false true   -- 000001
def ef1 : SS.BitString 6 := bs false false false false true  true   -- 000011
def ef2 : SS.BitString 6 := bs false false false true  false false  -- 000100
def ef3 : SS.BitString 6 := bs false false false true  true  false  -- 000110
def ef4 : SS.BitString 6 := bs false false true  false false false  -- 001000
def ef5 : SS.BitString 6 := bs false false true  false true  false  -- 001010
def ef6 : SS.BitString 6 := bs false true  false false false false  -- 010000
def ef7 : SS.BitString 6 := bs false true  false false true  false  -- 010010
def ef8 : SS.BitString 6 := bs true  false false false false false  -- 100000
def ef9 : SS.BitString 6 := bs true  false false false true  false  -- 100010
def w0 : SS.BitString 6 := bs false false false false false false  -- 000000
def w1 : SS.BitString 6 := bs false false false false false true   -- 000001
def w2 : SS.BitString 6 := bs false false false false true  false  -- 000010
def w3 : SS.BitString 6 := bs false false false true  false false  -- 000100
def w4 : SS.BitString 6 := bs false false true  false false false  -- 001000
def w5 : SS.BitString 6 := bs false true  false false false false  -- 010000

theorem incidence_ef0 :
    S1.filter (fun y => SS.bxor y ef0 ∈ S0) = {z1, z2, z4, z7, z8, z11, z13, z14} := by decide
theorem flip_ef0_1 : SS.bxor z1 ef0 = y1 := by decide
theorem flip_ef0_2 : SS.bxor z2 ef0 = y2 := by decide
theorem flip_ef0_4 : SS.bxor z4 ef0 = y4 := by decide
theorem flip_ef0_7 : SS.bxor z7 ef0 = y7 := by decide
theorem flip_ef0_8 : SS.bxor z8 ef0 = y8 := by decide
theorem flip_ef0_11 : SS.bxor z11 ef0 = y11 := by decide
theorem flip_ef0_13 : SS.bxor z13 ef0 = y13 := by decide
theorem flip_ef0_14 : SS.bxor z14 ef0 = y14 := by decide
theorem sg_ef0_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg_ef0_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg_ef0_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg_ef0_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg_ef0_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_ef0_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg_ef0_w0_13 : SS.bdot w0 z13 = false := by decide
theorem sg_ef0_w0_14 : SS.bdot w0 z14 = false := by decide
theorem sg_ef0_w2_1 : SS.bdot w2 z1 = false := by decide
theorem sg_ef0_w2_2 : SS.bdot w2 z2 = false := by decide
theorem sg_ef0_w2_4 : SS.bdot w2 z4 = false := by decide
theorem sg_ef0_w2_7 : SS.bdot w2 z7 = true := by decide
theorem sg_ef0_w2_8 : SS.bdot w2 z8 = false := by decide
theorem sg_ef0_w2_11 : SS.bdot w2 z11 = true := by decide
theorem sg_ef0_w2_13 : SS.bdot w2 z13 = true := by decide
theorem sg_ef0_w2_14 : SS.bdot w2 z14 = true := by decide
theorem sg_ef0_w3_1 : SS.bdot w3 z1 = true := by decide
theorem sg_ef0_w3_2 : SS.bdot w3 z2 = false := by decide
theorem sg_ef0_w3_4 : SS.bdot w3 z4 = false := by decide
theorem sg_ef0_w3_7 : SS.bdot w3 z7 = true := by decide
theorem sg_ef0_w3_8 : SS.bdot w3 z8 = false := by decide
theorem sg_ef0_w3_11 : SS.bdot w3 z11 = true := by decide
theorem sg_ef0_w3_13 : SS.bdot w3 z13 = true := by decide
theorem sg_ef0_w3_14 : SS.bdot w3 z14 = false := by decide
theorem sg_ef0_w4_1 : SS.bdot w4 z1 = false := by decide
theorem sg_ef0_w4_2 : SS.bdot w4 z2 = true := by decide
theorem sg_ef0_w4_4 : SS.bdot w4 z4 = false := by decide
theorem sg_ef0_w4_7 : SS.bdot w4 z7 = true := by decide
theorem sg_ef0_w4_8 : SS.bdot w4 z8 = false := by decide
theorem sg_ef0_w4_11 : SS.bdot w4 z11 = true := by decide
theorem sg_ef0_w4_13 : SS.bdot w4 z13 = false := by decide
theorem sg_ef0_w4_14 : SS.bdot w4 z14 = true := by decide
theorem sg_ef0_w5_1 : SS.bdot w5 z1 = false := by decide
theorem sg_ef0_w5_2 : SS.bdot w5 z2 = false := by decide
theorem sg_ef0_w5_4 : SS.bdot w5 z4 = true := by decide
theorem sg_ef0_w5_7 : SS.bdot w5 z7 = true := by decide
theorem sg_ef0_w5_8 : SS.bdot w5 z8 = false := by decide
theorem sg_ef0_w5_11 : SS.bdot w5 z11 = false := by decide
theorem sg_ef0_w5_13 : SS.bdot w5 z13 = true := by decide
theorem sg_ef0_w5_14 : SS.bdot w5 z14 = true := by decide

theorem incidence_ef1 :
    S1.filter (fun y => SS.bxor y ef1 ∈ S0) = {z0, z3, z5, z6, z9, z10, z12, z15} := by decide
theorem flip_ef1_0 : SS.bxor z0 ef1 = y0 := by decide
theorem flip_ef1_3 : SS.bxor z3 ef1 = y3 := by decide
theorem flip_ef1_5 : SS.bxor z5 ef1 = y5 := by decide
theorem flip_ef1_6 : SS.bxor z6 ef1 = y6 := by decide
theorem flip_ef1_9 : SS.bxor z9 ef1 = y9 := by decide
theorem flip_ef1_10 : SS.bxor z10 ef1 = y10 := by decide
theorem flip_ef1_12 : SS.bxor z12 ef1 = y12 := by decide
theorem flip_ef1_15 : SS.bxor z15 ef1 = y15 := by decide
theorem sg_ef1_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg_ef1_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg_ef1_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg_ef1_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg_ef1_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg_ef1_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg_ef1_w0_12 : SS.bdot w0 z12 = false := by decide
theorem sg_ef1_w0_15 : SS.bdot w0 z15 = false := by decide
theorem sg_ef1_w2_0 : SS.bdot w2 z0 = true := by decide
theorem sg_ef1_w2_3 : SS.bdot w2 z3 = false := by decide
theorem sg_ef1_w2_5 : SS.bdot w2 z5 = false := by decide
theorem sg_ef1_w2_6 : SS.bdot w2 z6 = false := by decide
theorem sg_ef1_w2_9 : SS.bdot w2 z9 = false := by decide
theorem sg_ef1_w2_10 : SS.bdot w2 z10 = false := by decide
theorem sg_ef1_w2_12 : SS.bdot w2 z12 = false := by decide
theorem sg_ef1_w2_15 : SS.bdot w2 z15 = true := by decide

theorem incidence_ef2 :
    S1.filter (fun y => SS.bxor y ef2 ∈ S0) = {z1, z3, z5, z7, z9, z11, z13, z15} := by decide
theorem flip_ef2_1 : SS.bxor z1 ef2 = y0 := by decide
theorem flip_ef2_3 : SS.bxor z3 ef2 = y2 := by decide
theorem flip_ef2_5 : SS.bxor z5 ef2 = y4 := by decide
theorem flip_ef2_7 : SS.bxor z7 ef2 = y6 := by decide
theorem flip_ef2_9 : SS.bxor z9 ef2 = y8 := by decide
theorem flip_ef2_11 : SS.bxor z11 ef2 = y10 := by decide
theorem flip_ef2_13 : SS.bxor z13 ef2 = y12 := by decide
theorem flip_ef2_15 : SS.bxor z15 ef2 = y14 := by decide
theorem sg_ef2_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg_ef2_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg_ef2_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg_ef2_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg_ef2_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg_ef2_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg_ef2_w0_13 : SS.bdot w0 z13 = false := by decide
theorem sg_ef2_w0_15 : SS.bdot w0 z15 = false := by decide
theorem sg_ef2_w1_1 : SS.bdot w1 z1 = false := by decide
theorem sg_ef2_w1_3 : SS.bdot w1 z3 = true := by decide
theorem sg_ef2_w1_5 : SS.bdot w1 z5 = true := by decide
theorem sg_ef2_w1_7 : SS.bdot w1 z7 = false := by decide
theorem sg_ef2_w1_9 : SS.bdot w1 z9 = true := by decide
theorem sg_ef2_w1_11 : SS.bdot w1 z11 = false := by decide
theorem sg_ef2_w1_13 : SS.bdot w1 z13 = false := by decide
theorem sg_ef2_w1_15 : SS.bdot w1 z15 = true := by decide
theorem sg_ef2_w2_1 : SS.bdot w2 z1 = false := by decide
theorem sg_ef2_w2_3 : SS.bdot w2 z3 = false := by decide
theorem sg_ef2_w2_5 : SS.bdot w2 z5 = false := by decide
theorem sg_ef2_w2_7 : SS.bdot w2 z7 = true := by decide
theorem sg_ef2_w2_9 : SS.bdot w2 z9 = false := by decide
theorem sg_ef2_w2_11 : SS.bdot w2 z11 = true := by decide
theorem sg_ef2_w2_13 : SS.bdot w2 z13 = true := by decide
theorem sg_ef2_w2_15 : SS.bdot w2 z15 = true := by decide
theorem sg_ef2_w4_1 : SS.bdot w4 z1 = false := by decide
theorem sg_ef2_w4_3 : SS.bdot w4 z3 = true := by decide
theorem sg_ef2_w4_5 : SS.bdot w4 z5 = false := by decide
theorem sg_ef2_w4_7 : SS.bdot w4 z7 = true := by decide
theorem sg_ef2_w4_9 : SS.bdot w4 z9 = false := by decide
theorem sg_ef2_w4_11 : SS.bdot w4 z11 = true := by decide
theorem sg_ef2_w4_13 : SS.bdot w4 z13 = false := by decide
theorem sg_ef2_w4_15 : SS.bdot w4 z15 = true := by decide
theorem sg_ef2_w5_1 : SS.bdot w5 z1 = false := by decide
theorem sg_ef2_w5_3 : SS.bdot w5 z3 = false := by decide
theorem sg_ef2_w5_5 : SS.bdot w5 z5 = true := by decide
theorem sg_ef2_w5_7 : SS.bdot w5 z7 = true := by decide
theorem sg_ef2_w5_9 : SS.bdot w5 z9 = false := by decide
theorem sg_ef2_w5_11 : SS.bdot w5 z11 = false := by decide
theorem sg_ef2_w5_13 : SS.bdot w5 z13 = true := by decide
theorem sg_ef2_w5_15 : SS.bdot w5 z15 = true := by decide

theorem incidence_ef3 :
    S1.filter (fun y => SS.bxor y ef3 ∈ S0) = {z0, z2, z4, z6, z8, z10, z12, z14} := by decide
theorem flip_ef3_0 : SS.bxor z0 ef3 = y1 := by decide
theorem flip_ef3_2 : SS.bxor z2 ef3 = y3 := by decide
theorem flip_ef3_4 : SS.bxor z4 ef3 = y5 := by decide
theorem flip_ef3_6 : SS.bxor z6 ef3 = y7 := by decide
theorem flip_ef3_8 : SS.bxor z8 ef3 = y9 := by decide
theorem flip_ef3_10 : SS.bxor z10 ef3 = y11 := by decide
theorem flip_ef3_12 : SS.bxor z12 ef3 = y13 := by decide
theorem flip_ef3_14 : SS.bxor z14 ef3 = y15 := by decide
theorem sg_ef3_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg_ef3_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg_ef3_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg_ef3_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg_ef3_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_ef3_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg_ef3_w0_12 : SS.bdot w0 z12 = false := by decide
theorem sg_ef3_w0_14 : SS.bdot w0 z14 = false := by decide
theorem sg_ef3_w2_0 : SS.bdot w2 z0 = true := by decide
theorem sg_ef3_w2_2 : SS.bdot w2 z2 = false := by decide
theorem sg_ef3_w2_4 : SS.bdot w2 z4 = false := by decide
theorem sg_ef3_w2_6 : SS.bdot w2 z6 = false := by decide
theorem sg_ef3_w2_8 : SS.bdot w2 z8 = false := by decide
theorem sg_ef3_w2_10 : SS.bdot w2 z10 = false := by decide
theorem sg_ef3_w2_12 : SS.bdot w2 z12 = false := by decide
theorem sg_ef3_w2_14 : SS.bdot w2 z14 = true := by decide

theorem incidence_ef4 :
    S1.filter (fun y => SS.bxor y ef4 ∈ S0) = {z2, z3, z6, z7, z10, z11, z14, z15} := by decide
theorem flip_ef4_2 : SS.bxor z2 ef4 = y0 := by decide
theorem flip_ef4_3 : SS.bxor z3 ef4 = y1 := by decide
theorem flip_ef4_6 : SS.bxor z6 ef4 = y4 := by decide
theorem flip_ef4_7 : SS.bxor z7 ef4 = y5 := by decide
theorem flip_ef4_10 : SS.bxor z10 ef4 = y8 := by decide
theorem flip_ef4_11 : SS.bxor z11 ef4 = y9 := by decide
theorem flip_ef4_14 : SS.bxor z14 ef4 = y12 := by decide
theorem flip_ef4_15 : SS.bxor z15 ef4 = y13 := by decide
theorem sg_ef4_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg_ef4_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg_ef4_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg_ef4_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg_ef4_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg_ef4_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg_ef4_w0_14 : SS.bdot w0 z14 = false := by decide
theorem sg_ef4_w0_15 : SS.bdot w0 z15 = false := by decide
theorem sg_ef4_w1_2 : SS.bdot w1 z2 = false := by decide
theorem sg_ef4_w1_3 : SS.bdot w1 z3 = true := by decide
theorem sg_ef4_w1_6 : SS.bdot w1 z6 = true := by decide
theorem sg_ef4_w1_7 : SS.bdot w1 z7 = false := by decide
theorem sg_ef4_w1_10 : SS.bdot w1 z10 = true := by decide
theorem sg_ef4_w1_11 : SS.bdot w1 z11 = false := by decide
theorem sg_ef4_w1_14 : SS.bdot w1 z14 = false := by decide
theorem sg_ef4_w1_15 : SS.bdot w1 z15 = true := by decide
theorem sg_ef4_w2_2 : SS.bdot w2 z2 = false := by decide
theorem sg_ef4_w2_3 : SS.bdot w2 z3 = false := by decide
theorem sg_ef4_w2_6 : SS.bdot w2 z6 = false := by decide
theorem sg_ef4_w2_7 : SS.bdot w2 z7 = true := by decide
theorem sg_ef4_w2_10 : SS.bdot w2 z10 = false := by decide
theorem sg_ef4_w2_11 : SS.bdot w2 z11 = true := by decide
theorem sg_ef4_w2_14 : SS.bdot w2 z14 = true := by decide
theorem sg_ef4_w2_15 : SS.bdot w2 z15 = true := by decide
theorem sg_ef4_w3_2 : SS.bdot w3 z2 = false := by decide
theorem sg_ef4_w3_3 : SS.bdot w3 z3 = true := by decide
theorem sg_ef4_w3_6 : SS.bdot w3 z6 = false := by decide
theorem sg_ef4_w3_7 : SS.bdot w3 z7 = true := by decide
theorem sg_ef4_w3_10 : SS.bdot w3 z10 = false := by decide
theorem sg_ef4_w3_11 : SS.bdot w3 z11 = true := by decide
theorem sg_ef4_w3_14 : SS.bdot w3 z14 = false := by decide
theorem sg_ef4_w3_15 : SS.bdot w3 z15 = true := by decide
theorem sg_ef4_w5_2 : SS.bdot w5 z2 = false := by decide
theorem sg_ef4_w5_3 : SS.bdot w5 z3 = false := by decide
theorem sg_ef4_w5_6 : SS.bdot w5 z6 = true := by decide
theorem sg_ef4_w5_7 : SS.bdot w5 z7 = true := by decide
theorem sg_ef4_w5_10 : SS.bdot w5 z10 = false := by decide
theorem sg_ef4_w5_11 : SS.bdot w5 z11 = false := by decide
theorem sg_ef4_w5_14 : SS.bdot w5 z14 = true := by decide
theorem sg_ef4_w5_15 : SS.bdot w5 z15 = true := by decide

theorem incidence_ef5 :
    S1.filter (fun y => SS.bxor y ef5 ∈ S0) = {z0, z1, z4, z5, z8, z9, z12, z13} := by decide
theorem flip_ef5_0 : SS.bxor z0 ef5 = y2 := by decide
theorem flip_ef5_1 : SS.bxor z1 ef5 = y3 := by decide
theorem flip_ef5_4 : SS.bxor z4 ef5 = y6 := by decide
theorem flip_ef5_5 : SS.bxor z5 ef5 = y7 := by decide
theorem flip_ef5_8 : SS.bxor z8 ef5 = y10 := by decide
theorem flip_ef5_9 : SS.bxor z9 ef5 = y11 := by decide
theorem flip_ef5_12 : SS.bxor z12 ef5 = y14 := by decide
theorem flip_ef5_13 : SS.bxor z13 ef5 = y15 := by decide
theorem sg_ef5_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg_ef5_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg_ef5_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg_ef5_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg_ef5_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_ef5_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg_ef5_w0_12 : SS.bdot w0 z12 = false := by decide
theorem sg_ef5_w0_13 : SS.bdot w0 z13 = false := by decide
theorem sg_ef5_w2_0 : SS.bdot w2 z0 = true := by decide
theorem sg_ef5_w2_1 : SS.bdot w2 z1 = false := by decide
theorem sg_ef5_w2_4 : SS.bdot w2 z4 = false := by decide
theorem sg_ef5_w2_5 : SS.bdot w2 z5 = false := by decide
theorem sg_ef5_w2_8 : SS.bdot w2 z8 = false := by decide
theorem sg_ef5_w2_9 : SS.bdot w2 z9 = false := by decide
theorem sg_ef5_w2_12 : SS.bdot w2 z12 = false := by decide
theorem sg_ef5_w2_13 : SS.bdot w2 z13 = true := by decide

theorem incidence_ef6 :
    S1.filter (fun y => SS.bxor y ef6 ∈ S0) = {z4, z5, z6, z7, z12, z13, z14, z15} := by decide
theorem flip_ef6_4 : SS.bxor z4 ef6 = y0 := by decide
theorem flip_ef6_5 : SS.bxor z5 ef6 = y1 := by decide
theorem flip_ef6_6 : SS.bxor z6 ef6 = y2 := by decide
theorem flip_ef6_7 : SS.bxor z7 ef6 = y3 := by decide
theorem flip_ef6_12 : SS.bxor z12 ef6 = y8 := by decide
theorem flip_ef6_13 : SS.bxor z13 ef6 = y9 := by decide
theorem flip_ef6_14 : SS.bxor z14 ef6 = y10 := by decide
theorem flip_ef6_15 : SS.bxor z15 ef6 = y11 := by decide
theorem sg_ef6_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg_ef6_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg_ef6_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg_ef6_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg_ef6_w0_12 : SS.bdot w0 z12 = false := by decide
theorem sg_ef6_w0_13 : SS.bdot w0 z13 = false := by decide
theorem sg_ef6_w0_14 : SS.bdot w0 z14 = false := by decide
theorem sg_ef6_w0_15 : SS.bdot w0 z15 = false := by decide
theorem sg_ef6_w1_4 : SS.bdot w1 z4 = false := by decide
theorem sg_ef6_w1_5 : SS.bdot w1 z5 = true := by decide
theorem sg_ef6_w1_6 : SS.bdot w1 z6 = true := by decide
theorem sg_ef6_w1_7 : SS.bdot w1 z7 = false := by decide
theorem sg_ef6_w1_12 : SS.bdot w1 z12 = true := by decide
theorem sg_ef6_w1_13 : SS.bdot w1 z13 = false := by decide
theorem sg_ef6_w1_14 : SS.bdot w1 z14 = false := by decide
theorem sg_ef6_w1_15 : SS.bdot w1 z15 = true := by decide
theorem sg_ef6_w2_4 : SS.bdot w2 z4 = false := by decide
theorem sg_ef6_w2_5 : SS.bdot w2 z5 = false := by decide
theorem sg_ef6_w2_6 : SS.bdot w2 z6 = false := by decide
theorem sg_ef6_w2_7 : SS.bdot w2 z7 = true := by decide
theorem sg_ef6_w2_12 : SS.bdot w2 z12 = false := by decide
theorem sg_ef6_w2_13 : SS.bdot w2 z13 = true := by decide
theorem sg_ef6_w2_14 : SS.bdot w2 z14 = true := by decide
theorem sg_ef6_w2_15 : SS.bdot w2 z15 = true := by decide
theorem sg_ef6_w3_4 : SS.bdot w3 z4 = false := by decide
theorem sg_ef6_w3_5 : SS.bdot w3 z5 = true := by decide
theorem sg_ef6_w3_6 : SS.bdot w3 z6 = false := by decide
theorem sg_ef6_w3_7 : SS.bdot w3 z7 = true := by decide
theorem sg_ef6_w3_12 : SS.bdot w3 z12 = false := by decide
theorem sg_ef6_w3_13 : SS.bdot w3 z13 = true := by decide
theorem sg_ef6_w3_14 : SS.bdot w3 z14 = false := by decide
theorem sg_ef6_w3_15 : SS.bdot w3 z15 = true := by decide
theorem sg_ef6_w4_4 : SS.bdot w4 z4 = false := by decide
theorem sg_ef6_w4_5 : SS.bdot w4 z5 = false := by decide
theorem sg_ef6_w4_6 : SS.bdot w4 z6 = true := by decide
theorem sg_ef6_w4_7 : SS.bdot w4 z7 = true := by decide
theorem sg_ef6_w4_12 : SS.bdot w4 z12 = false := by decide
theorem sg_ef6_w4_13 : SS.bdot w4 z13 = false := by decide
theorem sg_ef6_w4_14 : SS.bdot w4 z14 = true := by decide
theorem sg_ef6_w4_15 : SS.bdot w4 z15 = true := by decide

theorem incidence_ef7 :
    S1.filter (fun y => SS.bxor y ef7 ∈ S0) = {z0, z1, z2, z3, z8, z9, z10, z11} := by decide
theorem flip_ef7_0 : SS.bxor z0 ef7 = y4 := by decide
theorem flip_ef7_1 : SS.bxor z1 ef7 = y5 := by decide
theorem flip_ef7_2 : SS.bxor z2 ef7 = y6 := by decide
theorem flip_ef7_3 : SS.bxor z3 ef7 = y7 := by decide
theorem flip_ef7_8 : SS.bxor z8 ef7 = y12 := by decide
theorem flip_ef7_9 : SS.bxor z9 ef7 = y13 := by decide
theorem flip_ef7_10 : SS.bxor z10 ef7 = y14 := by decide
theorem flip_ef7_11 : SS.bxor z11 ef7 = y15 := by decide
theorem sg_ef7_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg_ef7_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg_ef7_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg_ef7_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg_ef7_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_ef7_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg_ef7_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg_ef7_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg_ef7_w2_0 : SS.bdot w2 z0 = true := by decide
theorem sg_ef7_w2_1 : SS.bdot w2 z1 = false := by decide
theorem sg_ef7_w2_2 : SS.bdot w2 z2 = false := by decide
theorem sg_ef7_w2_3 : SS.bdot w2 z3 = false := by decide
theorem sg_ef7_w2_8 : SS.bdot w2 z8 = false := by decide
theorem sg_ef7_w2_9 : SS.bdot w2 z9 = false := by decide
theorem sg_ef7_w2_10 : SS.bdot w2 z10 = false := by decide
theorem sg_ef7_w2_11 : SS.bdot w2 z11 = true := by decide

theorem incidence_ef8 :
    S1.filter (fun y => SS.bxor y ef8 ∈ S0) = {z8, z9, z10, z11, z12, z13, z14, z15} := by decide
theorem flip_ef8_8 : SS.bxor z8 ef8 = y0 := by decide
theorem flip_ef8_9 : SS.bxor z9 ef8 = y1 := by decide
theorem flip_ef8_10 : SS.bxor z10 ef8 = y2 := by decide
theorem flip_ef8_11 : SS.bxor z11 ef8 = y3 := by decide
theorem flip_ef8_12 : SS.bxor z12 ef8 = y4 := by decide
theorem flip_ef8_13 : SS.bxor z13 ef8 = y5 := by decide
theorem flip_ef8_14 : SS.bxor z14 ef8 = y6 := by decide
theorem flip_ef8_15 : SS.bxor z15 ef8 = y7 := by decide
theorem sg_ef8_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_ef8_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg_ef8_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg_ef8_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg_ef8_w0_12 : SS.bdot w0 z12 = false := by decide
theorem sg_ef8_w0_13 : SS.bdot w0 z13 = false := by decide
theorem sg_ef8_w0_14 : SS.bdot w0 z14 = false := by decide
theorem sg_ef8_w0_15 : SS.bdot w0 z15 = false := by decide
theorem sg_ef8_w1_8 : SS.bdot w1 z8 = false := by decide
theorem sg_ef8_w1_9 : SS.bdot w1 z9 = true := by decide
theorem sg_ef8_w1_10 : SS.bdot w1 z10 = true := by decide
theorem sg_ef8_w1_11 : SS.bdot w1 z11 = false := by decide
theorem sg_ef8_w1_12 : SS.bdot w1 z12 = true := by decide
theorem sg_ef8_w1_13 : SS.bdot w1 z13 = false := by decide
theorem sg_ef8_w1_14 : SS.bdot w1 z14 = false := by decide
theorem sg_ef8_w1_15 : SS.bdot w1 z15 = true := by decide
theorem sg_ef8_w2_8 : SS.bdot w2 z8 = false := by decide
theorem sg_ef8_w2_9 : SS.bdot w2 z9 = false := by decide
theorem sg_ef8_w2_10 : SS.bdot w2 z10 = false := by decide
theorem sg_ef8_w2_11 : SS.bdot w2 z11 = true := by decide
theorem sg_ef8_w2_12 : SS.bdot w2 z12 = false := by decide
theorem sg_ef8_w2_13 : SS.bdot w2 z13 = true := by decide
theorem sg_ef8_w2_14 : SS.bdot w2 z14 = true := by decide
theorem sg_ef8_w2_15 : SS.bdot w2 z15 = true := by decide
theorem sg_ef8_w3_8 : SS.bdot w3 z8 = false := by decide
theorem sg_ef8_w3_9 : SS.bdot w3 z9 = true := by decide
theorem sg_ef8_w3_10 : SS.bdot w3 z10 = false := by decide
theorem sg_ef8_w3_11 : SS.bdot w3 z11 = true := by decide
theorem sg_ef8_w3_12 : SS.bdot w3 z12 = false := by decide
theorem sg_ef8_w3_13 : SS.bdot w3 z13 = true := by decide
theorem sg_ef8_w3_14 : SS.bdot w3 z14 = false := by decide
theorem sg_ef8_w3_15 : SS.bdot w3 z15 = true := by decide
theorem sg_ef8_w4_8 : SS.bdot w4 z8 = false := by decide
theorem sg_ef8_w4_9 : SS.bdot w4 z9 = false := by decide
theorem sg_ef8_w4_10 : SS.bdot w4 z10 = true := by decide
theorem sg_ef8_w4_11 : SS.bdot w4 z11 = true := by decide
theorem sg_ef8_w4_12 : SS.bdot w4 z12 = false := by decide
theorem sg_ef8_w4_13 : SS.bdot w4 z13 = false := by decide
theorem sg_ef8_w4_14 : SS.bdot w4 z14 = true := by decide
theorem sg_ef8_w4_15 : SS.bdot w4 z15 = true := by decide

theorem incidence_ef9 :
    S1.filter (fun y => SS.bxor y ef9 ∈ S0) = {z0, z1, z2, z3, z4, z5, z6, z7} := by decide
theorem flip_ef9_0 : SS.bxor z0 ef9 = y8 := by decide
theorem flip_ef9_1 : SS.bxor z1 ef9 = y9 := by decide
theorem flip_ef9_2 : SS.bxor z2 ef9 = y10 := by decide
theorem flip_ef9_3 : SS.bxor z3 ef9 = y11 := by decide
theorem flip_ef9_4 : SS.bxor z4 ef9 = y12 := by decide
theorem flip_ef9_5 : SS.bxor z5 ef9 = y13 := by decide
theorem flip_ef9_6 : SS.bxor z6 ef9 = y14 := by decide
theorem flip_ef9_7 : SS.bxor z7 ef9 = y15 := by decide
theorem sg_ef9_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg_ef9_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg_ef9_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg_ef9_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg_ef9_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg_ef9_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg_ef9_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg_ef9_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg_ef9_w2_0 : SS.bdot w2 z0 = true := by decide
theorem sg_ef9_w2_1 : SS.bdot w2 z1 = false := by decide
theorem sg_ef9_w2_2 : SS.bdot w2 z2 = false := by decide
theorem sg_ef9_w2_3 : SS.bdot w2 z3 = false := by decide
theorem sg_ef9_w2_4 : SS.bdot w2 z4 = false := by decide
theorem sg_ef9_w2_5 : SS.bdot w2 z5 = false := by decide
theorem sg_ef9_w2_6 : SS.bdot w2 z6 = false := by decide
theorem sg_ef9_w2_7 : SS.bdot w2 z7 = true := by decide

/-! ## The moment system -/

/-- The two normalizations, the twenty-one moment equalities, and the
nonnegativity of every probability. -/
structure MomentSystem (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real) : Prop where
  n0 : q0 + q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 + q9 + q10 + q11 + q12 + q13 + q14 + q15 = 1
  n1 : r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15 = 1
  m1 : q8 + q9 + q10 + q11 + q12 + q13 + q14 + q15 = r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15
  m2 : q4 + q5 + q6 + q7 + q12 + q13 + q14 + q15 = r4 + r5 + r6 + r7 + r12 + r13 + r14 + r15
  m3 : q2 + q3 + q6 + q7 + q10 + q11 + q14 + q15 = r2 + r3 + r6 + r7 + r10 + r11 + r14 + r15
  m4 : q1 + q3 + q5 + q7 + q9 + q11 + q13 + q15 = r1 + r3 + r5 + r7 + r9 + r11 + r13 + r15
  m5 : q3 + q5 + q6 + q7 + q9 + q10 + q11 + q12 + q13 + q14 = r0 + r7 + r11 + r13 + r14 + r15
  m6 : q1 + q2 + q4 + q7 + q8 + q11 + q13 + q14 = r0 + r3 + r5 + r6 + r9 + r10 + r12 + r15
  m12 : q12 + q13 + q14 + q15 = r12 + r13 + r14 + r15
  m13 : q10 + q11 + q14 + q15 = r10 + r11 + r14 + r15
  m14 : q9 + q11 + q13 + q15 = r9 + r11 + r13 + r15
  m15 : q9 + q10 + q11 + q12 + q13 + q14 = r11 + r13 + r14 + r15
  m16 : q8 + q11 + q13 + q14 = r9 + r10 + r12 + r15
  m23 : q6 + q7 + q14 + q15 = r6 + r7 + r14 + r15
  m24 : q5 + q7 + q13 + q15 = r5 + r7 + r13 + r15
  m25 : q5 + q6 + q7 + q12 + q13 + q14 = r7 + r13 + r14 + r15
  m26 : q4 + q7 + q13 + q14 = r5 + r6 + r12 + r15
  m34 : q3 + q7 + q11 + q15 = r3 + r7 + r11 + r15
  m35 : q3 + q6 + q7 + q10 + q11 + q14 = r7 + r11 + r14 + r15
  m36 : q2 + q7 + q11 + q14 = r3 + r6 + r10 + r15
  m45 : q3 + q5 + q7 + q9 + q11 + q13 = r7 + r11 + r13 + r15
  m46 : q1 + q7 + q11 + q13 = r3 + r5 + r9 + r15
  m56 : q7 + q11 + q13 + q14 = r0 + r15

  nq0 : 0 ≤ q0
  nq1 : 0 ≤ q1
  nq2 : 0 ≤ q2
  nq3 : 0 ≤ q3
  nq4 : 0 ≤ q4
  nq5 : 0 ≤ q5
  nq6 : 0 ≤ q6
  nq7 : 0 ≤ q7
  nq8 : 0 ≤ q8
  nq9 : 0 ≤ q9
  nq10 : 0 ≤ q10
  nq11 : 0 ≤ q11
  nq12 : 0 ≤ q12
  nq13 : 0 ≤ q13
  nq14 : 0 ≤ q14
  nq15 : 0 ≤ q15
  nr0 : 0 ≤ r0
  nr1 : 0 ≤ r1
  nr2 : 0 ≤ r2
  nr3 : 0 ≤ r3
  nr4 : 0 ≤ r4
  nr5 : 0 ≤ r5
  nr6 : 0 ≤ r6
  nr7 : 0 ≤ r7
  nr8 : 0 ≤ r8
  nr9 : 0 ≤ r9
  nr10 : 0 ≤ r10
  nr11 : 0 ≤ r11
  nr12 : 0 ≤ r12
  nr13 : 0 ≤ r13
  nr14 : 0 ≤ r14
  nr15 : 0 ≤ r15

/-- The exact moment normal form on the `K_5` labelling. -/
theorem MomentSystem.endpoints {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    q15 = 1/8
      ∧ r0 = q15
      ∧ q14 + q13 + q11 + q7 = q0 + 1/8
      ∧ q14 + q12 + q10 + q6 = q1 + 1/8
      ∧ q13 + q12 + q9 + q5 = q2 + 1/8
      ∧ q11 + q10 + q9 + q3 = q4 + 1/8
      ∧ q7 + q6 + q5 + q3 = q8 + 1/8
      ∧ q0 + q1 + q2 + q4 + q8 = 3/8
      ∧ q14 + q13 + q11 + q7 + q12 + q10 + q6 + q9 + q5 + q3 = 1/2 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, m12, m13, m14, m15, m16, m23, m24, m25, m26, m34, m35, m36, m45, m46, m56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- The distinguished string is always active. -/
theorem MomentSystem.endpoints_pos {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    0 < r0 := by
  obtain ⟨e1, e2, _, _, _, _, _, _, _⟩ := h.endpoints
  linarith

/-! ## The Walsh expansions -/

def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),
      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

theorem ex_ef0_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w0 = star (c y1) * d z1 + star (c y2) * d z2 + star (c y4) * d z4 + star (c y7) * d z7 + star (c y8) * d z8 + star (c y11) * d z11 + star (c y13) * d z13 + star (c y14) * d z14 := by
  unfold offSum
  rw [incidence_ef0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef0_1, flip_ef0_2, flip_ef0_4, flip_ef0_7, flip_ef0_8, flip_ef0_11, flip_ef0_13, flip_ef0_14]
  simp only [sg_ef0_w0_1, sg_ef0_w0_2, sg_ef0_w0_4, sg_ef0_w0_7, sg_ef0_w0_8, sg_ef0_w0_11, sg_ef0_w0_13, sg_ef0_w0_14, SixQubit.signMul_false]
  try ring

theorem ex_ef0_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w2 = star (c y1) * d z1 + star (c y2) * d z2 + star (c y4) * d z4 - star (c y7) * d z7 + star (c y8) * d z8 - star (c y11) * d z11 - star (c y13) * d z13 - star (c y14) * d z14 := by
  unfold offSum
  rw [incidence_ef0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef0_1, flip_ef0_2, flip_ef0_4, flip_ef0_7, flip_ef0_8, flip_ef0_11, flip_ef0_13, flip_ef0_14]
  simp only [sg_ef0_w2_1, sg_ef0_w2_2, sg_ef0_w2_4, sg_ef0_w2_7, sg_ef0_w2_8, sg_ef0_w2_11, sg_ef0_w2_13, sg_ef0_w2_14, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef0_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w3 = - star (c y1) * d z1 + star (c y2) * d z2 + star (c y4) * d z4 - star (c y7) * d z7 + star (c y8) * d z8 - star (c y11) * d z11 - star (c y13) * d z13 + star (c y14) * d z14 := by
  unfold offSum
  rw [incidence_ef0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef0_1, flip_ef0_2, flip_ef0_4, flip_ef0_7, flip_ef0_8, flip_ef0_11, flip_ef0_13, flip_ef0_14]
  simp only [sg_ef0_w3_1, sg_ef0_w3_2, sg_ef0_w3_4, sg_ef0_w3_7, sg_ef0_w3_8, sg_ef0_w3_11, sg_ef0_w3_13, sg_ef0_w3_14, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef0_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w4 = star (c y1) * d z1 - star (c y2) * d z2 + star (c y4) * d z4 - star (c y7) * d z7 + star (c y8) * d z8 - star (c y11) * d z11 + star (c y13) * d z13 - star (c y14) * d z14 := by
  unfold offSum
  rw [incidence_ef0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef0_1, flip_ef0_2, flip_ef0_4, flip_ef0_7, flip_ef0_8, flip_ef0_11, flip_ef0_13, flip_ef0_14]
  simp only [sg_ef0_w4_1, sg_ef0_w4_2, sg_ef0_w4_4, sg_ef0_w4_7, sg_ef0_w4_8, sg_ef0_w4_11, sg_ef0_w4_13, sg_ef0_w4_14, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef0_w5 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w5 = star (c y1) * d z1 + star (c y2) * d z2 - star (c y4) * d z4 - star (c y7) * d z7 + star (c y8) * d z8 + star (c y11) * d z11 - star (c y13) * d z13 - star (c y14) * d z14 := by
  unfold offSum
  rw [incidence_ef0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef0_1, flip_ef0_2, flip_ef0_4, flip_ef0_7, flip_ef0_8, flip_ef0_11, flip_ef0_13, flip_ef0_14]
  simp only [sg_ef0_w5_1, sg_ef0_w5_2, sg_ef0_w5_4, sg_ef0_w5_7, sg_ef0_w5_8, sg_ef0_w5_11, sg_ef0_w5_13, sg_ef0_w5_14, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef1_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w0 = star (c y0) * d z0 + star (c y3) * d z3 + star (c y5) * d z5 + star (c y6) * d z6 + star (c y9) * d z9 + star (c y10) * d z10 + star (c y12) * d z12 + star (c y15) * d z15 := by
  unfold offSum
  rw [incidence_ef1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef1_0, flip_ef1_3, flip_ef1_5, flip_ef1_6, flip_ef1_9, flip_ef1_10, flip_ef1_12, flip_ef1_15]
  simp only [sg_ef1_w0_0, sg_ef1_w0_3, sg_ef1_w0_5, sg_ef1_w0_6, sg_ef1_w0_9, sg_ef1_w0_10, sg_ef1_w0_12, sg_ef1_w0_15, SixQubit.signMul_false]
  try ring

theorem ex_ef1_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w2 = - star (c y0) * d z0 + star (c y3) * d z3 + star (c y5) * d z5 + star (c y6) * d z6 + star (c y9) * d z9 + star (c y10) * d z10 + star (c y12) * d z12 - star (c y15) * d z15 := by
  unfold offSum
  rw [incidence_ef1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef1_0, flip_ef1_3, flip_ef1_5, flip_ef1_6, flip_ef1_9, flip_ef1_10, flip_ef1_12, flip_ef1_15]
  simp only [sg_ef1_w2_0, sg_ef1_w2_3, sg_ef1_w2_5, sg_ef1_w2_6, sg_ef1_w2_9, sg_ef1_w2_10, sg_ef1_w2_12, sg_ef1_w2_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef2_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w0 = star (c y0) * d z1 + star (c y2) * d z3 + star (c y4) * d z5 + star (c y6) * d z7 + star (c y8) * d z9 + star (c y10) * d z11 + star (c y12) * d z13 + star (c y14) * d z15 := by
  unfold offSum
  rw [incidence_ef2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef2_1, flip_ef2_3, flip_ef2_5, flip_ef2_7, flip_ef2_9, flip_ef2_11, flip_ef2_13, flip_ef2_15]
  simp only [sg_ef2_w0_1, sg_ef2_w0_3, sg_ef2_w0_5, sg_ef2_w0_7, sg_ef2_w0_9, sg_ef2_w0_11, sg_ef2_w0_13, sg_ef2_w0_15, SixQubit.signMul_false]
  try ring

theorem ex_ef2_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w1 = star (c y0) * d z1 - star (c y2) * d z3 - star (c y4) * d z5 + star (c y6) * d z7 - star (c y8) * d z9 + star (c y10) * d z11 + star (c y12) * d z13 - star (c y14) * d z15 := by
  unfold offSum
  rw [incidence_ef2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef2_1, flip_ef2_3, flip_ef2_5, flip_ef2_7, flip_ef2_9, flip_ef2_11, flip_ef2_13, flip_ef2_15]
  simp only [sg_ef2_w1_1, sg_ef2_w1_3, sg_ef2_w1_5, sg_ef2_w1_7, sg_ef2_w1_9, sg_ef2_w1_11, sg_ef2_w1_13, sg_ef2_w1_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef2_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w2 = star (c y0) * d z1 + star (c y2) * d z3 + star (c y4) * d z5 - star (c y6) * d z7 + star (c y8) * d z9 - star (c y10) * d z11 - star (c y12) * d z13 - star (c y14) * d z15 := by
  unfold offSum
  rw [incidence_ef2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef2_1, flip_ef2_3, flip_ef2_5, flip_ef2_7, flip_ef2_9, flip_ef2_11, flip_ef2_13, flip_ef2_15]
  simp only [sg_ef2_w2_1, sg_ef2_w2_3, sg_ef2_w2_5, sg_ef2_w2_7, sg_ef2_w2_9, sg_ef2_w2_11, sg_ef2_w2_13, sg_ef2_w2_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef2_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w4 = star (c y0) * d z1 - star (c y2) * d z3 + star (c y4) * d z5 - star (c y6) * d z7 + star (c y8) * d z9 - star (c y10) * d z11 + star (c y12) * d z13 - star (c y14) * d z15 := by
  unfold offSum
  rw [incidence_ef2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef2_1, flip_ef2_3, flip_ef2_5, flip_ef2_7, flip_ef2_9, flip_ef2_11, flip_ef2_13, flip_ef2_15]
  simp only [sg_ef2_w4_1, sg_ef2_w4_3, sg_ef2_w4_5, sg_ef2_w4_7, sg_ef2_w4_9, sg_ef2_w4_11, sg_ef2_w4_13, sg_ef2_w4_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef2_w5 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w5 = star (c y0) * d z1 + star (c y2) * d z3 - star (c y4) * d z5 - star (c y6) * d z7 + star (c y8) * d z9 + star (c y10) * d z11 - star (c y12) * d z13 - star (c y14) * d z15 := by
  unfold offSum
  rw [incidence_ef2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef2_1, flip_ef2_3, flip_ef2_5, flip_ef2_7, flip_ef2_9, flip_ef2_11, flip_ef2_13, flip_ef2_15]
  simp only [sg_ef2_w5_1, sg_ef2_w5_3, sg_ef2_w5_5, sg_ef2_w5_7, sg_ef2_w5_9, sg_ef2_w5_11, sg_ef2_w5_13, sg_ef2_w5_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef3_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w0 = star (c y1) * d z0 + star (c y3) * d z2 + star (c y5) * d z4 + star (c y7) * d z6 + star (c y9) * d z8 + star (c y11) * d z10 + star (c y13) * d z12 + star (c y15) * d z14 := by
  unfold offSum
  rw [incidence_ef3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef3_0, flip_ef3_2, flip_ef3_4, flip_ef3_6, flip_ef3_8, flip_ef3_10, flip_ef3_12, flip_ef3_14]
  simp only [sg_ef3_w0_0, sg_ef3_w0_2, sg_ef3_w0_4, sg_ef3_w0_6, sg_ef3_w0_8, sg_ef3_w0_10, sg_ef3_w0_12, sg_ef3_w0_14, SixQubit.signMul_false]
  try ring

theorem ex_ef3_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w2 = - star (c y1) * d z0 + star (c y3) * d z2 + star (c y5) * d z4 + star (c y7) * d z6 + star (c y9) * d z8 + star (c y11) * d z10 + star (c y13) * d z12 - star (c y15) * d z14 := by
  unfold offSum
  rw [incidence_ef3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef3_0, flip_ef3_2, flip_ef3_4, flip_ef3_6, flip_ef3_8, flip_ef3_10, flip_ef3_12, flip_ef3_14]
  simp only [sg_ef3_w2_0, sg_ef3_w2_2, sg_ef3_w2_4, sg_ef3_w2_6, sg_ef3_w2_8, sg_ef3_w2_10, sg_ef3_w2_12, sg_ef3_w2_14, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef4_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w0 = star (c y0) * d z2 + star (c y1) * d z3 + star (c y4) * d z6 + star (c y5) * d z7 + star (c y8) * d z10 + star (c y9) * d z11 + star (c y12) * d z14 + star (c y13) * d z15 := by
  unfold offSum
  rw [incidence_ef4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef4_2, flip_ef4_3, flip_ef4_6, flip_ef4_7, flip_ef4_10, flip_ef4_11, flip_ef4_14, flip_ef4_15]
  simp only [sg_ef4_w0_2, sg_ef4_w0_3, sg_ef4_w0_6, sg_ef4_w0_7, sg_ef4_w0_10, sg_ef4_w0_11, sg_ef4_w0_14, sg_ef4_w0_15, SixQubit.signMul_false]
  try ring

theorem ex_ef4_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w1 = star (c y0) * d z2 - star (c y1) * d z3 - star (c y4) * d z6 + star (c y5) * d z7 - star (c y8) * d z10 + star (c y9) * d z11 + star (c y12) * d z14 - star (c y13) * d z15 := by
  unfold offSum
  rw [incidence_ef4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef4_2, flip_ef4_3, flip_ef4_6, flip_ef4_7, flip_ef4_10, flip_ef4_11, flip_ef4_14, flip_ef4_15]
  simp only [sg_ef4_w1_2, sg_ef4_w1_3, sg_ef4_w1_6, sg_ef4_w1_7, sg_ef4_w1_10, sg_ef4_w1_11, sg_ef4_w1_14, sg_ef4_w1_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef4_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w2 = star (c y0) * d z2 + star (c y1) * d z3 + star (c y4) * d z6 - star (c y5) * d z7 + star (c y8) * d z10 - star (c y9) * d z11 - star (c y12) * d z14 - star (c y13) * d z15 := by
  unfold offSum
  rw [incidence_ef4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef4_2, flip_ef4_3, flip_ef4_6, flip_ef4_7, flip_ef4_10, flip_ef4_11, flip_ef4_14, flip_ef4_15]
  simp only [sg_ef4_w2_2, sg_ef4_w2_3, sg_ef4_w2_6, sg_ef4_w2_7, sg_ef4_w2_10, sg_ef4_w2_11, sg_ef4_w2_14, sg_ef4_w2_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef4_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w3 = star (c y0) * d z2 - star (c y1) * d z3 + star (c y4) * d z6 - star (c y5) * d z7 + star (c y8) * d z10 - star (c y9) * d z11 + star (c y12) * d z14 - star (c y13) * d z15 := by
  unfold offSum
  rw [incidence_ef4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef4_2, flip_ef4_3, flip_ef4_6, flip_ef4_7, flip_ef4_10, flip_ef4_11, flip_ef4_14, flip_ef4_15]
  simp only [sg_ef4_w3_2, sg_ef4_w3_3, sg_ef4_w3_6, sg_ef4_w3_7, sg_ef4_w3_10, sg_ef4_w3_11, sg_ef4_w3_14, sg_ef4_w3_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef4_w5 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w5 = star (c y0) * d z2 + star (c y1) * d z3 - star (c y4) * d z6 - star (c y5) * d z7 + star (c y8) * d z10 + star (c y9) * d z11 - star (c y12) * d z14 - star (c y13) * d z15 := by
  unfold offSum
  rw [incidence_ef4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef4_2, flip_ef4_3, flip_ef4_6, flip_ef4_7, flip_ef4_10, flip_ef4_11, flip_ef4_14, flip_ef4_15]
  simp only [sg_ef4_w5_2, sg_ef4_w5_3, sg_ef4_w5_6, sg_ef4_w5_7, sg_ef4_w5_10, sg_ef4_w5_11, sg_ef4_w5_14, sg_ef4_w5_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef5_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef5 w0 = star (c y2) * d z0 + star (c y3) * d z1 + star (c y6) * d z4 + star (c y7) * d z5 + star (c y10) * d z8 + star (c y11) * d z9 + star (c y14) * d z12 + star (c y15) * d z13 := by
  unfold offSum
  rw [incidence_ef5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef5_0, flip_ef5_1, flip_ef5_4, flip_ef5_5, flip_ef5_8, flip_ef5_9, flip_ef5_12, flip_ef5_13]
  simp only [sg_ef5_w0_0, sg_ef5_w0_1, sg_ef5_w0_4, sg_ef5_w0_5, sg_ef5_w0_8, sg_ef5_w0_9, sg_ef5_w0_12, sg_ef5_w0_13, SixQubit.signMul_false]
  try ring

theorem ex_ef5_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef5 w2 = - star (c y2) * d z0 + star (c y3) * d z1 + star (c y6) * d z4 + star (c y7) * d z5 + star (c y10) * d z8 + star (c y11) * d z9 + star (c y14) * d z12 - star (c y15) * d z13 := by
  unfold offSum
  rw [incidence_ef5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef5_0, flip_ef5_1, flip_ef5_4, flip_ef5_5, flip_ef5_8, flip_ef5_9, flip_ef5_12, flip_ef5_13]
  simp only [sg_ef5_w2_0, sg_ef5_w2_1, sg_ef5_w2_4, sg_ef5_w2_5, sg_ef5_w2_8, sg_ef5_w2_9, sg_ef5_w2_12, sg_ef5_w2_13, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef6_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w0 = star (c y0) * d z4 + star (c y1) * d z5 + star (c y2) * d z6 + star (c y3) * d z7 + star (c y8) * d z12 + star (c y9) * d z13 + star (c y10) * d z14 + star (c y11) * d z15 := by
  unfold offSum
  rw [incidence_ef6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef6_4, flip_ef6_5, flip_ef6_6, flip_ef6_7, flip_ef6_12, flip_ef6_13, flip_ef6_14, flip_ef6_15]
  simp only [sg_ef6_w0_4, sg_ef6_w0_5, sg_ef6_w0_6, sg_ef6_w0_7, sg_ef6_w0_12, sg_ef6_w0_13, sg_ef6_w0_14, sg_ef6_w0_15, SixQubit.signMul_false]
  try ring

theorem ex_ef6_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w1 = star (c y0) * d z4 - star (c y1) * d z5 - star (c y2) * d z6 + star (c y3) * d z7 - star (c y8) * d z12 + star (c y9) * d z13 + star (c y10) * d z14 - star (c y11) * d z15 := by
  unfold offSum
  rw [incidence_ef6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef6_4, flip_ef6_5, flip_ef6_6, flip_ef6_7, flip_ef6_12, flip_ef6_13, flip_ef6_14, flip_ef6_15]
  simp only [sg_ef6_w1_4, sg_ef6_w1_5, sg_ef6_w1_6, sg_ef6_w1_7, sg_ef6_w1_12, sg_ef6_w1_13, sg_ef6_w1_14, sg_ef6_w1_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef6_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w2 = star (c y0) * d z4 + star (c y1) * d z5 + star (c y2) * d z6 - star (c y3) * d z7 + star (c y8) * d z12 - star (c y9) * d z13 - star (c y10) * d z14 - star (c y11) * d z15 := by
  unfold offSum
  rw [incidence_ef6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef6_4, flip_ef6_5, flip_ef6_6, flip_ef6_7, flip_ef6_12, flip_ef6_13, flip_ef6_14, flip_ef6_15]
  simp only [sg_ef6_w2_4, sg_ef6_w2_5, sg_ef6_w2_6, sg_ef6_w2_7, sg_ef6_w2_12, sg_ef6_w2_13, sg_ef6_w2_14, sg_ef6_w2_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef6_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w3 = star (c y0) * d z4 - star (c y1) * d z5 + star (c y2) * d z6 - star (c y3) * d z7 + star (c y8) * d z12 - star (c y9) * d z13 + star (c y10) * d z14 - star (c y11) * d z15 := by
  unfold offSum
  rw [incidence_ef6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef6_4, flip_ef6_5, flip_ef6_6, flip_ef6_7, flip_ef6_12, flip_ef6_13, flip_ef6_14, flip_ef6_15]
  simp only [sg_ef6_w3_4, sg_ef6_w3_5, sg_ef6_w3_6, sg_ef6_w3_7, sg_ef6_w3_12, sg_ef6_w3_13, sg_ef6_w3_14, sg_ef6_w3_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef6_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w4 = star (c y0) * d z4 + star (c y1) * d z5 - star (c y2) * d z6 - star (c y3) * d z7 + star (c y8) * d z12 + star (c y9) * d z13 - star (c y10) * d z14 - star (c y11) * d z15 := by
  unfold offSum
  rw [incidence_ef6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef6_4, flip_ef6_5, flip_ef6_6, flip_ef6_7, flip_ef6_12, flip_ef6_13, flip_ef6_14, flip_ef6_15]
  simp only [sg_ef6_w4_4, sg_ef6_w4_5, sg_ef6_w4_6, sg_ef6_w4_7, sg_ef6_w4_12, sg_ef6_w4_13, sg_ef6_w4_14, sg_ef6_w4_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef7_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef7 w0 = star (c y4) * d z0 + star (c y5) * d z1 + star (c y6) * d z2 + star (c y7) * d z3 + star (c y12) * d z8 + star (c y13) * d z9 + star (c y14) * d z10 + star (c y15) * d z11 := by
  unfold offSum
  rw [incidence_ef7]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef7_0, flip_ef7_1, flip_ef7_2, flip_ef7_3, flip_ef7_8, flip_ef7_9, flip_ef7_10, flip_ef7_11]
  simp only [sg_ef7_w0_0, sg_ef7_w0_1, sg_ef7_w0_2, sg_ef7_w0_3, sg_ef7_w0_8, sg_ef7_w0_9, sg_ef7_w0_10, sg_ef7_w0_11, SixQubit.signMul_false]
  try ring

theorem ex_ef7_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef7 w2 = - star (c y4) * d z0 + star (c y5) * d z1 + star (c y6) * d z2 + star (c y7) * d z3 + star (c y12) * d z8 + star (c y13) * d z9 + star (c y14) * d z10 - star (c y15) * d z11 := by
  unfold offSum
  rw [incidence_ef7]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef7_0, flip_ef7_1, flip_ef7_2, flip_ef7_3, flip_ef7_8, flip_ef7_9, flip_ef7_10, flip_ef7_11]
  simp only [sg_ef7_w2_0, sg_ef7_w2_1, sg_ef7_w2_2, sg_ef7_w2_3, sg_ef7_w2_8, sg_ef7_w2_9, sg_ef7_w2_10, sg_ef7_w2_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef8_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef8 w0 = star (c y0) * d z8 + star (c y1) * d z9 + star (c y2) * d z10 + star (c y3) * d z11 + star (c y4) * d z12 + star (c y5) * d z13 + star (c y6) * d z14 + star (c y7) * d z15 := by
  unfold offSum
  rw [incidence_ef8]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef8_8, flip_ef8_9, flip_ef8_10, flip_ef8_11, flip_ef8_12, flip_ef8_13, flip_ef8_14, flip_ef8_15]
  simp only [sg_ef8_w0_8, sg_ef8_w0_9, sg_ef8_w0_10, sg_ef8_w0_11, sg_ef8_w0_12, sg_ef8_w0_13, sg_ef8_w0_14, sg_ef8_w0_15, SixQubit.signMul_false]
  try ring

theorem ex_ef8_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef8 w1 = star (c y0) * d z8 - star (c y1) * d z9 - star (c y2) * d z10 + star (c y3) * d z11 - star (c y4) * d z12 + star (c y5) * d z13 + star (c y6) * d z14 - star (c y7) * d z15 := by
  unfold offSum
  rw [incidence_ef8]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef8_8, flip_ef8_9, flip_ef8_10, flip_ef8_11, flip_ef8_12, flip_ef8_13, flip_ef8_14, flip_ef8_15]
  simp only [sg_ef8_w1_8, sg_ef8_w1_9, sg_ef8_w1_10, sg_ef8_w1_11, sg_ef8_w1_12, sg_ef8_w1_13, sg_ef8_w1_14, sg_ef8_w1_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef8_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef8 w2 = star (c y0) * d z8 + star (c y1) * d z9 + star (c y2) * d z10 - star (c y3) * d z11 + star (c y4) * d z12 - star (c y5) * d z13 - star (c y6) * d z14 - star (c y7) * d z15 := by
  unfold offSum
  rw [incidence_ef8]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef8_8, flip_ef8_9, flip_ef8_10, flip_ef8_11, flip_ef8_12, flip_ef8_13, flip_ef8_14, flip_ef8_15]
  simp only [sg_ef8_w2_8, sg_ef8_w2_9, sg_ef8_w2_10, sg_ef8_w2_11, sg_ef8_w2_12, sg_ef8_w2_13, sg_ef8_w2_14, sg_ef8_w2_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef8_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef8 w3 = star (c y0) * d z8 - star (c y1) * d z9 + star (c y2) * d z10 - star (c y3) * d z11 + star (c y4) * d z12 - star (c y5) * d z13 + star (c y6) * d z14 - star (c y7) * d z15 := by
  unfold offSum
  rw [incidence_ef8]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef8_8, flip_ef8_9, flip_ef8_10, flip_ef8_11, flip_ef8_12, flip_ef8_13, flip_ef8_14, flip_ef8_15]
  simp only [sg_ef8_w3_8, sg_ef8_w3_9, sg_ef8_w3_10, sg_ef8_w3_11, sg_ef8_w3_12, sg_ef8_w3_13, sg_ef8_w3_14, sg_ef8_w3_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef8_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef8 w4 = star (c y0) * d z8 + star (c y1) * d z9 - star (c y2) * d z10 - star (c y3) * d z11 + star (c y4) * d z12 + star (c y5) * d z13 - star (c y6) * d z14 - star (c y7) * d z15 := by
  unfold offSum
  rw [incidence_ef8]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef8_8, flip_ef8_9, flip_ef8_10, flip_ef8_11, flip_ef8_12, flip_ef8_13, flip_ef8_14, flip_ef8_15]
  simp only [sg_ef8_w4_8, sg_ef8_w4_9, sg_ef8_w4_10, sg_ef8_w4_11, sg_ef8_w4_12, sg_ef8_w4_13, sg_ef8_w4_14, sg_ef8_w4_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef9_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef9 w0 = star (c y8) * d z0 + star (c y9) * d z1 + star (c y10) * d z2 + star (c y11) * d z3 + star (c y12) * d z4 + star (c y13) * d z5 + star (c y14) * d z6 + star (c y15) * d z7 := by
  unfold offSum
  rw [incidence_ef9]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef9_0, flip_ef9_1, flip_ef9_2, flip_ef9_3, flip_ef9_4, flip_ef9_5, flip_ef9_6, flip_ef9_7]
  simp only [sg_ef9_w0_0, sg_ef9_w0_1, sg_ef9_w0_2, sg_ef9_w0_3, sg_ef9_w0_4, sg_ef9_w0_5, sg_ef9_w0_6, sg_ef9_w0_7, SixQubit.signMul_false]
  try ring

theorem ex_ef9_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef9 w2 = - star (c y8) * d z0 + star (c y9) * d z1 + star (c y10) * d z2 + star (c y11) * d z3 + star (c y12) * d z4 + star (c y13) * d z5 + star (c y14) * d z6 - star (c y15) * d z7 := by
  unfold offSum
  rw [incidence_ef9]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef9_0, flip_ef9_1, flip_ef9_2, flip_ef9_3, flip_ef9_4, flip_ef9_5, flip_ef9_6, flip_ef9_7]
  simp only [sg_ef9_w2_0, sg_ef9_w2_1, sg_ef9_w2_2, sg_ef9_w2_3, sg_ef9_w2_4, sg_ef9_w2_5, sg_ef9_w2_6, sg_ef9_w2_7, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

/-! ## The reduced Walsh rows -/

/-- Exact row reduction of the admissible dressings of the ten flip masks. -/
theorem rows (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef0 w0 = 0)
    (h1 : offSum c d ef0 w2 = 0)
    (h2 : offSum c d ef0 w3 = 0)
    (h3 : offSum c d ef0 w4 = 0)
    (h4 : offSum c d ef0 w5 = 0)
    (h5 : offSum c d ef1 w0 = 0)
    (h6 : offSum c d ef1 w2 = 0)
    (h7 : offSum c d ef2 w0 = 0)
    (h8 : offSum c d ef2 w1 = 0)
    (h9 : offSum c d ef2 w2 = 0)
    (h10 : offSum c d ef2 w4 = 0)
    (h11 : offSum c d ef2 w5 = 0)
    (h12 : offSum c d ef3 w0 = 0)
    (h13 : offSum c d ef3 w2 = 0)
    (h14 : offSum c d ef4 w0 = 0)
    (h15 : offSum c d ef4 w1 = 0)
    (h16 : offSum c d ef4 w2 = 0)
    (h17 : offSum c d ef4 w3 = 0)
    (h18 : offSum c d ef4 w5 = 0)
    (h19 : offSum c d ef5 w0 = 0)
    (h20 : offSum c d ef5 w2 = 0)
    (h21 : offSum c d ef6 w0 = 0)
    (h22 : offSum c d ef6 w1 = 0)
    (h23 : offSum c d ef6 w2 = 0)
    (h24 : offSum c d ef6 w3 = 0)
    (h25 : offSum c d ef6 w4 = 0)
    (h26 : offSum c d ef7 w0 = 0)
    (h27 : offSum c d ef7 w2 = 0)
    (h28 : offSum c d ef8 w0 = 0)
    (h29 : offSum c d ef8 w1 = 0)
    (h30 : offSum c d ef8 w2 = 0)
    (h31 : offSum c d ef8 w3 = 0)
    (h32 : offSum c d ef8 w4 = 0)
    (h33 : offSum c d ef9 w0 = 0)
    (h34 : offSum c d ef9 w2 = 0) :
    star (c y1) * d z1 - star (c y14) * d z14 = 0
      ∧ star (c y2) * d z2 - star (c y13) * d z13 = 0
      ∧ star (c y4) * d z4 - star (c y11) * d z11 = 0
      ∧ star (c y8) * d z8 - star (c y7) * d z7 = 0
      ∧ star (c y0) * d z1 - star (c y14) * d z15 = 0
      ∧ star (c y2) * d z3 - star (c y12) * d z13 = 0
      ∧ star (c y4) * d z5 - star (c y10) * d z11 = 0
      ∧ star (c y8) * d z9 - star (c y6) * d z7 = 0
      ∧ star (c y0) * d z2 - star (c y13) * d z15 = 0
      ∧ star (c y1) * d z3 - star (c y12) * d z14 = 0
      ∧ star (c y4) * d z6 - star (c y9) * d z11 = 0
      ∧ star (c y8) * d z10 - star (c y5) * d z7 = 0
      ∧ star (c y0) * d z4 - star (c y11) * d z15 = 0
      ∧ star (c y1) * d z5 - star (c y10) * d z14 = 0
      ∧ star (c y2) * d z6 - star (c y9) * d z13 = 0
      ∧ star (c y8) * d z12 - star (c y3) * d z7 = 0
      ∧ star (c y0) * d z8 - star (c y7) * d z15 = 0
      ∧ star (c y1) * d z9 - star (c y6) * d z14 = 0
      ∧ star (c y2) * d z10 - star (c y5) * d z13 = 0
      ∧ star (c y4) * d z12 - star (c y3) * d z11 = 0
      ∧ star (c y12) * d z12 + star (c y3) * d z3 + star (c y10) * d z10 + star (c y5) * d z5 + star (c y6) * d z6 + star (c y9) * d z9 = 0
      ∧ star (c y13) * d z12 + star (c y3) * d z2 + star (c y11) * d z10 + star (c y5) * d z4 + star (c y7) * d z6 + star (c y9) * d z8 = 0
      ∧ star (c y14) * d z12 + star (c y3) * d z1 + star (c y11) * d z9 + star (c y6) * d z4 + star (c y7) * d z5 + star (c y10) * d z8 = 0
      ∧ star (c y14) * d z10 + star (c y5) * d z1 + star (c y13) * d z9 + star (c y6) * d z2 + star (c y7) * d z3 + star (c y12) * d z8 = 0
      ∧ star (c y14) * d z6 + star (c y9) * d z1 + star (c y13) * d z5 + star (c y10) * d z2 + star (c y11) * d z3 + star (c y12) * d z4 = 0
      ∧ star (c y15) * d z15 + star (c y0) * d z0 = 0
      ∧ star (c y15) * d z14 + star (c y1) * d z0 = 0
      ∧ star (c y15) * d z13 + star (c y2) * d z0 = 0
      ∧ star (c y15) * d z11 + star (c y4) * d z0 = 0
      ∧ star (c y15) * d z7 + star (c y8) * d z0 = 0
      ∧ star (c y1) * d z1 + star (c y2) * d z2 + star (c y4) * d z4 + star (c y8) * d z8 = 0
      ∧ star (c y0) * d z1 + star (c y2) * d z3 + star (c y4) * d z5 + star (c y8) * d z9 = 0
      ∧ star (c y0) * d z2 + star (c y1) * d z3 + star (c y4) * d z6 + star (c y8) * d z10 = 0
      ∧ star (c y0) * d z4 + star (c y1) * d z5 + star (c y2) * d z6 + star (c y8) * d z12 = 0
      ∧ star (c y0) * d z8 + star (c y1) * d z9 + star (c y2) * d z10 + star (c y4) * d z12 = 0 := by
  rw [ex_ef0_w0] at h0
  rw [ex_ef0_w2] at h1
  rw [ex_ef0_w3] at h2
  rw [ex_ef0_w4] at h3
  rw [ex_ef0_w5] at h4
  rw [ex_ef1_w0] at h5
  rw [ex_ef1_w2] at h6
  rw [ex_ef2_w0] at h7
  rw [ex_ef2_w1] at h8
  rw [ex_ef2_w2] at h9
  rw [ex_ef2_w4] at h10
  rw [ex_ef2_w5] at h11
  rw [ex_ef3_w0] at h12
  rw [ex_ef3_w2] at h13
  rw [ex_ef4_w0] at h14
  rw [ex_ef4_w1] at h15
  rw [ex_ef4_w2] at h16
  rw [ex_ef4_w3] at h17
  rw [ex_ef4_w5] at h18
  rw [ex_ef5_w0] at h19
  rw [ex_ef5_w2] at h20
  rw [ex_ef6_w0] at h21
  rw [ex_ef6_w1] at h22
  rw [ex_ef6_w2] at h23
  rw [ex_ef6_w3] at h24
  rw [ex_ef6_w4] at h25
  rw [ex_ef7_w0] at h26
  rw [ex_ef7_w2] at h27
  rw [ex_ef8_w0] at h28
  rw [ex_ef8_w1] at h29
  rw [ex_ef8_w2] at h30
  rw [ex_ef8_w3] at h31
  rw [ex_ef8_w4] at h32
  rw [ex_ef9_w0] at h33
  rw [ex_ef9_w2] at h34
  have D0_1 : star (c y1) * d z1 - star (c y14) * d z14 = 0 := by
    linear_combination (1/2 : ℂ) * h1 + (-1/2 : ℂ) * h2
  have D0_2 : star (c y2) * d z2 - star (c y13) * d z13 = 0 := by
    linear_combination (1/2 : ℂ) * h1 + (-1/2 : ℂ) * h3
  have D0_3 : star (c y4) * d z4 - star (c y11) * d z11 = 0 := by
    linear_combination (1/2 : ℂ) * h1 + (-1/2 : ℂ) * h4
  have D0_4 : star (c y8) * d z8 - star (c y7) * d z7 = 0 := by
    linear_combination (-1/2 : ℂ) * h1 + (1/2 : ℂ) * h2 + (1/2 : ℂ) * h3 + (1/2 : ℂ) * h4
  have D1_0 : star (c y0) * d z1 - star (c y14) * d z15 = 0 := by
    linear_combination (1/2 : ℂ) * h8 + (1/2 : ℂ) * h9
  have D1_2 : star (c y2) * d z3 - star (c y12) * d z13 = 0 := by
    linear_combination (1/2 : ℂ) * h9 + (-1/2 : ℂ) * h10
  have D1_3 : star (c y4) * d z5 - star (c y10) * d z11 = 0 := by
    linear_combination (1/2 : ℂ) * h9 + (-1/2 : ℂ) * h11
  have D1_4 : star (c y8) * d z9 - star (c y6) * d z7 = 0 := by
    linear_combination (-1/2 : ℂ) * h8 + (-1/2 : ℂ) * h9 + (1/2 : ℂ) * h10 + (1/2 : ℂ) * h11
  have D2_0 : star (c y0) * d z2 - star (c y13) * d z15 = 0 := by
    linear_combination (1/2 : ℂ) * h15 + (1/2 : ℂ) * h16
  have D2_1 : star (c y1) * d z3 - star (c y12) * d z14 = 0 := by
    linear_combination (1/2 : ℂ) * h16 + (-1/2 : ℂ) * h17
  have D2_3 : star (c y4) * d z6 - star (c y9) * d z11 = 0 := by
    linear_combination (1/2 : ℂ) * h16 + (-1/2 : ℂ) * h18
  have D2_4 : star (c y8) * d z10 - star (c y5) * d z7 = 0 := by
    linear_combination (-1/2 : ℂ) * h15 + (-1/2 : ℂ) * h16 + (1/2 : ℂ) * h17 + (1/2 : ℂ) * h18
  have D3_0 : star (c y0) * d z4 - star (c y11) * d z15 = 0 := by
    linear_combination (1/2 : ℂ) * h22 + (1/2 : ℂ) * h23
  have D3_1 : star (c y1) * d z5 - star (c y10) * d z14 = 0 := by
    linear_combination (1/2 : ℂ) * h23 + (-1/2 : ℂ) * h24
  have D3_2 : star (c y2) * d z6 - star (c y9) * d z13 = 0 := by
    linear_combination (1/2 : ℂ) * h23 + (-1/2 : ℂ) * h25
  have D3_4 : star (c y8) * d z12 - star (c y3) * d z7 = 0 := by
    linear_combination (-1/2 : ℂ) * h22 + (-1/2 : ℂ) * h23 + (1/2 : ℂ) * h24 + (1/2 : ℂ) * h25
  have D4_0 : star (c y0) * d z8 - star (c y7) * d z15 = 0 := by
    linear_combination (1/2 : ℂ) * h29 + (1/2 : ℂ) * h30
  have D4_1 : star (c y1) * d z9 - star (c y6) * d z14 = 0 := by
    linear_combination (1/2 : ℂ) * h30 + (-1/2 : ℂ) * h31
  have D4_2 : star (c y2) * d z10 - star (c y5) * d z13 = 0 := by
    linear_combination (1/2 : ℂ) * h30 + (-1/2 : ℂ) * h32
  have D4_3 : star (c y4) * d z12 - star (c y3) * d z11 = 0 := by
    linear_combination (-1/2 : ℂ) * h29 + (-1/2 : ℂ) * h30 + (1/2 : ℂ) * h31 + (1/2 : ℂ) * h32
  have M0 : star (c y12) * d z12 + star (c y3) * d z3 + star (c y10) * d z10 + star (c y5) * d z5 + star (c y6) * d z6 + star (c y9) * d z9 = 0 := by
    linear_combination (1/2 : ℂ) * h5 + (1/2 : ℂ) * h6
  have M1 : star (c y13) * d z12 + star (c y3) * d z2 + star (c y11) * d z10 + star (c y5) * d z4 + star (c y7) * d z6 + star (c y9) * d z8 = 0 := by
    linear_combination (1/2 : ℂ) * h12 + (1/2 : ℂ) * h13
  have M2 : star (c y14) * d z12 + star (c y3) * d z1 + star (c y11) * d z9 + star (c y6) * d z4 + star (c y7) * d z5 + star (c y10) * d z8 = 0 := by
    linear_combination (1/2 : ℂ) * h19 + (1/2 : ℂ) * h20
  have M3 : star (c y14) * d z10 + star (c y5) * d z1 + star (c y13) * d z9 + star (c y6) * d z2 + star (c y7) * d z3 + star (c y12) * d z8 = 0 := by
    linear_combination (1/2 : ℂ) * h26 + (1/2 : ℂ) * h27
  have M4 : star (c y14) * d z6 + star (c y9) * d z1 + star (c y13) * d z5 + star (c y10) * d z2 + star (c y11) * d z3 + star (c y12) * d z4 = 0 := by
    linear_combination (1/2 : ℂ) * h33 + (1/2 : ℂ) * h34
  have R0 : star (c y15) * d z15 + star (c y0) * d z0 = 0 := by
    linear_combination (1/2 : ℂ) * h5 + (-1/2 : ℂ) * h6
  have R1 : star (c y15) * d z14 + star (c y1) * d z0 = 0 := by
    linear_combination (1/2 : ℂ) * h12 + (-1/2 : ℂ) * h13
  have R2 : star (c y15) * d z13 + star (c y2) * d z0 = 0 := by
    linear_combination (1/2 : ℂ) * h19 + (-1/2 : ℂ) * h20
  have R3 : star (c y15) * d z11 + star (c y4) * d z0 = 0 := by
    linear_combination (1/2 : ℂ) * h26 + (-1/2 : ℂ) * h27
  have R4 : star (c y15) * d z7 + star (c y8) * d z0 = 0 := by
    linear_combination (1/2 : ℂ) * h33 + (-1/2 : ℂ) * h34
  have T0 : star (c y1) * d z1 + star (c y2) * d z2 + star (c y4) * d z4 + star (c y8) * d z8 = 0 := by
    linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1
  have T1 : star (c y0) * d z1 + star (c y2) * d z3 + star (c y4) * d z5 + star (c y8) * d z9 = 0 := by
    linear_combination (1/2 : ℂ) * h7 + (1/2 : ℂ) * h9
  have T2 : star (c y0) * d z2 + star (c y1) * d z3 + star (c y4) * d z6 + star (c y8) * d z10 = 0 := by
    linear_combination (1/2 : ℂ) * h14 + (1/2 : ℂ) * h16
  have T3 : star (c y0) * d z4 + star (c y1) * d z5 + star (c y2) * d z6 + star (c y8) * d z12 = 0 := by
    linear_combination (1/2 : ℂ) * h21 + (1/2 : ℂ) * h23
  have T4 : star (c y0) * d z8 + star (c y1) * d z9 + star (c y2) * d z10 + star (c y4) * d z12 = 0 := by
    linear_combination (1/2 : ℂ) * h28 + (1/2 : ℂ) * h30
  exact ⟨D0_1, D0_2, D0_3, D0_4, D1_0, D1_2, D1_3, D1_4, D2_0, D2_1, D2_3, D2_4, D3_0, D3_1, D3_2, D3_4, D4_0, D4_1, D4_2, D4_3, M0, M1, M2, M3, M4, R0, R1, R2, R3, R4, T0, T1, T2, T3, T4⟩

/-! ## The K_5 data -/

/-- The reciprocal relations at the distinguished string turn every edge
phase defect into an annihilator of both endpoint amplitudes; the
weight-one sums then say `C b = 0`. -/
theorem target_zero (c d : SS.BitString 6 -> ℂ) (hs : d z0 ≠ 0)
    (h0 : offSum c d ef0 w0 = 0)
    (h1 : offSum c d ef0 w2 = 0)
    (h2 : offSum c d ef0 w3 = 0)
    (h3 : offSum c d ef0 w4 = 0)
    (h4 : offSum c d ef0 w5 = 0)
    (h5 : offSum c d ef1 w0 = 0)
    (h6 : offSum c d ef1 w2 = 0)
    (h7 : offSum c d ef2 w0 = 0)
    (h8 : offSum c d ef2 w1 = 0)
    (h9 : offSum c d ef2 w2 = 0)
    (h10 : offSum c d ef2 w4 = 0)
    (h11 : offSum c d ef2 w5 = 0)
    (h12 : offSum c d ef3 w0 = 0)
    (h13 : offSum c d ef3 w2 = 0)
    (h14 : offSum c d ef4 w0 = 0)
    (h15 : offSum c d ef4 w1 = 0)
    (h16 : offSum c d ef4 w2 = 0)
    (h17 : offSum c d ef4 w3 = 0)
    (h18 : offSum c d ef4 w5 = 0)
    (h19 : offSum c d ef5 w0 = 0)
    (h20 : offSum c d ef5 w2 = 0)
    (h21 : offSum c d ef6 w0 = 0)
    (h22 : offSum c d ef6 w1 = 0)
    (h23 : offSum c d ef6 w2 = 0)
    (h24 : offSum c d ef6 w3 = 0)
    (h25 : offSum c d ef6 w4 = 0)
    (h26 : offSum c d ef7 w0 = 0)
    (h27 : offSum c d ef7 w2 = 0)
    (h28 : offSum c d ef8 w0 = 0)
    (h29 : offSum c d ef8 w1 = 0)
    (h30 : offSum c d ef8 w2 = 0)
    (h31 : offSum c d ef8 w3 = 0)
    (h32 : offSum c d ef8 w4 = 0)
    (h33 : offSum c d ef9 w0 = 0)
    (h34 : offSum c d ef9 w2 = 0) :
    star (c y1) * star (c y14) + star (c y2) * star (c y13) + star (c y4) * star (c y11) + star (c y8) * star (c y7) = 0
      ∧ star (c y0) * star (c y14) + star (c y2) * star (c y12) + star (c y4) * star (c y10) + star (c y8) * star (c y6) = 0
      ∧ star (c y0) * star (c y13) + star (c y1) * star (c y12) + star (c y4) * star (c y9) + star (c y8) * star (c y5) = 0
      ∧ star (c y0) * star (c y11) + star (c y1) * star (c y10) + star (c y2) * star (c y9) + star (c y8) * star (c y3) = 0
      ∧ star (c y0) * star (c y7) + star (c y1) * star (c y6) + star (c y2) * star (c y5) + star (c y4) * star (c y3) = 0 := by
  obtain ⟨D0_1, D0_2, D0_3, D0_4, D1_0, D1_2, D1_3, D1_4, D2_0, D2_1, D2_3, D2_4, D3_0, D3_1, D3_2, D3_4, D4_0, D4_1, D4_2, D4_3, M0, M1, M2, M3, M4, R0, R1, R2, R3, R4, T0, T1, T2, T3, T4⟩ := rows c d h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34
  have kb01_0 : star (c y0) * (star (c y15) * d z1 + star (c y14) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D1_0 + (star (c y14) : ℂ) * R0
  have kb01_1 : star (c y1) * (star (c y15) * d z1 + star (c y14) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D0_1 + (star (c y14) : ℂ) * R1
  have kb02_0 : star (c y0) * (star (c y15) * d z2 + star (c y13) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D2_0 + (star (c y13) : ℂ) * R0
  have kb02_2 : star (c y2) * (star (c y15) * d z2 + star (c y13) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D0_2 + (star (c y13) : ℂ) * R2
  have kb03_0 : star (c y0) * (star (c y15) * d z4 + star (c y11) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D3_0 + (star (c y11) : ℂ) * R0
  have kb03_3 : star (c y4) * (star (c y15) * d z4 + star (c y11) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D0_3 + (star (c y11) : ℂ) * R3
  have kb04_0 : star (c y0) * (star (c y15) * d z8 + star (c y7) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D4_0 + (star (c y7) : ℂ) * R0
  have kb04_4 : star (c y8) * (star (c y15) * d z8 + star (c y7) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D0_4 + (star (c y7) : ℂ) * R4
  have kb12_1 : star (c y1) * (star (c y15) * d z3 + star (c y12) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D2_1 + (star (c y12) : ℂ) * R1
  have kb12_2 : star (c y2) * (star (c y15) * d z3 + star (c y12) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D1_2 + (star (c y12) : ℂ) * R2
  have kb13_1 : star (c y1) * (star (c y15) * d z5 + star (c y10) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D3_1 + (star (c y10) : ℂ) * R1
  have kb13_3 : star (c y4) * (star (c y15) * d z5 + star (c y10) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D1_3 + (star (c y10) : ℂ) * R3
  have kb14_1 : star (c y1) * (star (c y15) * d z9 + star (c y6) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D4_1 + (star (c y6) : ℂ) * R1
  have kb14_4 : star (c y8) * (star (c y15) * d z9 + star (c y6) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D1_4 + (star (c y6) : ℂ) * R4
  have kb23_2 : star (c y2) * (star (c y15) * d z6 + star (c y9) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D3_2 + (star (c y9) : ℂ) * R2
  have kb23_3 : star (c y4) * (star (c y15) * d z6 + star (c y9) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D2_3 + (star (c y9) : ℂ) * R3
  have kb24_2 : star (c y2) * (star (c y15) * d z10 + star (c y5) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D4_2 + (star (c y5) : ℂ) * R2
  have kb24_4 : star (c y8) * (star (c y15) * d z10 + star (c y5) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D2_4 + (star (c y5) : ℂ) * R4
  have kb34_3 : star (c y4) * (star (c y15) * d z12 + star (c y3) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D4_3 + (star (c y3) : ℂ) * R3
  have kb34_4 : star (c y8) * (star (c y15) * d z12 + star (c y3) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D3_4 + (star (c y3) : ℂ) * R4
  have sx0 : d z0 * (star (c y1) * star (c y14) + star (c y2) * star (c y13) + star (c y4) * star (c y11) + star (c y8) * star (c y7)) = 0 := by
    linear_combination kb01_1 + kb02_2 + kb03_3 + kb04_4 - (star (c y15) : ℂ) * T0
  have sx1 : d z0 * (star (c y0) * star (c y14) + star (c y2) * star (c y12) + star (c y4) * star (c y10) + star (c y8) * star (c y6)) = 0 := by
    linear_combination kb01_0 + kb12_2 + kb13_3 + kb14_4 - (star (c y15) : ℂ) * T1
  have sx2 : d z0 * (star (c y0) * star (c y13) + star (c y1) * star (c y12) + star (c y4) * star (c y9) + star (c y8) * star (c y5)) = 0 := by
    linear_combination kb02_0 + kb12_1 + kb23_3 + kb24_4 - (star (c y15) : ℂ) * T2
  have sx3 : d z0 * (star (c y0) * star (c y11) + star (c y1) * star (c y10) + star (c y2) * star (c y9) + star (c y8) * star (c y3)) = 0 := by
    linear_combination kb03_0 + kb13_1 + kb23_2 + kb34_4 - (star (c y15) : ℂ) * T3
  have sx4 : d z0 * (star (c y0) * star (c y7) + star (c y1) * star (c y6) + star (c y2) * star (c y5) + star (c y4) * star (c y3)) = 0 := by
    linear_combination kb04_0 + kb14_1 + kb24_2 + kb34_3 - (star (c y15) : ℂ) * T4
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rcases mul_eq_zero.mp sx0 with y | y
    · exact absurd y hs
    · exact y
  · rcases mul_eq_zero.mp sx1 with y | y
    · exact absurd y hs
    · exact y
  · rcases mul_eq_zero.mp sx2 with y | y
    · exact absurd y hs
    · exact y
  · rcases mul_eq_zero.mp sx3 with y | y
    · exact absurd y hs
    · exact y
  · rcases mul_eq_zero.mp sx4 with y | y
    · exact absurd y hs
    · exact y

/-! ## The no-go -/

/-- **Orbit 30 is impossible.** -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11)) (Complex.normSq (c y12)) (Complex.normSq (c y13)) (Complex.normSq (c y14)) (Complex.normSq (c y15))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)) (Complex.normSq (d z12)) (Complex.normSq (d z13)) (Complex.normSq (d z14)) (Complex.normSq (d z15)))
    (h0 : offSum c d ef0 w0 = 0)
    (h1 : offSum c d ef0 w2 = 0)
    (h2 : offSum c d ef0 w3 = 0)
    (h3 : offSum c d ef0 w4 = 0)
    (h4 : offSum c d ef0 w5 = 0)
    (h5 : offSum c d ef1 w0 = 0)
    (h6 : offSum c d ef1 w2 = 0)
    (h7 : offSum c d ef2 w0 = 0)
    (h8 : offSum c d ef2 w1 = 0)
    (h9 : offSum c d ef2 w2 = 0)
    (h10 : offSum c d ef2 w4 = 0)
    (h11 : offSum c d ef2 w5 = 0)
    (h12 : offSum c d ef3 w0 = 0)
    (h13 : offSum c d ef3 w2 = 0)
    (h14 : offSum c d ef4 w0 = 0)
    (h15 : offSum c d ef4 w1 = 0)
    (h16 : offSum c d ef4 w2 = 0)
    (h17 : offSum c d ef4 w3 = 0)
    (h18 : offSum c d ef4 w5 = 0)
    (h19 : offSum c d ef5 w0 = 0)
    (h20 : offSum c d ef5 w2 = 0)
    (h21 : offSum c d ef6 w0 = 0)
    (h22 : offSum c d ef6 w1 = 0)
    (h23 : offSum c d ef6 w2 = 0)
    (h24 : offSum c d ef6 w3 = 0)
    (h25 : offSum c d ef6 w4 = 0)
    (h26 : offSum c d ef7 w0 = 0)
    (h27 : offSum c d ef7 w2 = 0)
    (h28 : offSum c d ef8 w0 = 0)
    (h29 : offSum c d ef8 w1 = 0)
    (h30 : offSum c d ef8 w2 = 0)
    (h31 : offSum c d ef8 w3 = 0)
    (h32 : offSum c d ef8 w4 = 0)
    (h33 : offSum c d ef9 w0 = 0)
    (h34 : offSum c d ef9 w2 = 0)
    : False := by
  obtain ⟨f1, f2, g0, g1, g2, g3, g4, ftb, ftc⟩ := hm.endpoints
  have hpos : (0:Real) < Complex.normSq (d z0) := by
    have := hm.endpoints_pos
    linarith
  have hs : d z0 ≠ 0 := by
    intro hz
    rw [hz, Complex.normSq_zero] at hpos
    norm_num at hpos
  obtain ⟨st0, st1, st2, st3, st4⟩ := target_zero c d hs h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34
  obtain ⟨D0_1, D0_2, D0_3, D0_4, D1_0, D1_2, D1_3, D1_4, D2_0, D2_1, D2_3, D2_4, D3_0, D3_1, D3_2, D3_4, D4_0, D4_1, D4_2, D4_3, M0, M1, M2, M3, M4, R0, R1, R2, R3, R4, T0, T1, T2, T3, T4⟩ := rows c d h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34
  have nss : ∀ w : ℂ, Complex.normSq (star w) = Complex.normSq w :=
    fun w => by simp
  have kb01_0 : star (c y0) * (star (c y15) * d z1 + star (c y14) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D1_0 + (star (c y14) : ℂ) * R0
  have kb01_1 : star (c y1) * (star (c y15) * d z1 + star (c y14) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D0_1 + (star (c y14) : ℂ) * R1
  have kb02_0 : star (c y0) * (star (c y15) * d z2 + star (c y13) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D2_0 + (star (c y13) : ℂ) * R0
  have kb02_2 : star (c y2) * (star (c y15) * d z2 + star (c y13) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D0_2 + (star (c y13) : ℂ) * R2
  have kb03_0 : star (c y0) * (star (c y15) * d z4 + star (c y11) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D3_0 + (star (c y11) : ℂ) * R0
  have kb03_3 : star (c y4) * (star (c y15) * d z4 + star (c y11) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D0_3 + (star (c y11) : ℂ) * R3
  have kb04_0 : star (c y0) * (star (c y15) * d z8 + star (c y7) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D4_0 + (star (c y7) : ℂ) * R0
  have kb04_4 : star (c y8) * (star (c y15) * d z8 + star (c y7) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D0_4 + (star (c y7) : ℂ) * R4
  have kb12_1 : star (c y1) * (star (c y15) * d z3 + star (c y12) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D2_1 + (star (c y12) : ℂ) * R1
  have kb12_2 : star (c y2) * (star (c y15) * d z3 + star (c y12) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D1_2 + (star (c y12) : ℂ) * R2
  have kb13_1 : star (c y1) * (star (c y15) * d z5 + star (c y10) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D3_1 + (star (c y10) : ℂ) * R1
  have kb13_3 : star (c y4) * (star (c y15) * d z5 + star (c y10) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D1_3 + (star (c y10) : ℂ) * R3
  have kb14_1 : star (c y1) * (star (c y15) * d z9 + star (c y6) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D4_1 + (star (c y6) : ℂ) * R1
  have kb14_4 : star (c y8) * (star (c y15) * d z9 + star (c y6) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D1_4 + (star (c y6) : ℂ) * R4
  have kb23_2 : star (c y2) * (star (c y15) * d z6 + star (c y9) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D3_2 + (star (c y9) : ℂ) * R2
  have kb23_3 : star (c y4) * (star (c y15) * d z6 + star (c y9) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D2_3 + (star (c y9) : ℂ) * R3
  have kb24_2 : star (c y2) * (star (c y15) * d z10 + star (c y5) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D4_2 + (star (c y5) : ℂ) * R2
  have kb24_4 : star (c y8) * (star (c y15) * d z10 + star (c y5) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D2_4 + (star (c y5) : ℂ) * R4
  have kb34_3 : star (c y4) * (star (c y15) * d z12 + star (c y3) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D4_3 + (star (c y3) : ℂ) * R3
  have kb34_4 : star (c y8) * (star (c y15) * d z12 + star (c y3) * d z0) = 0 := by
    linear_combination (star (c y15) : ℂ) * D3_4 + (star (c y3) : ℂ) * R4
  have hf0 : star (c y12) * (star (c y15) * d z12 + star (c y3) * d z0) + star (c y3) * (star (c y15) * d z3 + star (c y12) * d z0) + star (c y10) * (star (c y15) * d z10 + star (c y5) * d z0) + star (c y5) * (star (c y15) * d z5 + star (c y10) * d z0) + star (c y6) * (star (c y15) * d z6 + star (c y9) * d z0) + star (c y9) * (star (c y15) * d z9 + star (c y6) * d z0)
      = 2 * d z0 * (star (c y12) * star (c y3) + star (c y10) * star (c y5) + star (c y6) * star (c y9)) := by
    linear_combination (star (c y15) : ℂ) * M0
  have hf1 : star (c y13) * (star (c y15) * d z12 + star (c y3) * d z0) + star (c y3) * (star (c y15) * d z2 + star (c y13) * d z0) + star (c y11) * (star (c y15) * d z10 + star (c y5) * d z0) + star (c y5) * (star (c y15) * d z4 + star (c y11) * d z0) + star (c y7) * (star (c y15) * d z6 + star (c y9) * d z0) + star (c y9) * (star (c y15) * d z8 + star (c y7) * d z0)
      = 2 * d z0 * (star (c y13) * star (c y3) + star (c y11) * star (c y5) + star (c y7) * star (c y9)) := by
    linear_combination (star (c y15) : ℂ) * M1
  have hf2 : star (c y14) * (star (c y15) * d z12 + star (c y3) * d z0) + star (c y3) * (star (c y15) * d z1 + star (c y14) * d z0) + star (c y11) * (star (c y15) * d z9 + star (c y6) * d z0) + star (c y6) * (star (c y15) * d z4 + star (c y11) * d z0) + star (c y7) * (star (c y15) * d z5 + star (c y10) * d z0) + star (c y10) * (star (c y15) * d z8 + star (c y7) * d z0)
      = 2 * d z0 * (star (c y14) * star (c y3) + star (c y11) * star (c y6) + star (c y7) * star (c y10)) := by
    linear_combination (star (c y15) : ℂ) * M2
  have hf3 : star (c y14) * (star (c y15) * d z10 + star (c y5) * d z0) + star (c y5) * (star (c y15) * d z1 + star (c y14) * d z0) + star (c y13) * (star (c y15) * d z9 + star (c y6) * d z0) + star (c y6) * (star (c y15) * d z2 + star (c y13) * d z0) + star (c y7) * (star (c y15) * d z3 + star (c y12) * d z0) + star (c y12) * (star (c y15) * d z8 + star (c y7) * d z0)
      = 2 * d z0 * (star (c y14) * star (c y5) + star (c y13) * star (c y6) + star (c y7) * star (c y12)) := by
    linear_combination (star (c y15) : ℂ) * M3
  have hf4 : star (c y14) * (star (c y15) * d z6 + star (c y9) * d z0) + star (c y9) * (star (c y15) * d z1 + star (c y14) * d z0) + star (c y13) * (star (c y15) * d z5 + star (c y10) * d z0) + star (c y10) * (star (c y15) * d z2 + star (c y13) * d z0) + star (c y11) * (star (c y15) * d z3 + star (c y12) * d z0) + star (c y12) * (star (c y15) * d z4 + star (c y11) * d z0)
      = 2 * d z0 * (star (c y14) * star (c y9) + star (c y13) * star (c y10) + star (c y11) * star (c y12)) := by
    linear_combination (star (c y15) : ℂ) * M4
  have dg0 : Complex.normSq (star (c y14)) + Complex.normSq (star (c y13)) + Complex.normSq (star (c y11)) + Complex.normSq (star (c y7))
      = Complex.normSq (star (c y0)) + 1/8 := by
    simp only [nss]
    linarith
  have dg1 : Complex.normSq (star (c y14)) + Complex.normSq (star (c y12)) + Complex.normSq (star (c y10)) + Complex.normSq (star (c y6))
      = Complex.normSq (star (c y1)) + 1/8 := by
    simp only [nss]
    linarith
  have dg2 : Complex.normSq (star (c y13)) + Complex.normSq (star (c y12)) + Complex.normSq (star (c y9)) + Complex.normSq (star (c y5))
      = Complex.normSq (star (c y2)) + 1/8 := by
    simp only [nss]
    linarith
  have dg3 : Complex.normSq (star (c y11)) + Complex.normSq (star (c y10)) + Complex.normSq (star (c y9)) + Complex.normSq (star (c y3))
      = Complex.normSq (star (c y4)) + 1/8 := by
    simp only [nss]
    linarith
  have dg4 : Complex.normSq (star (c y7)) + Complex.normSq (star (c y6)) + Complex.normSq (star (c y5)) + Complex.normSq (star (c y3))
      = Complex.normSq (star (c y8)) + 1/8 := by
    simp only [nss]
    linarith
  have htb : Complex.normSq (star (c y0)) + Complex.normSq (star (c y1)) + Complex.normSq (star (c y2)) + Complex.normSq (star (c y4)) + Complex.normSq (star (c y8)) = 3/8 := by
    simp only [nss]
    linarith
  have htc : Complex.normSq (star (c y14)) + Complex.normSq (star (c y13)) + Complex.normSq (star (c y11)) + Complex.normSq (star (c y7)) + Complex.normSq (star (c y12)) + Complex.normSq (star (c y10)) + Complex.normSq (star (c y6)) + Complex.normSq (star (c y9)) + Complex.normSq (star (c y5)) + Complex.normSq (star (c y3)) = 1/2 := by
    simp only [nss]
    linarith
  exact SixQubit.K5.no_go
    ⟨hs, st0, st1, st2, st3, st4,
     kb01_0, kb01_1, kb02_0, kb02_2, kb03_0, kb03_3, kb04_0, kb04_4, kb12_1, kb12_2, kb13_1, kb13_3, kb14_1, kb14_4, kb23_2, kb23_3, kb24_2, kb24_4, kb34_3, kb34_4,
     hf0, hf1, hf2, hf3, hf4,
     dg0, dg1, dg2, dg3, dg4, htb, htc⟩

end

end SixQubit.Orbit30
