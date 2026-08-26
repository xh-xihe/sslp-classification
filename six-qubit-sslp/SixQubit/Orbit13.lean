import Mathlib

import SS.FullKL
import SixQubit.Common
import SixQubit.Frame

/-!
# Six-qubit no-go for moment orbit 13

Orbit 13 of `six_qubit_sslp.tex`: q = 4, angle vector
a = (0, 1, 1, 1, 2, 2), residues 0 and 2.

Qubit 1 has angle zero, so the amplitudes group into vectors in `ℂ²`.
The support splits into 4 blocks of two bottom and two top tails, and
every one of the four inner products inside a block is isolated by the
weight-at-most-two rows.  The diagonal conditions make the two block
frames equal, so `SixQubit.Frame.block_zero` kills each block and the
normalization fails.

Everything computational is decided by the Lean kernel; `native_decide`
is not used.
-/

namespace SixQubit.Orbit13

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]

def y0 : SS.BitString 6 := bs false false false false false false  -- 000000
def y1 : SS.BitString 6 := bs false false false false true  true   -- 000011
def y2 : SS.BitString 6 := bs false false true  true  false true   -- 001101
def y3 : SS.BitString 6 := bs false false true  true  true  false  -- 001110
def y4 : SS.BitString 6 := bs false true  false true  false true   -- 010101
def y5 : SS.BitString 6 := bs false true  false true  true  false  -- 010110
def y6 : SS.BitString 6 := bs false true  true  false false true   -- 011001
def y7 : SS.BitString 6 := bs false true  true  false true  false  -- 011010
def y8 : SS.BitString 6 := bs true  false false false false false  -- 100000
def y9 : SS.BitString 6 := bs true  false false false true  true   -- 100011
def y10 : SS.BitString 6 := bs true  false true  true  false true   -- 101101
def y11 : SS.BitString 6 := bs true  false true  true  true  false  -- 101110
def y12 : SS.BitString 6 := bs true  true  false true  false true   -- 110101
def y13 : SS.BitString 6 := bs true  true  false true  true  false  -- 110110
def y14 : SS.BitString 6 := bs true  true  true  false false true   -- 111001
def y15 : SS.BitString 6 := bs true  true  true  false true  false  -- 111010

def z0 : SS.BitString 6 := bs false false false false false true   -- 000001
def z1 : SS.BitString 6 := bs false false false false true  false  -- 000010
def z2 : SS.BitString 6 := bs false false true  true  false false  -- 001100
def z3 : SS.BitString 6 := bs false false true  true  true  true   -- 001111
def z4 : SS.BitString 6 := bs false true  false true  false false  -- 010100
def z5 : SS.BitString 6 := bs false true  false true  true  true   -- 010111
def z6 : SS.BitString 6 := bs false true  true  false false false  -- 011000
def z7 : SS.BitString 6 := bs false true  true  false true  true   -- 011011
def z8 : SS.BitString 6 := bs true  false false false false true   -- 100001
def z9 : SS.BitString 6 := bs true  false false false true  false  -- 100010
def z10 : SS.BitString 6 := bs true  false true  true  false false  -- 101100
def z11 : SS.BitString 6 := bs true  false true  true  true  true   -- 101111
def z12 : SS.BitString 6 := bs true  true  false true  false false  -- 110100
def z13 : SS.BitString 6 := bs true  true  false true  true  true   -- 110111
def z14 : SS.BitString 6 := bs true  true  true  false false false  -- 111000
def z15 : SS.BitString 6 := bs true  true  true  false true  true   -- 111011

def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15}
def S1 : Finset (SS.BitString 6) := {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15}

def av : Fin 6 -> ZMod 4 := ![0, 1, 1, 1, 2, 2]

theorem S0_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 0) = S0 := by
  decide

theorem S1_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 2) = S1 := by
  decide

/-! ## Masks and dressings -/

def ef0 : SS.BitString 6 := bs false false false false false true   -- 000001
def ef1 : SS.BitString 6 := bs false false false false true  false  -- 000010
def efZ : SS.BitString 6 := bs true  false false false false false  -- 100000
def w0 : SS.BitString 6 := bs false false false false false false  -- 000000
def w1 : SS.BitString 6 := bs false false false false false true   -- 000001
def w10 : SS.BitString 6 := bs false true  false false false false  -- 010000
def w11 : SS.BitString 6 := bs true  false false false false false  -- 100000
def w12 : SS.BitString 6 := bs true  false false false false true   -- 100001
def w13 : SS.BitString 6 := bs true  false false false true  false  -- 100010
def w14 : SS.BitString 6 := bs true  false false true  false false  -- 100100
def w15 : SS.BitString 6 := bs true  false true  false false false  -- 101000
def w16 : SS.BitString 6 := bs true  true  false false false false  -- 110000
def w2 : SS.BitString 6 := bs false false false false true  false  -- 000010
def w3 : SS.BitString 6 := bs false false false false true  true   -- 000011
def w4 : SS.BitString 6 := bs false false false true  false false  -- 000100
def w5 : SS.BitString 6 := bs false false false true  false true   -- 000101
def w6 : SS.BitString 6 := bs false false false true  true  false  -- 000110
def w7 : SS.BitString 6 := bs false false true  false false false  -- 001000
def w8 : SS.BitString 6 := bs false false true  false false true   -- 001001
def w9 : SS.BitString 6 := bs false false true  false true  false  -- 001010

/-! ## The off-diagonal layer -/

def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),
      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

theorem incidence_ef0 :
    S1.filter (fun y => SS.bxor y ef0 ∈ S0) = {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15} := by decide
theorem flip_ef0_0 : SS.bxor z0 ef0 = y0 := by decide
theorem flip_ef0_1 : SS.bxor z1 ef0 = y1 := by decide
theorem flip_ef0_2 : SS.bxor z2 ef0 = y2 := by decide
theorem flip_ef0_3 : SS.bxor z3 ef0 = y3 := by decide
theorem flip_ef0_4 : SS.bxor z4 ef0 = y4 := by decide
theorem flip_ef0_5 : SS.bxor z5 ef0 = y5 := by decide
theorem flip_ef0_6 : SS.bxor z6 ef0 = y6 := by decide
theorem flip_ef0_7 : SS.bxor z7 ef0 = y7 := by decide
theorem flip_ef0_8 : SS.bxor z8 ef0 = y8 := by decide
theorem flip_ef0_9 : SS.bxor z9 ef0 = y9 := by decide
theorem flip_ef0_10 : SS.bxor z10 ef0 = y10 := by decide
theorem flip_ef0_11 : SS.bxor z11 ef0 = y11 := by decide
theorem flip_ef0_12 : SS.bxor z12 ef0 = y12 := by decide
theorem flip_ef0_13 : SS.bxor z13 ef0 = y13 := by decide
theorem flip_ef0_14 : SS.bxor z14 ef0 = y14 := by decide
theorem flip_ef0_15 : SS.bxor z15 ef0 = y15 := by decide
theorem sg_ef0_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg_ef0_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg_ef0_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg_ef0_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg_ef0_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg_ef0_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg_ef0_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg_ef0_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg_ef0_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_ef0_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg_ef0_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg_ef0_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg_ef0_w0_12 : SS.bdot w0 z12 = false := by decide
theorem sg_ef0_w0_13 : SS.bdot w0 z13 = false := by decide
theorem sg_ef0_w0_14 : SS.bdot w0 z14 = false := by decide
theorem sg_ef0_w0_15 : SS.bdot w0 z15 = false := by decide
theorem ex_ef0_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w0 = star (c y0) * d z0 + star (c y1) * d z1 + star (c y2) * d z2 + star (c y3) * d z3 + star (c y4) * d z4 + star (c y5) * d z5 + star (c y6) * d z6 + star (c y7) * d z7 + star (c y8) * d z8 + star (c y9) * d z9 + star (c y10) * d z10 + star (c y11) * d z11 + star (c y12) * d z12 + star (c y13) * d z13 + star (c y14) * d z14 + star (c y15) * d z15 := by
  unfold offSum
  rw [incidence_ef0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef0_0, flip_ef0_1, flip_ef0_2, flip_ef0_3, flip_ef0_4, flip_ef0_5, flip_ef0_6, flip_ef0_7, flip_ef0_8, flip_ef0_9, flip_ef0_10, flip_ef0_11, flip_ef0_12, flip_ef0_13, flip_ef0_14, flip_ef0_15]
  simp only [sg_ef0_w0_0, sg_ef0_w0_1, sg_ef0_w0_2, sg_ef0_w0_3, sg_ef0_w0_4, sg_ef0_w0_5, sg_ef0_w0_6, sg_ef0_w0_7, sg_ef0_w0_8, sg_ef0_w0_9, sg_ef0_w0_10, sg_ef0_w0_11, sg_ef0_w0_12, sg_ef0_w0_13, sg_ef0_w0_14, sg_ef0_w0_15, SixQubit.signMul_false]
  try ring
theorem sg_ef0_w1_0 : SS.bdot w1 z0 = true := by decide
theorem sg_ef0_w1_1 : SS.bdot w1 z1 = false := by decide
theorem sg_ef0_w1_2 : SS.bdot w1 z2 = false := by decide
theorem sg_ef0_w1_3 : SS.bdot w1 z3 = true := by decide
theorem sg_ef0_w1_4 : SS.bdot w1 z4 = false := by decide
theorem sg_ef0_w1_5 : SS.bdot w1 z5 = true := by decide
theorem sg_ef0_w1_6 : SS.bdot w1 z6 = false := by decide
theorem sg_ef0_w1_7 : SS.bdot w1 z7 = true := by decide
theorem sg_ef0_w1_8 : SS.bdot w1 z8 = true := by decide
theorem sg_ef0_w1_9 : SS.bdot w1 z9 = false := by decide
theorem sg_ef0_w1_10 : SS.bdot w1 z10 = false := by decide
theorem sg_ef0_w1_11 : SS.bdot w1 z11 = true := by decide
theorem sg_ef0_w1_12 : SS.bdot w1 z12 = false := by decide
theorem sg_ef0_w1_13 : SS.bdot w1 z13 = true := by decide
theorem sg_ef0_w1_14 : SS.bdot w1 z14 = false := by decide
theorem sg_ef0_w1_15 : SS.bdot w1 z15 = true := by decide
theorem ex_ef0_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w1 = - star (c y0) * d z0 + star (c y1) * d z1 + star (c y2) * d z2 - star (c y3) * d z3 + star (c y4) * d z4 - star (c y5) * d z5 + star (c y6) * d z6 - star (c y7) * d z7 - star (c y8) * d z8 + star (c y9) * d z9 + star (c y10) * d z10 - star (c y11) * d z11 + star (c y12) * d z12 - star (c y13) * d z13 + star (c y14) * d z14 - star (c y15) * d z15 := by
  unfold offSum
  rw [incidence_ef0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef0_0, flip_ef0_1, flip_ef0_2, flip_ef0_3, flip_ef0_4, flip_ef0_5, flip_ef0_6, flip_ef0_7, flip_ef0_8, flip_ef0_9, flip_ef0_10, flip_ef0_11, flip_ef0_12, flip_ef0_13, flip_ef0_14, flip_ef0_15]
  simp only [sg_ef0_w1_0, sg_ef0_w1_1, sg_ef0_w1_2, sg_ef0_w1_3, sg_ef0_w1_4, sg_ef0_w1_5, sg_ef0_w1_6, sg_ef0_w1_7, sg_ef0_w1_8, sg_ef0_w1_9, sg_ef0_w1_10, sg_ef0_w1_11, sg_ef0_w1_12, sg_ef0_w1_13, sg_ef0_w1_14, sg_ef0_w1_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef0_w2_0 : SS.bdot w2 z0 = false := by decide
theorem sg_ef0_w2_1 : SS.bdot w2 z1 = true := by decide
theorem sg_ef0_w2_2 : SS.bdot w2 z2 = false := by decide
theorem sg_ef0_w2_3 : SS.bdot w2 z3 = true := by decide
theorem sg_ef0_w2_4 : SS.bdot w2 z4 = false := by decide
theorem sg_ef0_w2_5 : SS.bdot w2 z5 = true := by decide
theorem sg_ef0_w2_6 : SS.bdot w2 z6 = false := by decide
theorem sg_ef0_w2_7 : SS.bdot w2 z7 = true := by decide
theorem sg_ef0_w2_8 : SS.bdot w2 z8 = false := by decide
theorem sg_ef0_w2_9 : SS.bdot w2 z9 = true := by decide
theorem sg_ef0_w2_10 : SS.bdot w2 z10 = false := by decide
theorem sg_ef0_w2_11 : SS.bdot w2 z11 = true := by decide
theorem sg_ef0_w2_12 : SS.bdot w2 z12 = false := by decide
theorem sg_ef0_w2_13 : SS.bdot w2 z13 = true := by decide
theorem sg_ef0_w2_14 : SS.bdot w2 z14 = false := by decide
theorem sg_ef0_w2_15 : SS.bdot w2 z15 = true := by decide
theorem ex_ef0_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w2 = star (c y0) * d z0 - star (c y1) * d z1 + star (c y2) * d z2 - star (c y3) * d z3 + star (c y4) * d z4 - star (c y5) * d z5 + star (c y6) * d z6 - star (c y7) * d z7 + star (c y8) * d z8 - star (c y9) * d z9 + star (c y10) * d z10 - star (c y11) * d z11 + star (c y12) * d z12 - star (c y13) * d z13 + star (c y14) * d z14 - star (c y15) * d z15 := by
  unfold offSum
  rw [incidence_ef0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef0_0, flip_ef0_1, flip_ef0_2, flip_ef0_3, flip_ef0_4, flip_ef0_5, flip_ef0_6, flip_ef0_7, flip_ef0_8, flip_ef0_9, flip_ef0_10, flip_ef0_11, flip_ef0_12, flip_ef0_13, flip_ef0_14, flip_ef0_15]
  simp only [sg_ef0_w2_0, sg_ef0_w2_1, sg_ef0_w2_2, sg_ef0_w2_3, sg_ef0_w2_4, sg_ef0_w2_5, sg_ef0_w2_6, sg_ef0_w2_7, sg_ef0_w2_8, sg_ef0_w2_9, sg_ef0_w2_10, sg_ef0_w2_11, sg_ef0_w2_12, sg_ef0_w2_13, sg_ef0_w2_14, sg_ef0_w2_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef0_w3_0 : SS.bdot w3 z0 = true := by decide
theorem sg_ef0_w3_1 : SS.bdot w3 z1 = true := by decide
theorem sg_ef0_w3_2 : SS.bdot w3 z2 = false := by decide
theorem sg_ef0_w3_3 : SS.bdot w3 z3 = false := by decide
theorem sg_ef0_w3_4 : SS.bdot w3 z4 = false := by decide
theorem sg_ef0_w3_5 : SS.bdot w3 z5 = false := by decide
theorem sg_ef0_w3_6 : SS.bdot w3 z6 = false := by decide
theorem sg_ef0_w3_7 : SS.bdot w3 z7 = false := by decide
theorem sg_ef0_w3_8 : SS.bdot w3 z8 = true := by decide
theorem sg_ef0_w3_9 : SS.bdot w3 z9 = true := by decide
theorem sg_ef0_w3_10 : SS.bdot w3 z10 = false := by decide
theorem sg_ef0_w3_11 : SS.bdot w3 z11 = false := by decide
theorem sg_ef0_w3_12 : SS.bdot w3 z12 = false := by decide
theorem sg_ef0_w3_13 : SS.bdot w3 z13 = false := by decide
theorem sg_ef0_w3_14 : SS.bdot w3 z14 = false := by decide
theorem sg_ef0_w3_15 : SS.bdot w3 z15 = false := by decide
theorem ex_ef0_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w3 = - star (c y0) * d z0 - star (c y1) * d z1 + star (c y2) * d z2 + star (c y3) * d z3 + star (c y4) * d z4 + star (c y5) * d z5 + star (c y6) * d z6 + star (c y7) * d z7 - star (c y8) * d z8 - star (c y9) * d z9 + star (c y10) * d z10 + star (c y11) * d z11 + star (c y12) * d z12 + star (c y13) * d z13 + star (c y14) * d z14 + star (c y15) * d z15 := by
  unfold offSum
  rw [incidence_ef0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef0_0, flip_ef0_1, flip_ef0_2, flip_ef0_3, flip_ef0_4, flip_ef0_5, flip_ef0_6, flip_ef0_7, flip_ef0_8, flip_ef0_9, flip_ef0_10, flip_ef0_11, flip_ef0_12, flip_ef0_13, flip_ef0_14, flip_ef0_15]
  simp only [sg_ef0_w3_0, sg_ef0_w3_1, sg_ef0_w3_2, sg_ef0_w3_3, sg_ef0_w3_4, sg_ef0_w3_5, sg_ef0_w3_6, sg_ef0_w3_7, sg_ef0_w3_8, sg_ef0_w3_9, sg_ef0_w3_10, sg_ef0_w3_11, sg_ef0_w3_12, sg_ef0_w3_13, sg_ef0_w3_14, sg_ef0_w3_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef0_w4_0 : SS.bdot w4 z0 = false := by decide
theorem sg_ef0_w4_1 : SS.bdot w4 z1 = false := by decide
theorem sg_ef0_w4_2 : SS.bdot w4 z2 = true := by decide
theorem sg_ef0_w4_3 : SS.bdot w4 z3 = true := by decide
theorem sg_ef0_w4_4 : SS.bdot w4 z4 = true := by decide
theorem sg_ef0_w4_5 : SS.bdot w4 z5 = true := by decide
theorem sg_ef0_w4_6 : SS.bdot w4 z6 = false := by decide
theorem sg_ef0_w4_7 : SS.bdot w4 z7 = false := by decide
theorem sg_ef0_w4_8 : SS.bdot w4 z8 = false := by decide
theorem sg_ef0_w4_9 : SS.bdot w4 z9 = false := by decide
theorem sg_ef0_w4_10 : SS.bdot w4 z10 = true := by decide
theorem sg_ef0_w4_11 : SS.bdot w4 z11 = true := by decide
theorem sg_ef0_w4_12 : SS.bdot w4 z12 = true := by decide
theorem sg_ef0_w4_13 : SS.bdot w4 z13 = true := by decide
theorem sg_ef0_w4_14 : SS.bdot w4 z14 = false := by decide
theorem sg_ef0_w4_15 : SS.bdot w4 z15 = false := by decide
theorem ex_ef0_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w4 = star (c y0) * d z0 + star (c y1) * d z1 - star (c y2) * d z2 - star (c y3) * d z3 - star (c y4) * d z4 - star (c y5) * d z5 + star (c y6) * d z6 + star (c y7) * d z7 + star (c y8) * d z8 + star (c y9) * d z9 - star (c y10) * d z10 - star (c y11) * d z11 - star (c y12) * d z12 - star (c y13) * d z13 + star (c y14) * d z14 + star (c y15) * d z15 := by
  unfold offSum
  rw [incidence_ef0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef0_0, flip_ef0_1, flip_ef0_2, flip_ef0_3, flip_ef0_4, flip_ef0_5, flip_ef0_6, flip_ef0_7, flip_ef0_8, flip_ef0_9, flip_ef0_10, flip_ef0_11, flip_ef0_12, flip_ef0_13, flip_ef0_14, flip_ef0_15]
  simp only [sg_ef0_w4_0, sg_ef0_w4_1, sg_ef0_w4_2, sg_ef0_w4_3, sg_ef0_w4_4, sg_ef0_w4_5, sg_ef0_w4_6, sg_ef0_w4_7, sg_ef0_w4_8, sg_ef0_w4_9, sg_ef0_w4_10, sg_ef0_w4_11, sg_ef0_w4_12, sg_ef0_w4_13, sg_ef0_w4_14, sg_ef0_w4_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef0_w5_0 : SS.bdot w5 z0 = true := by decide
theorem sg_ef0_w5_1 : SS.bdot w5 z1 = false := by decide
theorem sg_ef0_w5_2 : SS.bdot w5 z2 = true := by decide
theorem sg_ef0_w5_3 : SS.bdot w5 z3 = false := by decide
theorem sg_ef0_w5_4 : SS.bdot w5 z4 = true := by decide
theorem sg_ef0_w5_5 : SS.bdot w5 z5 = false := by decide
theorem sg_ef0_w5_6 : SS.bdot w5 z6 = false := by decide
theorem sg_ef0_w5_7 : SS.bdot w5 z7 = true := by decide
theorem sg_ef0_w5_8 : SS.bdot w5 z8 = true := by decide
theorem sg_ef0_w5_9 : SS.bdot w5 z9 = false := by decide
theorem sg_ef0_w5_10 : SS.bdot w5 z10 = true := by decide
theorem sg_ef0_w5_11 : SS.bdot w5 z11 = false := by decide
theorem sg_ef0_w5_12 : SS.bdot w5 z12 = true := by decide
theorem sg_ef0_w5_13 : SS.bdot w5 z13 = false := by decide
theorem sg_ef0_w5_14 : SS.bdot w5 z14 = false := by decide
theorem sg_ef0_w5_15 : SS.bdot w5 z15 = true := by decide
theorem ex_ef0_w5 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w5 = - star (c y0) * d z0 + star (c y1) * d z1 - star (c y2) * d z2 + star (c y3) * d z3 - star (c y4) * d z4 + star (c y5) * d z5 + star (c y6) * d z6 - star (c y7) * d z7 - star (c y8) * d z8 + star (c y9) * d z9 - star (c y10) * d z10 + star (c y11) * d z11 - star (c y12) * d z12 + star (c y13) * d z13 + star (c y14) * d z14 - star (c y15) * d z15 := by
  unfold offSum
  rw [incidence_ef0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef0_0, flip_ef0_1, flip_ef0_2, flip_ef0_3, flip_ef0_4, flip_ef0_5, flip_ef0_6, flip_ef0_7, flip_ef0_8, flip_ef0_9, flip_ef0_10, flip_ef0_11, flip_ef0_12, flip_ef0_13, flip_ef0_14, flip_ef0_15]
  simp only [sg_ef0_w5_0, sg_ef0_w5_1, sg_ef0_w5_2, sg_ef0_w5_3, sg_ef0_w5_4, sg_ef0_w5_5, sg_ef0_w5_6, sg_ef0_w5_7, sg_ef0_w5_8, sg_ef0_w5_9, sg_ef0_w5_10, sg_ef0_w5_11, sg_ef0_w5_12, sg_ef0_w5_13, sg_ef0_w5_14, sg_ef0_w5_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef0_w7_0 : SS.bdot w7 z0 = false := by decide
theorem sg_ef0_w7_1 : SS.bdot w7 z1 = false := by decide
theorem sg_ef0_w7_2 : SS.bdot w7 z2 = true := by decide
theorem sg_ef0_w7_3 : SS.bdot w7 z3 = true := by decide
theorem sg_ef0_w7_4 : SS.bdot w7 z4 = false := by decide
theorem sg_ef0_w7_5 : SS.bdot w7 z5 = false := by decide
theorem sg_ef0_w7_6 : SS.bdot w7 z6 = true := by decide
theorem sg_ef0_w7_7 : SS.bdot w7 z7 = true := by decide
theorem sg_ef0_w7_8 : SS.bdot w7 z8 = false := by decide
theorem sg_ef0_w7_9 : SS.bdot w7 z9 = false := by decide
theorem sg_ef0_w7_10 : SS.bdot w7 z10 = true := by decide
theorem sg_ef0_w7_11 : SS.bdot w7 z11 = true := by decide
theorem sg_ef0_w7_12 : SS.bdot w7 z12 = false := by decide
theorem sg_ef0_w7_13 : SS.bdot w7 z13 = false := by decide
theorem sg_ef0_w7_14 : SS.bdot w7 z14 = true := by decide
theorem sg_ef0_w7_15 : SS.bdot w7 z15 = true := by decide
theorem ex_ef0_w7 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w7 = star (c y0) * d z0 + star (c y1) * d z1 - star (c y2) * d z2 - star (c y3) * d z3 + star (c y4) * d z4 + star (c y5) * d z5 - star (c y6) * d z6 - star (c y7) * d z7 + star (c y8) * d z8 + star (c y9) * d z9 - star (c y10) * d z10 - star (c y11) * d z11 + star (c y12) * d z12 + star (c y13) * d z13 - star (c y14) * d z14 - star (c y15) * d z15 := by
  unfold offSum
  rw [incidence_ef0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef0_0, flip_ef0_1, flip_ef0_2, flip_ef0_3, flip_ef0_4, flip_ef0_5, flip_ef0_6, flip_ef0_7, flip_ef0_8, flip_ef0_9, flip_ef0_10, flip_ef0_11, flip_ef0_12, flip_ef0_13, flip_ef0_14, flip_ef0_15]
  simp only [sg_ef0_w7_0, sg_ef0_w7_1, sg_ef0_w7_2, sg_ef0_w7_3, sg_ef0_w7_4, sg_ef0_w7_5, sg_ef0_w7_6, sg_ef0_w7_7, sg_ef0_w7_8, sg_ef0_w7_9, sg_ef0_w7_10, sg_ef0_w7_11, sg_ef0_w7_12, sg_ef0_w7_13, sg_ef0_w7_14, sg_ef0_w7_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef0_w8_0 : SS.bdot w8 z0 = true := by decide
theorem sg_ef0_w8_1 : SS.bdot w8 z1 = false := by decide
theorem sg_ef0_w8_2 : SS.bdot w8 z2 = true := by decide
theorem sg_ef0_w8_3 : SS.bdot w8 z3 = false := by decide
theorem sg_ef0_w8_4 : SS.bdot w8 z4 = false := by decide
theorem sg_ef0_w8_5 : SS.bdot w8 z5 = true := by decide
theorem sg_ef0_w8_6 : SS.bdot w8 z6 = true := by decide
theorem sg_ef0_w8_7 : SS.bdot w8 z7 = false := by decide
theorem sg_ef0_w8_8 : SS.bdot w8 z8 = true := by decide
theorem sg_ef0_w8_9 : SS.bdot w8 z9 = false := by decide
theorem sg_ef0_w8_10 : SS.bdot w8 z10 = true := by decide
theorem sg_ef0_w8_11 : SS.bdot w8 z11 = false := by decide
theorem sg_ef0_w8_12 : SS.bdot w8 z12 = false := by decide
theorem sg_ef0_w8_13 : SS.bdot w8 z13 = true := by decide
theorem sg_ef0_w8_14 : SS.bdot w8 z14 = true := by decide
theorem sg_ef0_w8_15 : SS.bdot w8 z15 = false := by decide
theorem ex_ef0_w8 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w8 = - star (c y0) * d z0 + star (c y1) * d z1 - star (c y2) * d z2 + star (c y3) * d z3 + star (c y4) * d z4 - star (c y5) * d z5 - star (c y6) * d z6 + star (c y7) * d z7 - star (c y8) * d z8 + star (c y9) * d z9 - star (c y10) * d z10 + star (c y11) * d z11 + star (c y12) * d z12 - star (c y13) * d z13 - star (c y14) * d z14 + star (c y15) * d z15 := by
  unfold offSum
  rw [incidence_ef0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef0_0, flip_ef0_1, flip_ef0_2, flip_ef0_3, flip_ef0_4, flip_ef0_5, flip_ef0_6, flip_ef0_7, flip_ef0_8, flip_ef0_9, flip_ef0_10, flip_ef0_11, flip_ef0_12, flip_ef0_13, flip_ef0_14, flip_ef0_15]
  simp only [sg_ef0_w8_0, sg_ef0_w8_1, sg_ef0_w8_2, sg_ef0_w8_3, sg_ef0_w8_4, sg_ef0_w8_5, sg_ef0_w8_6, sg_ef0_w8_7, sg_ef0_w8_8, sg_ef0_w8_9, sg_ef0_w8_10, sg_ef0_w8_11, sg_ef0_w8_12, sg_ef0_w8_13, sg_ef0_w8_14, sg_ef0_w8_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem incidence_ef1 :
    S1.filter (fun y => SS.bxor y ef1 ∈ S0) = {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15} := by decide
theorem flip_ef1_0 : SS.bxor z0 ef1 = y1 := by decide
theorem flip_ef1_1 : SS.bxor z1 ef1 = y0 := by decide
theorem flip_ef1_2 : SS.bxor z2 ef1 = y3 := by decide
theorem flip_ef1_3 : SS.bxor z3 ef1 = y2 := by decide
theorem flip_ef1_4 : SS.bxor z4 ef1 = y5 := by decide
theorem flip_ef1_5 : SS.bxor z5 ef1 = y4 := by decide
theorem flip_ef1_6 : SS.bxor z6 ef1 = y7 := by decide
theorem flip_ef1_7 : SS.bxor z7 ef1 = y6 := by decide
theorem flip_ef1_8 : SS.bxor z8 ef1 = y9 := by decide
theorem flip_ef1_9 : SS.bxor z9 ef1 = y8 := by decide
theorem flip_ef1_10 : SS.bxor z10 ef1 = y11 := by decide
theorem flip_ef1_11 : SS.bxor z11 ef1 = y10 := by decide
theorem flip_ef1_12 : SS.bxor z12 ef1 = y13 := by decide
theorem flip_ef1_13 : SS.bxor z13 ef1 = y12 := by decide
theorem flip_ef1_14 : SS.bxor z14 ef1 = y15 := by decide
theorem flip_ef1_15 : SS.bxor z15 ef1 = y14 := by decide
theorem sg_ef1_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg_ef1_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg_ef1_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg_ef1_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg_ef1_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg_ef1_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg_ef1_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg_ef1_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg_ef1_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_ef1_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg_ef1_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg_ef1_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg_ef1_w0_12 : SS.bdot w0 z12 = false := by decide
theorem sg_ef1_w0_13 : SS.bdot w0 z13 = false := by decide
theorem sg_ef1_w0_14 : SS.bdot w0 z14 = false := by decide
theorem sg_ef1_w0_15 : SS.bdot w0 z15 = false := by decide
theorem ex_ef1_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w0 = star (c y1) * d z0 + star (c y0) * d z1 + star (c y3) * d z2 + star (c y2) * d z3 + star (c y5) * d z4 + star (c y4) * d z5 + star (c y7) * d z6 + star (c y6) * d z7 + star (c y9) * d z8 + star (c y8) * d z9 + star (c y11) * d z10 + star (c y10) * d z11 + star (c y13) * d z12 + star (c y12) * d z13 + star (c y15) * d z14 + star (c y14) * d z15 := by
  unfold offSum
  rw [incidence_ef1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef1_0, flip_ef1_1, flip_ef1_2, flip_ef1_3, flip_ef1_4, flip_ef1_5, flip_ef1_6, flip_ef1_7, flip_ef1_8, flip_ef1_9, flip_ef1_10, flip_ef1_11, flip_ef1_12, flip_ef1_13, flip_ef1_14, flip_ef1_15]
  simp only [sg_ef1_w0_0, sg_ef1_w0_1, sg_ef1_w0_2, sg_ef1_w0_3, sg_ef1_w0_4, sg_ef1_w0_5, sg_ef1_w0_6, sg_ef1_w0_7, sg_ef1_w0_8, sg_ef1_w0_9, sg_ef1_w0_10, sg_ef1_w0_11, sg_ef1_w0_12, sg_ef1_w0_13, sg_ef1_w0_14, sg_ef1_w0_15, SixQubit.signMul_false]
  try ring
theorem sg_ef1_w1_0 : SS.bdot w1 z0 = true := by decide
theorem sg_ef1_w1_1 : SS.bdot w1 z1 = false := by decide
theorem sg_ef1_w1_2 : SS.bdot w1 z2 = false := by decide
theorem sg_ef1_w1_3 : SS.bdot w1 z3 = true := by decide
theorem sg_ef1_w1_4 : SS.bdot w1 z4 = false := by decide
theorem sg_ef1_w1_5 : SS.bdot w1 z5 = true := by decide
theorem sg_ef1_w1_6 : SS.bdot w1 z6 = false := by decide
theorem sg_ef1_w1_7 : SS.bdot w1 z7 = true := by decide
theorem sg_ef1_w1_8 : SS.bdot w1 z8 = true := by decide
theorem sg_ef1_w1_9 : SS.bdot w1 z9 = false := by decide
theorem sg_ef1_w1_10 : SS.bdot w1 z10 = false := by decide
theorem sg_ef1_w1_11 : SS.bdot w1 z11 = true := by decide
theorem sg_ef1_w1_12 : SS.bdot w1 z12 = false := by decide
theorem sg_ef1_w1_13 : SS.bdot w1 z13 = true := by decide
theorem sg_ef1_w1_14 : SS.bdot w1 z14 = false := by decide
theorem sg_ef1_w1_15 : SS.bdot w1 z15 = true := by decide
theorem ex_ef1_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w1 = - star (c y1) * d z0 + star (c y0) * d z1 + star (c y3) * d z2 - star (c y2) * d z3 + star (c y5) * d z4 - star (c y4) * d z5 + star (c y7) * d z6 - star (c y6) * d z7 - star (c y9) * d z8 + star (c y8) * d z9 + star (c y11) * d z10 - star (c y10) * d z11 + star (c y13) * d z12 - star (c y12) * d z13 + star (c y15) * d z14 - star (c y14) * d z15 := by
  unfold offSum
  rw [incidence_ef1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef1_0, flip_ef1_1, flip_ef1_2, flip_ef1_3, flip_ef1_4, flip_ef1_5, flip_ef1_6, flip_ef1_7, flip_ef1_8, flip_ef1_9, flip_ef1_10, flip_ef1_11, flip_ef1_12, flip_ef1_13, flip_ef1_14, flip_ef1_15]
  simp only [sg_ef1_w1_0, sg_ef1_w1_1, sg_ef1_w1_2, sg_ef1_w1_3, sg_ef1_w1_4, sg_ef1_w1_5, sg_ef1_w1_6, sg_ef1_w1_7, sg_ef1_w1_8, sg_ef1_w1_9, sg_ef1_w1_10, sg_ef1_w1_11, sg_ef1_w1_12, sg_ef1_w1_13, sg_ef1_w1_14, sg_ef1_w1_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef1_w2_0 : SS.bdot w2 z0 = false := by decide
theorem sg_ef1_w2_1 : SS.bdot w2 z1 = true := by decide
theorem sg_ef1_w2_2 : SS.bdot w2 z2 = false := by decide
theorem sg_ef1_w2_3 : SS.bdot w2 z3 = true := by decide
theorem sg_ef1_w2_4 : SS.bdot w2 z4 = false := by decide
theorem sg_ef1_w2_5 : SS.bdot w2 z5 = true := by decide
theorem sg_ef1_w2_6 : SS.bdot w2 z6 = false := by decide
theorem sg_ef1_w2_7 : SS.bdot w2 z7 = true := by decide
theorem sg_ef1_w2_8 : SS.bdot w2 z8 = false := by decide
theorem sg_ef1_w2_9 : SS.bdot w2 z9 = true := by decide
theorem sg_ef1_w2_10 : SS.bdot w2 z10 = false := by decide
theorem sg_ef1_w2_11 : SS.bdot w2 z11 = true := by decide
theorem sg_ef1_w2_12 : SS.bdot w2 z12 = false := by decide
theorem sg_ef1_w2_13 : SS.bdot w2 z13 = true := by decide
theorem sg_ef1_w2_14 : SS.bdot w2 z14 = false := by decide
theorem sg_ef1_w2_15 : SS.bdot w2 z15 = true := by decide
theorem ex_ef1_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w2 = star (c y1) * d z0 - star (c y0) * d z1 + star (c y3) * d z2 - star (c y2) * d z3 + star (c y5) * d z4 - star (c y4) * d z5 + star (c y7) * d z6 - star (c y6) * d z7 + star (c y9) * d z8 - star (c y8) * d z9 + star (c y11) * d z10 - star (c y10) * d z11 + star (c y13) * d z12 - star (c y12) * d z13 + star (c y15) * d z14 - star (c y14) * d z15 := by
  unfold offSum
  rw [incidence_ef1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef1_0, flip_ef1_1, flip_ef1_2, flip_ef1_3, flip_ef1_4, flip_ef1_5, flip_ef1_6, flip_ef1_7, flip_ef1_8, flip_ef1_9, flip_ef1_10, flip_ef1_11, flip_ef1_12, flip_ef1_13, flip_ef1_14, flip_ef1_15]
  simp only [sg_ef1_w2_0, sg_ef1_w2_1, sg_ef1_w2_2, sg_ef1_w2_3, sg_ef1_w2_4, sg_ef1_w2_5, sg_ef1_w2_6, sg_ef1_w2_7, sg_ef1_w2_8, sg_ef1_w2_9, sg_ef1_w2_10, sg_ef1_w2_11, sg_ef1_w2_12, sg_ef1_w2_13, sg_ef1_w2_14, sg_ef1_w2_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef1_w3_0 : SS.bdot w3 z0 = true := by decide
theorem sg_ef1_w3_1 : SS.bdot w3 z1 = true := by decide
theorem sg_ef1_w3_2 : SS.bdot w3 z2 = false := by decide
theorem sg_ef1_w3_3 : SS.bdot w3 z3 = false := by decide
theorem sg_ef1_w3_4 : SS.bdot w3 z4 = false := by decide
theorem sg_ef1_w3_5 : SS.bdot w3 z5 = false := by decide
theorem sg_ef1_w3_6 : SS.bdot w3 z6 = false := by decide
theorem sg_ef1_w3_7 : SS.bdot w3 z7 = false := by decide
theorem sg_ef1_w3_8 : SS.bdot w3 z8 = true := by decide
theorem sg_ef1_w3_9 : SS.bdot w3 z9 = true := by decide
theorem sg_ef1_w3_10 : SS.bdot w3 z10 = false := by decide
theorem sg_ef1_w3_11 : SS.bdot w3 z11 = false := by decide
theorem sg_ef1_w3_12 : SS.bdot w3 z12 = false := by decide
theorem sg_ef1_w3_13 : SS.bdot w3 z13 = false := by decide
theorem sg_ef1_w3_14 : SS.bdot w3 z14 = false := by decide
theorem sg_ef1_w3_15 : SS.bdot w3 z15 = false := by decide
theorem ex_ef1_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w3 = - star (c y1) * d z0 - star (c y0) * d z1 + star (c y3) * d z2 + star (c y2) * d z3 + star (c y5) * d z4 + star (c y4) * d z5 + star (c y7) * d z6 + star (c y6) * d z7 - star (c y9) * d z8 - star (c y8) * d z9 + star (c y11) * d z10 + star (c y10) * d z11 + star (c y13) * d z12 + star (c y12) * d z13 + star (c y15) * d z14 + star (c y14) * d z15 := by
  unfold offSum
  rw [incidence_ef1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef1_0, flip_ef1_1, flip_ef1_2, flip_ef1_3, flip_ef1_4, flip_ef1_5, flip_ef1_6, flip_ef1_7, flip_ef1_8, flip_ef1_9, flip_ef1_10, flip_ef1_11, flip_ef1_12, flip_ef1_13, flip_ef1_14, flip_ef1_15]
  simp only [sg_ef1_w3_0, sg_ef1_w3_1, sg_ef1_w3_2, sg_ef1_w3_3, sg_ef1_w3_4, sg_ef1_w3_5, sg_ef1_w3_6, sg_ef1_w3_7, sg_ef1_w3_8, sg_ef1_w3_9, sg_ef1_w3_10, sg_ef1_w3_11, sg_ef1_w3_12, sg_ef1_w3_13, sg_ef1_w3_14, sg_ef1_w3_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef1_w4_0 : SS.bdot w4 z0 = false := by decide
theorem sg_ef1_w4_1 : SS.bdot w4 z1 = false := by decide
theorem sg_ef1_w4_2 : SS.bdot w4 z2 = true := by decide
theorem sg_ef1_w4_3 : SS.bdot w4 z3 = true := by decide
theorem sg_ef1_w4_4 : SS.bdot w4 z4 = true := by decide
theorem sg_ef1_w4_5 : SS.bdot w4 z5 = true := by decide
theorem sg_ef1_w4_6 : SS.bdot w4 z6 = false := by decide
theorem sg_ef1_w4_7 : SS.bdot w4 z7 = false := by decide
theorem sg_ef1_w4_8 : SS.bdot w4 z8 = false := by decide
theorem sg_ef1_w4_9 : SS.bdot w4 z9 = false := by decide
theorem sg_ef1_w4_10 : SS.bdot w4 z10 = true := by decide
theorem sg_ef1_w4_11 : SS.bdot w4 z11 = true := by decide
theorem sg_ef1_w4_12 : SS.bdot w4 z12 = true := by decide
theorem sg_ef1_w4_13 : SS.bdot w4 z13 = true := by decide
theorem sg_ef1_w4_14 : SS.bdot w4 z14 = false := by decide
theorem sg_ef1_w4_15 : SS.bdot w4 z15 = false := by decide
theorem ex_ef1_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w4 = star (c y1) * d z0 + star (c y0) * d z1 - star (c y3) * d z2 - star (c y2) * d z3 - star (c y5) * d z4 - star (c y4) * d z5 + star (c y7) * d z6 + star (c y6) * d z7 + star (c y9) * d z8 + star (c y8) * d z9 - star (c y11) * d z10 - star (c y10) * d z11 - star (c y13) * d z12 - star (c y12) * d z13 + star (c y15) * d z14 + star (c y14) * d z15 := by
  unfold offSum
  rw [incidence_ef1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef1_0, flip_ef1_1, flip_ef1_2, flip_ef1_3, flip_ef1_4, flip_ef1_5, flip_ef1_6, flip_ef1_7, flip_ef1_8, flip_ef1_9, flip_ef1_10, flip_ef1_11, flip_ef1_12, flip_ef1_13, flip_ef1_14, flip_ef1_15]
  simp only [sg_ef1_w4_0, sg_ef1_w4_1, sg_ef1_w4_2, sg_ef1_w4_3, sg_ef1_w4_4, sg_ef1_w4_5, sg_ef1_w4_6, sg_ef1_w4_7, sg_ef1_w4_8, sg_ef1_w4_9, sg_ef1_w4_10, sg_ef1_w4_11, sg_ef1_w4_12, sg_ef1_w4_13, sg_ef1_w4_14, sg_ef1_w4_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef1_w6_0 : SS.bdot w6 z0 = false := by decide
theorem sg_ef1_w6_1 : SS.bdot w6 z1 = true := by decide
theorem sg_ef1_w6_2 : SS.bdot w6 z2 = true := by decide
theorem sg_ef1_w6_3 : SS.bdot w6 z3 = false := by decide
theorem sg_ef1_w6_4 : SS.bdot w6 z4 = true := by decide
theorem sg_ef1_w6_5 : SS.bdot w6 z5 = false := by decide
theorem sg_ef1_w6_6 : SS.bdot w6 z6 = false := by decide
theorem sg_ef1_w6_7 : SS.bdot w6 z7 = true := by decide
theorem sg_ef1_w6_8 : SS.bdot w6 z8 = false := by decide
theorem sg_ef1_w6_9 : SS.bdot w6 z9 = true := by decide
theorem sg_ef1_w6_10 : SS.bdot w6 z10 = true := by decide
theorem sg_ef1_w6_11 : SS.bdot w6 z11 = false := by decide
theorem sg_ef1_w6_12 : SS.bdot w6 z12 = true := by decide
theorem sg_ef1_w6_13 : SS.bdot w6 z13 = false := by decide
theorem sg_ef1_w6_14 : SS.bdot w6 z14 = false := by decide
theorem sg_ef1_w6_15 : SS.bdot w6 z15 = true := by decide
theorem ex_ef1_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w6 = star (c y1) * d z0 - star (c y0) * d z1 - star (c y3) * d z2 + star (c y2) * d z3 - star (c y5) * d z4 + star (c y4) * d z5 + star (c y7) * d z6 - star (c y6) * d z7 + star (c y9) * d z8 - star (c y8) * d z9 - star (c y11) * d z10 + star (c y10) * d z11 - star (c y13) * d z12 + star (c y12) * d z13 + star (c y15) * d z14 - star (c y14) * d z15 := by
  unfold offSum
  rw [incidence_ef1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef1_0, flip_ef1_1, flip_ef1_2, flip_ef1_3, flip_ef1_4, flip_ef1_5, flip_ef1_6, flip_ef1_7, flip_ef1_8, flip_ef1_9, flip_ef1_10, flip_ef1_11, flip_ef1_12, flip_ef1_13, flip_ef1_14, flip_ef1_15]
  simp only [sg_ef1_w6_0, sg_ef1_w6_1, sg_ef1_w6_2, sg_ef1_w6_3, sg_ef1_w6_4, sg_ef1_w6_5, sg_ef1_w6_6, sg_ef1_w6_7, sg_ef1_w6_8, sg_ef1_w6_9, sg_ef1_w6_10, sg_ef1_w6_11, sg_ef1_w6_12, sg_ef1_w6_13, sg_ef1_w6_14, sg_ef1_w6_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef1_w7_0 : SS.bdot w7 z0 = false := by decide
theorem sg_ef1_w7_1 : SS.bdot w7 z1 = false := by decide
theorem sg_ef1_w7_2 : SS.bdot w7 z2 = true := by decide
theorem sg_ef1_w7_3 : SS.bdot w7 z3 = true := by decide
theorem sg_ef1_w7_4 : SS.bdot w7 z4 = false := by decide
theorem sg_ef1_w7_5 : SS.bdot w7 z5 = false := by decide
theorem sg_ef1_w7_6 : SS.bdot w7 z6 = true := by decide
theorem sg_ef1_w7_7 : SS.bdot w7 z7 = true := by decide
theorem sg_ef1_w7_8 : SS.bdot w7 z8 = false := by decide
theorem sg_ef1_w7_9 : SS.bdot w7 z9 = false := by decide
theorem sg_ef1_w7_10 : SS.bdot w7 z10 = true := by decide
theorem sg_ef1_w7_11 : SS.bdot w7 z11 = true := by decide
theorem sg_ef1_w7_12 : SS.bdot w7 z12 = false := by decide
theorem sg_ef1_w7_13 : SS.bdot w7 z13 = false := by decide
theorem sg_ef1_w7_14 : SS.bdot w7 z14 = true := by decide
theorem sg_ef1_w7_15 : SS.bdot w7 z15 = true := by decide
theorem ex_ef1_w7 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w7 = star (c y1) * d z0 + star (c y0) * d z1 - star (c y3) * d z2 - star (c y2) * d z3 + star (c y5) * d z4 + star (c y4) * d z5 - star (c y7) * d z6 - star (c y6) * d z7 + star (c y9) * d z8 + star (c y8) * d z9 - star (c y11) * d z10 - star (c y10) * d z11 + star (c y13) * d z12 + star (c y12) * d z13 - star (c y15) * d z14 - star (c y14) * d z15 := by
  unfold offSum
  rw [incidence_ef1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef1_0, flip_ef1_1, flip_ef1_2, flip_ef1_3, flip_ef1_4, flip_ef1_5, flip_ef1_6, flip_ef1_7, flip_ef1_8, flip_ef1_9, flip_ef1_10, flip_ef1_11, flip_ef1_12, flip_ef1_13, flip_ef1_14, flip_ef1_15]
  simp only [sg_ef1_w7_0, sg_ef1_w7_1, sg_ef1_w7_2, sg_ef1_w7_3, sg_ef1_w7_4, sg_ef1_w7_5, sg_ef1_w7_6, sg_ef1_w7_7, sg_ef1_w7_8, sg_ef1_w7_9, sg_ef1_w7_10, sg_ef1_w7_11, sg_ef1_w7_12, sg_ef1_w7_13, sg_ef1_w7_14, sg_ef1_w7_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef1_w9_0 : SS.bdot w9 z0 = false := by decide
theorem sg_ef1_w9_1 : SS.bdot w9 z1 = true := by decide
theorem sg_ef1_w9_2 : SS.bdot w9 z2 = true := by decide
theorem sg_ef1_w9_3 : SS.bdot w9 z3 = false := by decide
theorem sg_ef1_w9_4 : SS.bdot w9 z4 = false := by decide
theorem sg_ef1_w9_5 : SS.bdot w9 z5 = true := by decide
theorem sg_ef1_w9_6 : SS.bdot w9 z6 = true := by decide
theorem sg_ef1_w9_7 : SS.bdot w9 z7 = false := by decide
theorem sg_ef1_w9_8 : SS.bdot w9 z8 = false := by decide
theorem sg_ef1_w9_9 : SS.bdot w9 z9 = true := by decide
theorem sg_ef1_w9_10 : SS.bdot w9 z10 = true := by decide
theorem sg_ef1_w9_11 : SS.bdot w9 z11 = false := by decide
theorem sg_ef1_w9_12 : SS.bdot w9 z12 = false := by decide
theorem sg_ef1_w9_13 : SS.bdot w9 z13 = true := by decide
theorem sg_ef1_w9_14 : SS.bdot w9 z14 = true := by decide
theorem sg_ef1_w9_15 : SS.bdot w9 z15 = false := by decide
theorem ex_ef1_w9 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w9 = star (c y1) * d z0 - star (c y0) * d z1 - star (c y3) * d z2 + star (c y2) * d z3 + star (c y5) * d z4 - star (c y4) * d z5 - star (c y7) * d z6 + star (c y6) * d z7 + star (c y9) * d z8 - star (c y8) * d z9 - star (c y11) * d z10 + star (c y10) * d z11 + star (c y13) * d z12 - star (c y12) * d z13 - star (c y15) * d z14 + star (c y14) * d z15 := by
  unfold offSum
  rw [incidence_ef1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef1_0, flip_ef1_1, flip_ef1_2, flip_ef1_3, flip_ef1_4, flip_ef1_5, flip_ef1_6, flip_ef1_7, flip_ef1_8, flip_ef1_9, flip_ef1_10, flip_ef1_11, flip_ef1_12, flip_ef1_13, flip_ef1_14, flip_ef1_15]
  simp only [sg_ef1_w9_0, sg_ef1_w9_1, sg_ef1_w9_2, sg_ef1_w9_3, sg_ef1_w9_4, sg_ef1_w9_5, sg_ef1_w9_6, sg_ef1_w9_7, sg_ef1_w9_8, sg_ef1_w9_9, sg_ef1_w9_10, sg_ef1_w9_11, sg_ef1_w9_12, sg_ef1_w9_13, sg_ef1_w9_14, sg_ef1_w9_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

/-! ## The diagonal layer on the free qubit -/

def diagBot (c : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ x ∈ S0.filter (fun x => SS.bxor x e ∈ S0),
      SixQubit.signMul (SS.bdot z x) (star (c (SS.bxor x e)) * c x)

def diagTop (dd : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S1),
      SixQubit.signMul (SS.bdot z y) (star (dd (SS.bxor y e)) * dd y)

theorem dincB : S0.filter (fun x => SS.bxor x efZ ∈ S0) = {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15} := by decide
theorem dincT : S1.filter (fun y => SS.bxor y efZ ∈ S1) = {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15} := by decide
theorem dflipB_0 : SS.bxor y0 efZ = y8 := by decide
theorem dflipB_1 : SS.bxor y1 efZ = y9 := by decide
theorem dflipB_2 : SS.bxor y2 efZ = y10 := by decide
theorem dflipB_3 : SS.bxor y3 efZ = y11 := by decide
theorem dflipB_4 : SS.bxor y4 efZ = y12 := by decide
theorem dflipB_5 : SS.bxor y5 efZ = y13 := by decide
theorem dflipB_6 : SS.bxor y6 efZ = y14 := by decide
theorem dflipB_7 : SS.bxor y7 efZ = y15 := by decide
theorem dflipB_8 : SS.bxor y8 efZ = y0 := by decide
theorem dflipB_9 : SS.bxor y9 efZ = y1 := by decide
theorem dflipB_10 : SS.bxor y10 efZ = y2 := by decide
theorem dflipB_11 : SS.bxor y11 efZ = y3 := by decide
theorem dflipB_12 : SS.bxor y12 efZ = y4 := by decide
theorem dflipB_13 : SS.bxor y13 efZ = y5 := by decide
theorem dflipB_14 : SS.bxor y14 efZ = y6 := by decide
theorem dflipB_15 : SS.bxor y15 efZ = y7 := by decide
theorem dflipT_0 : SS.bxor z0 efZ = z8 := by decide
theorem dflipT_1 : SS.bxor z1 efZ = z9 := by decide
theorem dflipT_2 : SS.bxor z2 efZ = z10 := by decide
theorem dflipT_3 : SS.bxor z3 efZ = z11 := by decide
theorem dflipT_4 : SS.bxor z4 efZ = z12 := by decide
theorem dflipT_5 : SS.bxor z5 efZ = z13 := by decide
theorem dflipT_6 : SS.bxor z6 efZ = z14 := by decide
theorem dflipT_7 : SS.bxor z7 efZ = z15 := by decide
theorem dflipT_8 : SS.bxor z8 efZ = z0 := by decide
theorem dflipT_9 : SS.bxor z9 efZ = z1 := by decide
theorem dflipT_10 : SS.bxor z10 efZ = z2 := by decide
theorem dflipT_11 : SS.bxor z11 efZ = z3 := by decide
theorem dflipT_12 : SS.bxor z12 efZ = z4 := by decide
theorem dflipT_13 : SS.bxor z13 efZ = z5 := by decide
theorem dflipT_14 : SS.bxor z14 efZ = z6 := by decide
theorem dflipT_15 : SS.bxor z15 efZ = z7 := by decide

theorem dsB_w0_0 : SS.bdot w0 y0 = false := by decide
theorem dsB_w0_1 : SS.bdot w0 y1 = false := by decide
theorem dsB_w0_2 : SS.bdot w0 y2 = false := by decide
theorem dsB_w0_3 : SS.bdot w0 y3 = false := by decide
theorem dsB_w0_4 : SS.bdot w0 y4 = false := by decide
theorem dsB_w0_5 : SS.bdot w0 y5 = false := by decide
theorem dsB_w0_6 : SS.bdot w0 y6 = false := by decide
theorem dsB_w0_7 : SS.bdot w0 y7 = false := by decide
theorem dsB_w0_8 : SS.bdot w0 y8 = false := by decide
theorem dsB_w0_9 : SS.bdot w0 y9 = false := by decide
theorem dsB_w0_10 : SS.bdot w0 y10 = false := by decide
theorem dsB_w0_11 : SS.bdot w0 y11 = false := by decide
theorem dsB_w0_12 : SS.bdot w0 y12 = false := by decide
theorem dsB_w0_13 : SS.bdot w0 y13 = false := by decide
theorem dsB_w0_14 : SS.bdot w0 y14 = false := by decide
theorem dsB_w0_15 : SS.bdot w0 y15 = false := by decide
theorem dsT_w0_0 : SS.bdot w0 z0 = false := by decide
theorem dsT_w0_1 : SS.bdot w0 z1 = false := by decide
theorem dsT_w0_2 : SS.bdot w0 z2 = false := by decide
theorem dsT_w0_3 : SS.bdot w0 z3 = false := by decide
theorem dsT_w0_4 : SS.bdot w0 z4 = false := by decide
theorem dsT_w0_5 : SS.bdot w0 z5 = false := by decide
theorem dsT_w0_6 : SS.bdot w0 z6 = false := by decide
theorem dsT_w0_7 : SS.bdot w0 z7 = false := by decide
theorem dsT_w0_8 : SS.bdot w0 z8 = false := by decide
theorem dsT_w0_9 : SS.bdot w0 z9 = false := by decide
theorem dsT_w0_10 : SS.bdot w0 z10 = false := by decide
theorem dsT_w0_11 : SS.bdot w0 z11 = false := by decide
theorem dsT_w0_12 : SS.bdot w0 z12 = false := by decide
theorem dsT_w0_13 : SS.bdot w0 z13 = false := by decide
theorem dsT_w0_14 : SS.bdot w0 z14 = false := by decide
theorem dsT_w0_15 : SS.bdot w0 z15 = false := by decide
theorem dexB_w0 (c : SS.BitString 6 -> ℂ) :
    diagBot c efZ w0 = star (c y8) * c y0 + star (c y9) * c y1 + star (c y10) * c y2 + star (c y11) * c y3 + star (c y12) * c y4 + star (c y13) * c y5 + star (c y14) * c y6 + star (c y15) * c y7 + star (c y0) * c y8 + star (c y1) * c y9 + star (c y2) * c y10 + star (c y3) * c y11 + star (c y4) * c y12 + star (c y5) * c y13 + star (c y6) * c y14 + star (c y7) * c y15 := by
  unfold diagBot
  rw [dincB]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipB_0, dflipB_1, dflipB_2, dflipB_3, dflipB_4, dflipB_5, dflipB_6, dflipB_7, dflipB_8, dflipB_9, dflipB_10, dflipB_11, dflipB_12, dflipB_13, dflipB_14, dflipB_15]
  simp only [dsB_w0_0, dsB_w0_1, dsB_w0_2, dsB_w0_3, dsB_w0_4, dsB_w0_5, dsB_w0_6, dsB_w0_7, dsB_w0_8, dsB_w0_9, dsB_w0_10, dsB_w0_11, dsB_w0_12, dsB_w0_13, dsB_w0_14, dsB_w0_15, SixQubit.signMul_false]
  try ring
theorem dexT_w0 (dd : SS.BitString 6 -> ℂ) :
    diagTop dd efZ w0 = star (dd z8) * dd z0 + star (dd z9) * dd z1 + star (dd z10) * dd z2 + star (dd z11) * dd z3 + star (dd z12) * dd z4 + star (dd z13) * dd z5 + star (dd z14) * dd z6 + star (dd z15) * dd z7 + star (dd z0) * dd z8 + star (dd z1) * dd z9 + star (dd z2) * dd z10 + star (dd z3) * dd z11 + star (dd z4) * dd z12 + star (dd z5) * dd z13 + star (dd z6) * dd z14 + star (dd z7) * dd z15 := by
  unfold diagTop
  rw [dincT]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipT_0, dflipT_1, dflipT_2, dflipT_3, dflipT_4, dflipT_5, dflipT_6, dflipT_7, dflipT_8, dflipT_9, dflipT_10, dflipT_11, dflipT_12, dflipT_13, dflipT_14, dflipT_15]
  simp only [dsT_w0_0, dsT_w0_1, dsT_w0_2, dsT_w0_3, dsT_w0_4, dsT_w0_5, dsT_w0_6, dsT_w0_7, dsT_w0_8, dsT_w0_9, dsT_w0_10, dsT_w0_11, dsT_w0_12, dsT_w0_13, dsT_w0_14, dsT_w0_15, SixQubit.signMul_false]
  try ring

theorem dsB_w1_0 : SS.bdot w1 y0 = false := by decide
theorem dsB_w1_1 : SS.bdot w1 y1 = true := by decide
theorem dsB_w1_2 : SS.bdot w1 y2 = true := by decide
theorem dsB_w1_3 : SS.bdot w1 y3 = false := by decide
theorem dsB_w1_4 : SS.bdot w1 y4 = true := by decide
theorem dsB_w1_5 : SS.bdot w1 y5 = false := by decide
theorem dsB_w1_6 : SS.bdot w1 y6 = true := by decide
theorem dsB_w1_7 : SS.bdot w1 y7 = false := by decide
theorem dsB_w1_8 : SS.bdot w1 y8 = false := by decide
theorem dsB_w1_9 : SS.bdot w1 y9 = true := by decide
theorem dsB_w1_10 : SS.bdot w1 y10 = true := by decide
theorem dsB_w1_11 : SS.bdot w1 y11 = false := by decide
theorem dsB_w1_12 : SS.bdot w1 y12 = true := by decide
theorem dsB_w1_13 : SS.bdot w1 y13 = false := by decide
theorem dsB_w1_14 : SS.bdot w1 y14 = true := by decide
theorem dsB_w1_15 : SS.bdot w1 y15 = false := by decide
theorem dsT_w1_0 : SS.bdot w1 z0 = true := by decide
theorem dsT_w1_1 : SS.bdot w1 z1 = false := by decide
theorem dsT_w1_2 : SS.bdot w1 z2 = false := by decide
theorem dsT_w1_3 : SS.bdot w1 z3 = true := by decide
theorem dsT_w1_4 : SS.bdot w1 z4 = false := by decide
theorem dsT_w1_5 : SS.bdot w1 z5 = true := by decide
theorem dsT_w1_6 : SS.bdot w1 z6 = false := by decide
theorem dsT_w1_7 : SS.bdot w1 z7 = true := by decide
theorem dsT_w1_8 : SS.bdot w1 z8 = true := by decide
theorem dsT_w1_9 : SS.bdot w1 z9 = false := by decide
theorem dsT_w1_10 : SS.bdot w1 z10 = false := by decide
theorem dsT_w1_11 : SS.bdot w1 z11 = true := by decide
theorem dsT_w1_12 : SS.bdot w1 z12 = false := by decide
theorem dsT_w1_13 : SS.bdot w1 z13 = true := by decide
theorem dsT_w1_14 : SS.bdot w1 z14 = false := by decide
theorem dsT_w1_15 : SS.bdot w1 z15 = true := by decide
theorem dexB_w1 (c : SS.BitString 6 -> ℂ) :
    diagBot c efZ w1 = star (c y8) * c y0 - star (c y9) * c y1 - star (c y10) * c y2 + star (c y11) * c y3 - star (c y12) * c y4 + star (c y13) * c y5 - star (c y14) * c y6 + star (c y15) * c y7 + star (c y0) * c y8 - star (c y1) * c y9 - star (c y2) * c y10 + star (c y3) * c y11 - star (c y4) * c y12 + star (c y5) * c y13 - star (c y6) * c y14 + star (c y7) * c y15 := by
  unfold diagBot
  rw [dincB]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipB_0, dflipB_1, dflipB_2, dflipB_3, dflipB_4, dflipB_5, dflipB_6, dflipB_7, dflipB_8, dflipB_9, dflipB_10, dflipB_11, dflipB_12, dflipB_13, dflipB_14, dflipB_15]
  simp only [dsB_w1_0, dsB_w1_1, dsB_w1_2, dsB_w1_3, dsB_w1_4, dsB_w1_5, dsB_w1_6, dsB_w1_7, dsB_w1_8, dsB_w1_9, dsB_w1_10, dsB_w1_11, dsB_w1_12, dsB_w1_13, dsB_w1_14, dsB_w1_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem dexT_w1 (dd : SS.BitString 6 -> ℂ) :
    diagTop dd efZ w1 = - star (dd z8) * dd z0 + star (dd z9) * dd z1 + star (dd z10) * dd z2 - star (dd z11) * dd z3 + star (dd z12) * dd z4 - star (dd z13) * dd z5 + star (dd z14) * dd z6 - star (dd z15) * dd z7 - star (dd z0) * dd z8 + star (dd z1) * dd z9 + star (dd z2) * dd z10 - star (dd z3) * dd z11 + star (dd z4) * dd z12 - star (dd z5) * dd z13 + star (dd z6) * dd z14 - star (dd z7) * dd z15 := by
  unfold diagTop
  rw [dincT]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipT_0, dflipT_1, dflipT_2, dflipT_3, dflipT_4, dflipT_5, dflipT_6, dflipT_7, dflipT_8, dflipT_9, dflipT_10, dflipT_11, dflipT_12, dflipT_13, dflipT_14, dflipT_15]
  simp only [dsT_w1_0, dsT_w1_1, dsT_w1_2, dsT_w1_3, dsT_w1_4, dsT_w1_5, dsT_w1_6, dsT_w1_7, dsT_w1_8, dsT_w1_9, dsT_w1_10, dsT_w1_11, dsT_w1_12, dsT_w1_13, dsT_w1_14, dsT_w1_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dsB_w2_0 : SS.bdot w2 y0 = false := by decide
theorem dsB_w2_1 : SS.bdot w2 y1 = true := by decide
theorem dsB_w2_2 : SS.bdot w2 y2 = false := by decide
theorem dsB_w2_3 : SS.bdot w2 y3 = true := by decide
theorem dsB_w2_4 : SS.bdot w2 y4 = false := by decide
theorem dsB_w2_5 : SS.bdot w2 y5 = true := by decide
theorem dsB_w2_6 : SS.bdot w2 y6 = false := by decide
theorem dsB_w2_7 : SS.bdot w2 y7 = true := by decide
theorem dsB_w2_8 : SS.bdot w2 y8 = false := by decide
theorem dsB_w2_9 : SS.bdot w2 y9 = true := by decide
theorem dsB_w2_10 : SS.bdot w2 y10 = false := by decide
theorem dsB_w2_11 : SS.bdot w2 y11 = true := by decide
theorem dsB_w2_12 : SS.bdot w2 y12 = false := by decide
theorem dsB_w2_13 : SS.bdot w2 y13 = true := by decide
theorem dsB_w2_14 : SS.bdot w2 y14 = false := by decide
theorem dsB_w2_15 : SS.bdot w2 y15 = true := by decide
theorem dsT_w2_0 : SS.bdot w2 z0 = false := by decide
theorem dsT_w2_1 : SS.bdot w2 z1 = true := by decide
theorem dsT_w2_2 : SS.bdot w2 z2 = false := by decide
theorem dsT_w2_3 : SS.bdot w2 z3 = true := by decide
theorem dsT_w2_4 : SS.bdot w2 z4 = false := by decide
theorem dsT_w2_5 : SS.bdot w2 z5 = true := by decide
theorem dsT_w2_6 : SS.bdot w2 z6 = false := by decide
theorem dsT_w2_7 : SS.bdot w2 z7 = true := by decide
theorem dsT_w2_8 : SS.bdot w2 z8 = false := by decide
theorem dsT_w2_9 : SS.bdot w2 z9 = true := by decide
theorem dsT_w2_10 : SS.bdot w2 z10 = false := by decide
theorem dsT_w2_11 : SS.bdot w2 z11 = true := by decide
theorem dsT_w2_12 : SS.bdot w2 z12 = false := by decide
theorem dsT_w2_13 : SS.bdot w2 z13 = true := by decide
theorem dsT_w2_14 : SS.bdot w2 z14 = false := by decide
theorem dsT_w2_15 : SS.bdot w2 z15 = true := by decide
theorem dexB_w2 (c : SS.BitString 6 -> ℂ) :
    diagBot c efZ w2 = star (c y8) * c y0 - star (c y9) * c y1 + star (c y10) * c y2 - star (c y11) * c y3 + star (c y12) * c y4 - star (c y13) * c y5 + star (c y14) * c y6 - star (c y15) * c y7 + star (c y0) * c y8 - star (c y1) * c y9 + star (c y2) * c y10 - star (c y3) * c y11 + star (c y4) * c y12 - star (c y5) * c y13 + star (c y6) * c y14 - star (c y7) * c y15 := by
  unfold diagBot
  rw [dincB]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipB_0, dflipB_1, dflipB_2, dflipB_3, dflipB_4, dflipB_5, dflipB_6, dflipB_7, dflipB_8, dflipB_9, dflipB_10, dflipB_11, dflipB_12, dflipB_13, dflipB_14, dflipB_15]
  simp only [dsB_w2_0, dsB_w2_1, dsB_w2_2, dsB_w2_3, dsB_w2_4, dsB_w2_5, dsB_w2_6, dsB_w2_7, dsB_w2_8, dsB_w2_9, dsB_w2_10, dsB_w2_11, dsB_w2_12, dsB_w2_13, dsB_w2_14, dsB_w2_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem dexT_w2 (dd : SS.BitString 6 -> ℂ) :
    diagTop dd efZ w2 = star (dd z8) * dd z0 - star (dd z9) * dd z1 + star (dd z10) * dd z2 - star (dd z11) * dd z3 + star (dd z12) * dd z4 - star (dd z13) * dd z5 + star (dd z14) * dd z6 - star (dd z15) * dd z7 + star (dd z0) * dd z8 - star (dd z1) * dd z9 + star (dd z2) * dd z10 - star (dd z3) * dd z11 + star (dd z4) * dd z12 - star (dd z5) * dd z13 + star (dd z6) * dd z14 - star (dd z7) * dd z15 := by
  unfold diagTop
  rw [dincT]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipT_0, dflipT_1, dflipT_2, dflipT_3, dflipT_4, dflipT_5, dflipT_6, dflipT_7, dflipT_8, dflipT_9, dflipT_10, dflipT_11, dflipT_12, dflipT_13, dflipT_14, dflipT_15]
  simp only [dsT_w2_0, dsT_w2_1, dsT_w2_2, dsT_w2_3, dsT_w2_4, dsT_w2_5, dsT_w2_6, dsT_w2_7, dsT_w2_8, dsT_w2_9, dsT_w2_10, dsT_w2_11, dsT_w2_12, dsT_w2_13, dsT_w2_14, dsT_w2_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dsB_w4_0 : SS.bdot w4 y0 = false := by decide
theorem dsB_w4_1 : SS.bdot w4 y1 = false := by decide
theorem dsB_w4_2 : SS.bdot w4 y2 = true := by decide
theorem dsB_w4_3 : SS.bdot w4 y3 = true := by decide
theorem dsB_w4_4 : SS.bdot w4 y4 = true := by decide
theorem dsB_w4_5 : SS.bdot w4 y5 = true := by decide
theorem dsB_w4_6 : SS.bdot w4 y6 = false := by decide
theorem dsB_w4_7 : SS.bdot w4 y7 = false := by decide
theorem dsB_w4_8 : SS.bdot w4 y8 = false := by decide
theorem dsB_w4_9 : SS.bdot w4 y9 = false := by decide
theorem dsB_w4_10 : SS.bdot w4 y10 = true := by decide
theorem dsB_w4_11 : SS.bdot w4 y11 = true := by decide
theorem dsB_w4_12 : SS.bdot w4 y12 = true := by decide
theorem dsB_w4_13 : SS.bdot w4 y13 = true := by decide
theorem dsB_w4_14 : SS.bdot w4 y14 = false := by decide
theorem dsB_w4_15 : SS.bdot w4 y15 = false := by decide
theorem dsT_w4_0 : SS.bdot w4 z0 = false := by decide
theorem dsT_w4_1 : SS.bdot w4 z1 = false := by decide
theorem dsT_w4_2 : SS.bdot w4 z2 = true := by decide
theorem dsT_w4_3 : SS.bdot w4 z3 = true := by decide
theorem dsT_w4_4 : SS.bdot w4 z4 = true := by decide
theorem dsT_w4_5 : SS.bdot w4 z5 = true := by decide
theorem dsT_w4_6 : SS.bdot w4 z6 = false := by decide
theorem dsT_w4_7 : SS.bdot w4 z7 = false := by decide
theorem dsT_w4_8 : SS.bdot w4 z8 = false := by decide
theorem dsT_w4_9 : SS.bdot w4 z9 = false := by decide
theorem dsT_w4_10 : SS.bdot w4 z10 = true := by decide
theorem dsT_w4_11 : SS.bdot w4 z11 = true := by decide
theorem dsT_w4_12 : SS.bdot w4 z12 = true := by decide
theorem dsT_w4_13 : SS.bdot w4 z13 = true := by decide
theorem dsT_w4_14 : SS.bdot w4 z14 = false := by decide
theorem dsT_w4_15 : SS.bdot w4 z15 = false := by decide
theorem dexB_w4 (c : SS.BitString 6 -> ℂ) :
    diagBot c efZ w4 = star (c y8) * c y0 + star (c y9) * c y1 - star (c y10) * c y2 - star (c y11) * c y3 - star (c y12) * c y4 - star (c y13) * c y5 + star (c y14) * c y6 + star (c y15) * c y7 + star (c y0) * c y8 + star (c y1) * c y9 - star (c y2) * c y10 - star (c y3) * c y11 - star (c y4) * c y12 - star (c y5) * c y13 + star (c y6) * c y14 + star (c y7) * c y15 := by
  unfold diagBot
  rw [dincB]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipB_0, dflipB_1, dflipB_2, dflipB_3, dflipB_4, dflipB_5, dflipB_6, dflipB_7, dflipB_8, dflipB_9, dflipB_10, dflipB_11, dflipB_12, dflipB_13, dflipB_14, dflipB_15]
  simp only [dsB_w4_0, dsB_w4_1, dsB_w4_2, dsB_w4_3, dsB_w4_4, dsB_w4_5, dsB_w4_6, dsB_w4_7, dsB_w4_8, dsB_w4_9, dsB_w4_10, dsB_w4_11, dsB_w4_12, dsB_w4_13, dsB_w4_14, dsB_w4_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem dexT_w4 (dd : SS.BitString 6 -> ℂ) :
    diagTop dd efZ w4 = star (dd z8) * dd z0 + star (dd z9) * dd z1 - star (dd z10) * dd z2 - star (dd z11) * dd z3 - star (dd z12) * dd z4 - star (dd z13) * dd z5 + star (dd z14) * dd z6 + star (dd z15) * dd z7 + star (dd z0) * dd z8 + star (dd z1) * dd z9 - star (dd z2) * dd z10 - star (dd z3) * dd z11 - star (dd z4) * dd z12 - star (dd z5) * dd z13 + star (dd z6) * dd z14 + star (dd z7) * dd z15 := by
  unfold diagTop
  rw [dincT]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipT_0, dflipT_1, dflipT_2, dflipT_3, dflipT_4, dflipT_5, dflipT_6, dflipT_7, dflipT_8, dflipT_9, dflipT_10, dflipT_11, dflipT_12, dflipT_13, dflipT_14, dflipT_15]
  simp only [dsT_w4_0, dsT_w4_1, dsT_w4_2, dsT_w4_3, dsT_w4_4, dsT_w4_5, dsT_w4_6, dsT_w4_7, dsT_w4_8, dsT_w4_9, dsT_w4_10, dsT_w4_11, dsT_w4_12, dsT_w4_13, dsT_w4_14, dsT_w4_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dsB_w7_0 : SS.bdot w7 y0 = false := by decide
theorem dsB_w7_1 : SS.bdot w7 y1 = false := by decide
theorem dsB_w7_2 : SS.bdot w7 y2 = true := by decide
theorem dsB_w7_3 : SS.bdot w7 y3 = true := by decide
theorem dsB_w7_4 : SS.bdot w7 y4 = false := by decide
theorem dsB_w7_5 : SS.bdot w7 y5 = false := by decide
theorem dsB_w7_6 : SS.bdot w7 y6 = true := by decide
theorem dsB_w7_7 : SS.bdot w7 y7 = true := by decide
theorem dsB_w7_8 : SS.bdot w7 y8 = false := by decide
theorem dsB_w7_9 : SS.bdot w7 y9 = false := by decide
theorem dsB_w7_10 : SS.bdot w7 y10 = true := by decide
theorem dsB_w7_11 : SS.bdot w7 y11 = true := by decide
theorem dsB_w7_12 : SS.bdot w7 y12 = false := by decide
theorem dsB_w7_13 : SS.bdot w7 y13 = false := by decide
theorem dsB_w7_14 : SS.bdot w7 y14 = true := by decide
theorem dsB_w7_15 : SS.bdot w7 y15 = true := by decide
theorem dsT_w7_0 : SS.bdot w7 z0 = false := by decide
theorem dsT_w7_1 : SS.bdot w7 z1 = false := by decide
theorem dsT_w7_2 : SS.bdot w7 z2 = true := by decide
theorem dsT_w7_3 : SS.bdot w7 z3 = true := by decide
theorem dsT_w7_4 : SS.bdot w7 z4 = false := by decide
theorem dsT_w7_5 : SS.bdot w7 z5 = false := by decide
theorem dsT_w7_6 : SS.bdot w7 z6 = true := by decide
theorem dsT_w7_7 : SS.bdot w7 z7 = true := by decide
theorem dsT_w7_8 : SS.bdot w7 z8 = false := by decide
theorem dsT_w7_9 : SS.bdot w7 z9 = false := by decide
theorem dsT_w7_10 : SS.bdot w7 z10 = true := by decide
theorem dsT_w7_11 : SS.bdot w7 z11 = true := by decide
theorem dsT_w7_12 : SS.bdot w7 z12 = false := by decide
theorem dsT_w7_13 : SS.bdot w7 z13 = false := by decide
theorem dsT_w7_14 : SS.bdot w7 z14 = true := by decide
theorem dsT_w7_15 : SS.bdot w7 z15 = true := by decide
theorem dexB_w7 (c : SS.BitString 6 -> ℂ) :
    diagBot c efZ w7 = star (c y8) * c y0 + star (c y9) * c y1 - star (c y10) * c y2 - star (c y11) * c y3 + star (c y12) * c y4 + star (c y13) * c y5 - star (c y14) * c y6 - star (c y15) * c y7 + star (c y0) * c y8 + star (c y1) * c y9 - star (c y2) * c y10 - star (c y3) * c y11 + star (c y4) * c y12 + star (c y5) * c y13 - star (c y6) * c y14 - star (c y7) * c y15 := by
  unfold diagBot
  rw [dincB]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipB_0, dflipB_1, dflipB_2, dflipB_3, dflipB_4, dflipB_5, dflipB_6, dflipB_7, dflipB_8, dflipB_9, dflipB_10, dflipB_11, dflipB_12, dflipB_13, dflipB_14, dflipB_15]
  simp only [dsB_w7_0, dsB_w7_1, dsB_w7_2, dsB_w7_3, dsB_w7_4, dsB_w7_5, dsB_w7_6, dsB_w7_7, dsB_w7_8, dsB_w7_9, dsB_w7_10, dsB_w7_11, dsB_w7_12, dsB_w7_13, dsB_w7_14, dsB_w7_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem dexT_w7 (dd : SS.BitString 6 -> ℂ) :
    diagTop dd efZ w7 = star (dd z8) * dd z0 + star (dd z9) * dd z1 - star (dd z10) * dd z2 - star (dd z11) * dd z3 + star (dd z12) * dd z4 + star (dd z13) * dd z5 - star (dd z14) * dd z6 - star (dd z15) * dd z7 + star (dd z0) * dd z8 + star (dd z1) * dd z9 - star (dd z2) * dd z10 - star (dd z3) * dd z11 + star (dd z4) * dd z12 + star (dd z5) * dd z13 - star (dd z6) * dd z14 - star (dd z7) * dd z15 := by
  unfold diagTop
  rw [dincT]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipT_0, dflipT_1, dflipT_2, dflipT_3, dflipT_4, dflipT_5, dflipT_6, dflipT_7, dflipT_8, dflipT_9, dflipT_10, dflipT_11, dflipT_12, dflipT_13, dflipT_14, dflipT_15]
  simp only [dsT_w7_0, dsT_w7_1, dsT_w7_2, dsT_w7_3, dsT_w7_4, dsT_w7_5, dsT_w7_6, dsT_w7_7, dsT_w7_8, dsT_w7_9, dsT_w7_10, dsT_w7_11, dsT_w7_12, dsT_w7_13, dsT_w7_14, dsT_w7_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dsB_w10_0 : SS.bdot w10 y0 = false := by decide
theorem dsB_w10_1 : SS.bdot w10 y1 = false := by decide
theorem dsB_w10_2 : SS.bdot w10 y2 = false := by decide
theorem dsB_w10_3 : SS.bdot w10 y3 = false := by decide
theorem dsB_w10_4 : SS.bdot w10 y4 = true := by decide
theorem dsB_w10_5 : SS.bdot w10 y5 = true := by decide
theorem dsB_w10_6 : SS.bdot w10 y6 = true := by decide
theorem dsB_w10_7 : SS.bdot w10 y7 = true := by decide
theorem dsB_w10_8 : SS.bdot w10 y8 = false := by decide
theorem dsB_w10_9 : SS.bdot w10 y9 = false := by decide
theorem dsB_w10_10 : SS.bdot w10 y10 = false := by decide
theorem dsB_w10_11 : SS.bdot w10 y11 = false := by decide
theorem dsB_w10_12 : SS.bdot w10 y12 = true := by decide
theorem dsB_w10_13 : SS.bdot w10 y13 = true := by decide
theorem dsB_w10_14 : SS.bdot w10 y14 = true := by decide
theorem dsB_w10_15 : SS.bdot w10 y15 = true := by decide
theorem dsT_w10_0 : SS.bdot w10 z0 = false := by decide
theorem dsT_w10_1 : SS.bdot w10 z1 = false := by decide
theorem dsT_w10_2 : SS.bdot w10 z2 = false := by decide
theorem dsT_w10_3 : SS.bdot w10 z3 = false := by decide
theorem dsT_w10_4 : SS.bdot w10 z4 = true := by decide
theorem dsT_w10_5 : SS.bdot w10 z5 = true := by decide
theorem dsT_w10_6 : SS.bdot w10 z6 = true := by decide
theorem dsT_w10_7 : SS.bdot w10 z7 = true := by decide
theorem dsT_w10_8 : SS.bdot w10 z8 = false := by decide
theorem dsT_w10_9 : SS.bdot w10 z9 = false := by decide
theorem dsT_w10_10 : SS.bdot w10 z10 = false := by decide
theorem dsT_w10_11 : SS.bdot w10 z11 = false := by decide
theorem dsT_w10_12 : SS.bdot w10 z12 = true := by decide
theorem dsT_w10_13 : SS.bdot w10 z13 = true := by decide
theorem dsT_w10_14 : SS.bdot w10 z14 = true := by decide
theorem dsT_w10_15 : SS.bdot w10 z15 = true := by decide
theorem dexB_w10 (c : SS.BitString 6 -> ℂ) :
    diagBot c efZ w10 = star (c y8) * c y0 + star (c y9) * c y1 + star (c y10) * c y2 + star (c y11) * c y3 - star (c y12) * c y4 - star (c y13) * c y5 - star (c y14) * c y6 - star (c y15) * c y7 + star (c y0) * c y8 + star (c y1) * c y9 + star (c y2) * c y10 + star (c y3) * c y11 - star (c y4) * c y12 - star (c y5) * c y13 - star (c y6) * c y14 - star (c y7) * c y15 := by
  unfold diagBot
  rw [dincB]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipB_0, dflipB_1, dflipB_2, dflipB_3, dflipB_4, dflipB_5, dflipB_6, dflipB_7, dflipB_8, dflipB_9, dflipB_10, dflipB_11, dflipB_12, dflipB_13, dflipB_14, dflipB_15]
  simp only [dsB_w10_0, dsB_w10_1, dsB_w10_2, dsB_w10_3, dsB_w10_4, dsB_w10_5, dsB_w10_6, dsB_w10_7, dsB_w10_8, dsB_w10_9, dsB_w10_10, dsB_w10_11, dsB_w10_12, dsB_w10_13, dsB_w10_14, dsB_w10_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem dexT_w10 (dd : SS.BitString 6 -> ℂ) :
    diagTop dd efZ w10 = star (dd z8) * dd z0 + star (dd z9) * dd z1 + star (dd z10) * dd z2 + star (dd z11) * dd z3 - star (dd z12) * dd z4 - star (dd z13) * dd z5 - star (dd z14) * dd z6 - star (dd z15) * dd z7 + star (dd z0) * dd z8 + star (dd z1) * dd z9 + star (dd z2) * dd z10 + star (dd z3) * dd z11 - star (dd z4) * dd z12 - star (dd z5) * dd z13 - star (dd z6) * dd z14 - star (dd z7) * dd z15 := by
  unfold diagTop
  rw [dincT]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipT_0, dflipT_1, dflipT_2, dflipT_3, dflipT_4, dflipT_5, dflipT_6, dflipT_7, dflipT_8, dflipT_9, dflipT_10, dflipT_11, dflipT_12, dflipT_13, dflipT_14, dflipT_15]
  simp only [dsT_w10_0, dsT_w10_1, dsT_w10_2, dsT_w10_3, dsT_w10_4, dsT_w10_5, dsT_w10_6, dsT_w10_7, dsT_w10_8, dsT_w10_9, dsT_w10_10, dsT_w10_11, dsT_w10_12, dsT_w10_13, dsT_w10_14, dsT_w10_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dsB_w11_0 : SS.bdot w11 y0 = false := by decide
theorem dsB_w11_1 : SS.bdot w11 y1 = false := by decide
theorem dsB_w11_2 : SS.bdot w11 y2 = false := by decide
theorem dsB_w11_3 : SS.bdot w11 y3 = false := by decide
theorem dsB_w11_4 : SS.bdot w11 y4 = false := by decide
theorem dsB_w11_5 : SS.bdot w11 y5 = false := by decide
theorem dsB_w11_6 : SS.bdot w11 y6 = false := by decide
theorem dsB_w11_7 : SS.bdot w11 y7 = false := by decide
theorem dsB_w11_8 : SS.bdot w11 y8 = true := by decide
theorem dsB_w11_9 : SS.bdot w11 y9 = true := by decide
theorem dsB_w11_10 : SS.bdot w11 y10 = true := by decide
theorem dsB_w11_11 : SS.bdot w11 y11 = true := by decide
theorem dsB_w11_12 : SS.bdot w11 y12 = true := by decide
theorem dsB_w11_13 : SS.bdot w11 y13 = true := by decide
theorem dsB_w11_14 : SS.bdot w11 y14 = true := by decide
theorem dsB_w11_15 : SS.bdot w11 y15 = true := by decide
theorem dsT_w11_0 : SS.bdot w11 z0 = false := by decide
theorem dsT_w11_1 : SS.bdot w11 z1 = false := by decide
theorem dsT_w11_2 : SS.bdot w11 z2 = false := by decide
theorem dsT_w11_3 : SS.bdot w11 z3 = false := by decide
theorem dsT_w11_4 : SS.bdot w11 z4 = false := by decide
theorem dsT_w11_5 : SS.bdot w11 z5 = false := by decide
theorem dsT_w11_6 : SS.bdot w11 z6 = false := by decide
theorem dsT_w11_7 : SS.bdot w11 z7 = false := by decide
theorem dsT_w11_8 : SS.bdot w11 z8 = true := by decide
theorem dsT_w11_9 : SS.bdot w11 z9 = true := by decide
theorem dsT_w11_10 : SS.bdot w11 z10 = true := by decide
theorem dsT_w11_11 : SS.bdot w11 z11 = true := by decide
theorem dsT_w11_12 : SS.bdot w11 z12 = true := by decide
theorem dsT_w11_13 : SS.bdot w11 z13 = true := by decide
theorem dsT_w11_14 : SS.bdot w11 z14 = true := by decide
theorem dsT_w11_15 : SS.bdot w11 z15 = true := by decide
theorem dexB_w11 (c : SS.BitString 6 -> ℂ) :
    diagBot c efZ w11 = star (c y8) * c y0 + star (c y9) * c y1 + star (c y10) * c y2 + star (c y11) * c y3 + star (c y12) * c y4 + star (c y13) * c y5 + star (c y14) * c y6 + star (c y15) * c y7 - star (c y0) * c y8 - star (c y1) * c y9 - star (c y2) * c y10 - star (c y3) * c y11 - star (c y4) * c y12 - star (c y5) * c y13 - star (c y6) * c y14 - star (c y7) * c y15 := by
  unfold diagBot
  rw [dincB]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipB_0, dflipB_1, dflipB_2, dflipB_3, dflipB_4, dflipB_5, dflipB_6, dflipB_7, dflipB_8, dflipB_9, dflipB_10, dflipB_11, dflipB_12, dflipB_13, dflipB_14, dflipB_15]
  simp only [dsB_w11_0, dsB_w11_1, dsB_w11_2, dsB_w11_3, dsB_w11_4, dsB_w11_5, dsB_w11_6, dsB_w11_7, dsB_w11_8, dsB_w11_9, dsB_w11_10, dsB_w11_11, dsB_w11_12, dsB_w11_13, dsB_w11_14, dsB_w11_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem dexT_w11 (dd : SS.BitString 6 -> ℂ) :
    diagTop dd efZ w11 = star (dd z8) * dd z0 + star (dd z9) * dd z1 + star (dd z10) * dd z2 + star (dd z11) * dd z3 + star (dd z12) * dd z4 + star (dd z13) * dd z5 + star (dd z14) * dd z6 + star (dd z15) * dd z7 - star (dd z0) * dd z8 - star (dd z1) * dd z9 - star (dd z2) * dd z10 - star (dd z3) * dd z11 - star (dd z4) * dd z12 - star (dd z5) * dd z13 - star (dd z6) * dd z14 - star (dd z7) * dd z15 := by
  unfold diagTop
  rw [dincT]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipT_0, dflipT_1, dflipT_2, dflipT_3, dflipT_4, dflipT_5, dflipT_6, dflipT_7, dflipT_8, dflipT_9, dflipT_10, dflipT_11, dflipT_12, dflipT_13, dflipT_14, dflipT_15]
  simp only [dsT_w11_0, dsT_w11_1, dsT_w11_2, dsT_w11_3, dsT_w11_4, dsT_w11_5, dsT_w11_6, dsT_w11_7, dsT_w11_8, dsT_w11_9, dsT_w11_10, dsT_w11_11, dsT_w11_12, dsT_w11_13, dsT_w11_14, dsT_w11_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dsB_w12_0 : SS.bdot w12 y0 = false := by decide
theorem dsB_w12_1 : SS.bdot w12 y1 = true := by decide
theorem dsB_w12_2 : SS.bdot w12 y2 = true := by decide
theorem dsB_w12_3 : SS.bdot w12 y3 = false := by decide
theorem dsB_w12_4 : SS.bdot w12 y4 = true := by decide
theorem dsB_w12_5 : SS.bdot w12 y5 = false := by decide
theorem dsB_w12_6 : SS.bdot w12 y6 = true := by decide
theorem dsB_w12_7 : SS.bdot w12 y7 = false := by decide
theorem dsB_w12_8 : SS.bdot w12 y8 = true := by decide
theorem dsB_w12_9 : SS.bdot w12 y9 = false := by decide
theorem dsB_w12_10 : SS.bdot w12 y10 = false := by decide
theorem dsB_w12_11 : SS.bdot w12 y11 = true := by decide
theorem dsB_w12_12 : SS.bdot w12 y12 = false := by decide
theorem dsB_w12_13 : SS.bdot w12 y13 = true := by decide
theorem dsB_w12_14 : SS.bdot w12 y14 = false := by decide
theorem dsB_w12_15 : SS.bdot w12 y15 = true := by decide
theorem dsT_w12_0 : SS.bdot w12 z0 = true := by decide
theorem dsT_w12_1 : SS.bdot w12 z1 = false := by decide
theorem dsT_w12_2 : SS.bdot w12 z2 = false := by decide
theorem dsT_w12_3 : SS.bdot w12 z3 = true := by decide
theorem dsT_w12_4 : SS.bdot w12 z4 = false := by decide
theorem dsT_w12_5 : SS.bdot w12 z5 = true := by decide
theorem dsT_w12_6 : SS.bdot w12 z6 = false := by decide
theorem dsT_w12_7 : SS.bdot w12 z7 = true := by decide
theorem dsT_w12_8 : SS.bdot w12 z8 = false := by decide
theorem dsT_w12_9 : SS.bdot w12 z9 = true := by decide
theorem dsT_w12_10 : SS.bdot w12 z10 = true := by decide
theorem dsT_w12_11 : SS.bdot w12 z11 = false := by decide
theorem dsT_w12_12 : SS.bdot w12 z12 = true := by decide
theorem dsT_w12_13 : SS.bdot w12 z13 = false := by decide
theorem dsT_w12_14 : SS.bdot w12 z14 = true := by decide
theorem dsT_w12_15 : SS.bdot w12 z15 = false := by decide
theorem dexB_w12 (c : SS.BitString 6 -> ℂ) :
    diagBot c efZ w12 = star (c y8) * c y0 - star (c y9) * c y1 - star (c y10) * c y2 + star (c y11) * c y3 - star (c y12) * c y4 + star (c y13) * c y5 - star (c y14) * c y6 + star (c y15) * c y7 - star (c y0) * c y8 + star (c y1) * c y9 + star (c y2) * c y10 - star (c y3) * c y11 + star (c y4) * c y12 - star (c y5) * c y13 + star (c y6) * c y14 - star (c y7) * c y15 := by
  unfold diagBot
  rw [dincB]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipB_0, dflipB_1, dflipB_2, dflipB_3, dflipB_4, dflipB_5, dflipB_6, dflipB_7, dflipB_8, dflipB_9, dflipB_10, dflipB_11, dflipB_12, dflipB_13, dflipB_14, dflipB_15]
  simp only [dsB_w12_0, dsB_w12_1, dsB_w12_2, dsB_w12_3, dsB_w12_4, dsB_w12_5, dsB_w12_6, dsB_w12_7, dsB_w12_8, dsB_w12_9, dsB_w12_10, dsB_w12_11, dsB_w12_12, dsB_w12_13, dsB_w12_14, dsB_w12_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem dexT_w12 (dd : SS.BitString 6 -> ℂ) :
    diagTop dd efZ w12 = - star (dd z8) * dd z0 + star (dd z9) * dd z1 + star (dd z10) * dd z2 - star (dd z11) * dd z3 + star (dd z12) * dd z4 - star (dd z13) * dd z5 + star (dd z14) * dd z6 - star (dd z15) * dd z7 + star (dd z0) * dd z8 - star (dd z1) * dd z9 - star (dd z2) * dd z10 + star (dd z3) * dd z11 - star (dd z4) * dd z12 + star (dd z5) * dd z13 - star (dd z6) * dd z14 + star (dd z7) * dd z15 := by
  unfold diagTop
  rw [dincT]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipT_0, dflipT_1, dflipT_2, dflipT_3, dflipT_4, dflipT_5, dflipT_6, dflipT_7, dflipT_8, dflipT_9, dflipT_10, dflipT_11, dflipT_12, dflipT_13, dflipT_14, dflipT_15]
  simp only [dsT_w12_0, dsT_w12_1, dsT_w12_2, dsT_w12_3, dsT_w12_4, dsT_w12_5, dsT_w12_6, dsT_w12_7, dsT_w12_8, dsT_w12_9, dsT_w12_10, dsT_w12_11, dsT_w12_12, dsT_w12_13, dsT_w12_14, dsT_w12_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dsB_w13_0 : SS.bdot w13 y0 = false := by decide
theorem dsB_w13_1 : SS.bdot w13 y1 = true := by decide
theorem dsB_w13_2 : SS.bdot w13 y2 = false := by decide
theorem dsB_w13_3 : SS.bdot w13 y3 = true := by decide
theorem dsB_w13_4 : SS.bdot w13 y4 = false := by decide
theorem dsB_w13_5 : SS.bdot w13 y5 = true := by decide
theorem dsB_w13_6 : SS.bdot w13 y6 = false := by decide
theorem dsB_w13_7 : SS.bdot w13 y7 = true := by decide
theorem dsB_w13_8 : SS.bdot w13 y8 = true := by decide
theorem dsB_w13_9 : SS.bdot w13 y9 = false := by decide
theorem dsB_w13_10 : SS.bdot w13 y10 = true := by decide
theorem dsB_w13_11 : SS.bdot w13 y11 = false := by decide
theorem dsB_w13_12 : SS.bdot w13 y12 = true := by decide
theorem dsB_w13_13 : SS.bdot w13 y13 = false := by decide
theorem dsB_w13_14 : SS.bdot w13 y14 = true := by decide
theorem dsB_w13_15 : SS.bdot w13 y15 = false := by decide
theorem dsT_w13_0 : SS.bdot w13 z0 = false := by decide
theorem dsT_w13_1 : SS.bdot w13 z1 = true := by decide
theorem dsT_w13_2 : SS.bdot w13 z2 = false := by decide
theorem dsT_w13_3 : SS.bdot w13 z3 = true := by decide
theorem dsT_w13_4 : SS.bdot w13 z4 = false := by decide
theorem dsT_w13_5 : SS.bdot w13 z5 = true := by decide
theorem dsT_w13_6 : SS.bdot w13 z6 = false := by decide
theorem dsT_w13_7 : SS.bdot w13 z7 = true := by decide
theorem dsT_w13_8 : SS.bdot w13 z8 = true := by decide
theorem dsT_w13_9 : SS.bdot w13 z9 = false := by decide
theorem dsT_w13_10 : SS.bdot w13 z10 = true := by decide
theorem dsT_w13_11 : SS.bdot w13 z11 = false := by decide
theorem dsT_w13_12 : SS.bdot w13 z12 = true := by decide
theorem dsT_w13_13 : SS.bdot w13 z13 = false := by decide
theorem dsT_w13_14 : SS.bdot w13 z14 = true := by decide
theorem dsT_w13_15 : SS.bdot w13 z15 = false := by decide
theorem dexB_w13 (c : SS.BitString 6 -> ℂ) :
    diagBot c efZ w13 = star (c y8) * c y0 - star (c y9) * c y1 + star (c y10) * c y2 - star (c y11) * c y3 + star (c y12) * c y4 - star (c y13) * c y5 + star (c y14) * c y6 - star (c y15) * c y7 - star (c y0) * c y8 + star (c y1) * c y9 - star (c y2) * c y10 + star (c y3) * c y11 - star (c y4) * c y12 + star (c y5) * c y13 - star (c y6) * c y14 + star (c y7) * c y15 := by
  unfold diagBot
  rw [dincB]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipB_0, dflipB_1, dflipB_2, dflipB_3, dflipB_4, dflipB_5, dflipB_6, dflipB_7, dflipB_8, dflipB_9, dflipB_10, dflipB_11, dflipB_12, dflipB_13, dflipB_14, dflipB_15]
  simp only [dsB_w13_0, dsB_w13_1, dsB_w13_2, dsB_w13_3, dsB_w13_4, dsB_w13_5, dsB_w13_6, dsB_w13_7, dsB_w13_8, dsB_w13_9, dsB_w13_10, dsB_w13_11, dsB_w13_12, dsB_w13_13, dsB_w13_14, dsB_w13_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem dexT_w13 (dd : SS.BitString 6 -> ℂ) :
    diagTop dd efZ w13 = star (dd z8) * dd z0 - star (dd z9) * dd z1 + star (dd z10) * dd z2 - star (dd z11) * dd z3 + star (dd z12) * dd z4 - star (dd z13) * dd z5 + star (dd z14) * dd z6 - star (dd z15) * dd z7 - star (dd z0) * dd z8 + star (dd z1) * dd z9 - star (dd z2) * dd z10 + star (dd z3) * dd z11 - star (dd z4) * dd z12 + star (dd z5) * dd z13 - star (dd z6) * dd z14 + star (dd z7) * dd z15 := by
  unfold diagTop
  rw [dincT]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipT_0, dflipT_1, dflipT_2, dflipT_3, dflipT_4, dflipT_5, dflipT_6, dflipT_7, dflipT_8, dflipT_9, dflipT_10, dflipT_11, dflipT_12, dflipT_13, dflipT_14, dflipT_15]
  simp only [dsT_w13_0, dsT_w13_1, dsT_w13_2, dsT_w13_3, dsT_w13_4, dsT_w13_5, dsT_w13_6, dsT_w13_7, dsT_w13_8, dsT_w13_9, dsT_w13_10, dsT_w13_11, dsT_w13_12, dsT_w13_13, dsT_w13_14, dsT_w13_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dsB_w14_0 : SS.bdot w14 y0 = false := by decide
theorem dsB_w14_1 : SS.bdot w14 y1 = false := by decide
theorem dsB_w14_2 : SS.bdot w14 y2 = true := by decide
theorem dsB_w14_3 : SS.bdot w14 y3 = true := by decide
theorem dsB_w14_4 : SS.bdot w14 y4 = true := by decide
theorem dsB_w14_5 : SS.bdot w14 y5 = true := by decide
theorem dsB_w14_6 : SS.bdot w14 y6 = false := by decide
theorem dsB_w14_7 : SS.bdot w14 y7 = false := by decide
theorem dsB_w14_8 : SS.bdot w14 y8 = true := by decide
theorem dsB_w14_9 : SS.bdot w14 y9 = true := by decide
theorem dsB_w14_10 : SS.bdot w14 y10 = false := by decide
theorem dsB_w14_11 : SS.bdot w14 y11 = false := by decide
theorem dsB_w14_12 : SS.bdot w14 y12 = false := by decide
theorem dsB_w14_13 : SS.bdot w14 y13 = false := by decide
theorem dsB_w14_14 : SS.bdot w14 y14 = true := by decide
theorem dsB_w14_15 : SS.bdot w14 y15 = true := by decide
theorem dsT_w14_0 : SS.bdot w14 z0 = false := by decide
theorem dsT_w14_1 : SS.bdot w14 z1 = false := by decide
theorem dsT_w14_2 : SS.bdot w14 z2 = true := by decide
theorem dsT_w14_3 : SS.bdot w14 z3 = true := by decide
theorem dsT_w14_4 : SS.bdot w14 z4 = true := by decide
theorem dsT_w14_5 : SS.bdot w14 z5 = true := by decide
theorem dsT_w14_6 : SS.bdot w14 z6 = false := by decide
theorem dsT_w14_7 : SS.bdot w14 z7 = false := by decide
theorem dsT_w14_8 : SS.bdot w14 z8 = true := by decide
theorem dsT_w14_9 : SS.bdot w14 z9 = true := by decide
theorem dsT_w14_10 : SS.bdot w14 z10 = false := by decide
theorem dsT_w14_11 : SS.bdot w14 z11 = false := by decide
theorem dsT_w14_12 : SS.bdot w14 z12 = false := by decide
theorem dsT_w14_13 : SS.bdot w14 z13 = false := by decide
theorem dsT_w14_14 : SS.bdot w14 z14 = true := by decide
theorem dsT_w14_15 : SS.bdot w14 z15 = true := by decide
theorem dexB_w14 (c : SS.BitString 6 -> ℂ) :
    diagBot c efZ w14 = star (c y8) * c y0 + star (c y9) * c y1 - star (c y10) * c y2 - star (c y11) * c y3 - star (c y12) * c y4 - star (c y13) * c y5 + star (c y14) * c y6 + star (c y15) * c y7 - star (c y0) * c y8 - star (c y1) * c y9 + star (c y2) * c y10 + star (c y3) * c y11 + star (c y4) * c y12 + star (c y5) * c y13 - star (c y6) * c y14 - star (c y7) * c y15 := by
  unfold diagBot
  rw [dincB]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipB_0, dflipB_1, dflipB_2, dflipB_3, dflipB_4, dflipB_5, dflipB_6, dflipB_7, dflipB_8, dflipB_9, dflipB_10, dflipB_11, dflipB_12, dflipB_13, dflipB_14, dflipB_15]
  simp only [dsB_w14_0, dsB_w14_1, dsB_w14_2, dsB_w14_3, dsB_w14_4, dsB_w14_5, dsB_w14_6, dsB_w14_7, dsB_w14_8, dsB_w14_9, dsB_w14_10, dsB_w14_11, dsB_w14_12, dsB_w14_13, dsB_w14_14, dsB_w14_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem dexT_w14 (dd : SS.BitString 6 -> ℂ) :
    diagTop dd efZ w14 = star (dd z8) * dd z0 + star (dd z9) * dd z1 - star (dd z10) * dd z2 - star (dd z11) * dd z3 - star (dd z12) * dd z4 - star (dd z13) * dd z5 + star (dd z14) * dd z6 + star (dd z15) * dd z7 - star (dd z0) * dd z8 - star (dd z1) * dd z9 + star (dd z2) * dd z10 + star (dd z3) * dd z11 + star (dd z4) * dd z12 + star (dd z5) * dd z13 - star (dd z6) * dd z14 - star (dd z7) * dd z15 := by
  unfold diagTop
  rw [dincT]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipT_0, dflipT_1, dflipT_2, dflipT_3, dflipT_4, dflipT_5, dflipT_6, dflipT_7, dflipT_8, dflipT_9, dflipT_10, dflipT_11, dflipT_12, dflipT_13, dflipT_14, dflipT_15]
  simp only [dsT_w14_0, dsT_w14_1, dsT_w14_2, dsT_w14_3, dsT_w14_4, dsT_w14_5, dsT_w14_6, dsT_w14_7, dsT_w14_8, dsT_w14_9, dsT_w14_10, dsT_w14_11, dsT_w14_12, dsT_w14_13, dsT_w14_14, dsT_w14_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dsB_w15_0 : SS.bdot w15 y0 = false := by decide
theorem dsB_w15_1 : SS.bdot w15 y1 = false := by decide
theorem dsB_w15_2 : SS.bdot w15 y2 = true := by decide
theorem dsB_w15_3 : SS.bdot w15 y3 = true := by decide
theorem dsB_w15_4 : SS.bdot w15 y4 = false := by decide
theorem dsB_w15_5 : SS.bdot w15 y5 = false := by decide
theorem dsB_w15_6 : SS.bdot w15 y6 = true := by decide
theorem dsB_w15_7 : SS.bdot w15 y7 = true := by decide
theorem dsB_w15_8 : SS.bdot w15 y8 = true := by decide
theorem dsB_w15_9 : SS.bdot w15 y9 = true := by decide
theorem dsB_w15_10 : SS.bdot w15 y10 = false := by decide
theorem dsB_w15_11 : SS.bdot w15 y11 = false := by decide
theorem dsB_w15_12 : SS.bdot w15 y12 = true := by decide
theorem dsB_w15_13 : SS.bdot w15 y13 = true := by decide
theorem dsB_w15_14 : SS.bdot w15 y14 = false := by decide
theorem dsB_w15_15 : SS.bdot w15 y15 = false := by decide
theorem dsT_w15_0 : SS.bdot w15 z0 = false := by decide
theorem dsT_w15_1 : SS.bdot w15 z1 = false := by decide
theorem dsT_w15_2 : SS.bdot w15 z2 = true := by decide
theorem dsT_w15_3 : SS.bdot w15 z3 = true := by decide
theorem dsT_w15_4 : SS.bdot w15 z4 = false := by decide
theorem dsT_w15_5 : SS.bdot w15 z5 = false := by decide
theorem dsT_w15_6 : SS.bdot w15 z6 = true := by decide
theorem dsT_w15_7 : SS.bdot w15 z7 = true := by decide
theorem dsT_w15_8 : SS.bdot w15 z8 = true := by decide
theorem dsT_w15_9 : SS.bdot w15 z9 = true := by decide
theorem dsT_w15_10 : SS.bdot w15 z10 = false := by decide
theorem dsT_w15_11 : SS.bdot w15 z11 = false := by decide
theorem dsT_w15_12 : SS.bdot w15 z12 = true := by decide
theorem dsT_w15_13 : SS.bdot w15 z13 = true := by decide
theorem dsT_w15_14 : SS.bdot w15 z14 = false := by decide
theorem dsT_w15_15 : SS.bdot w15 z15 = false := by decide
theorem dexB_w15 (c : SS.BitString 6 -> ℂ) :
    diagBot c efZ w15 = star (c y8) * c y0 + star (c y9) * c y1 - star (c y10) * c y2 - star (c y11) * c y3 + star (c y12) * c y4 + star (c y13) * c y5 - star (c y14) * c y6 - star (c y15) * c y7 - star (c y0) * c y8 - star (c y1) * c y9 + star (c y2) * c y10 + star (c y3) * c y11 - star (c y4) * c y12 - star (c y5) * c y13 + star (c y6) * c y14 + star (c y7) * c y15 := by
  unfold diagBot
  rw [dincB]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipB_0, dflipB_1, dflipB_2, dflipB_3, dflipB_4, dflipB_5, dflipB_6, dflipB_7, dflipB_8, dflipB_9, dflipB_10, dflipB_11, dflipB_12, dflipB_13, dflipB_14, dflipB_15]
  simp only [dsB_w15_0, dsB_w15_1, dsB_w15_2, dsB_w15_3, dsB_w15_4, dsB_w15_5, dsB_w15_6, dsB_w15_7, dsB_w15_8, dsB_w15_9, dsB_w15_10, dsB_w15_11, dsB_w15_12, dsB_w15_13, dsB_w15_14, dsB_w15_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem dexT_w15 (dd : SS.BitString 6 -> ℂ) :
    diagTop dd efZ w15 = star (dd z8) * dd z0 + star (dd z9) * dd z1 - star (dd z10) * dd z2 - star (dd z11) * dd z3 + star (dd z12) * dd z4 + star (dd z13) * dd z5 - star (dd z14) * dd z6 - star (dd z15) * dd z7 - star (dd z0) * dd z8 - star (dd z1) * dd z9 + star (dd z2) * dd z10 + star (dd z3) * dd z11 - star (dd z4) * dd z12 - star (dd z5) * dd z13 + star (dd z6) * dd z14 + star (dd z7) * dd z15 := by
  unfold diagTop
  rw [dincT]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipT_0, dflipT_1, dflipT_2, dflipT_3, dflipT_4, dflipT_5, dflipT_6, dflipT_7, dflipT_8, dflipT_9, dflipT_10, dflipT_11, dflipT_12, dflipT_13, dflipT_14, dflipT_15]
  simp only [dsT_w15_0, dsT_w15_1, dsT_w15_2, dsT_w15_3, dsT_w15_4, dsT_w15_5, dsT_w15_6, dsT_w15_7, dsT_w15_8, dsT_w15_9, dsT_w15_10, dsT_w15_11, dsT_w15_12, dsT_w15_13, dsT_w15_14, dsT_w15_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dsB_w16_0 : SS.bdot w16 y0 = false := by decide
theorem dsB_w16_1 : SS.bdot w16 y1 = false := by decide
theorem dsB_w16_2 : SS.bdot w16 y2 = false := by decide
theorem dsB_w16_3 : SS.bdot w16 y3 = false := by decide
theorem dsB_w16_4 : SS.bdot w16 y4 = true := by decide
theorem dsB_w16_5 : SS.bdot w16 y5 = true := by decide
theorem dsB_w16_6 : SS.bdot w16 y6 = true := by decide
theorem dsB_w16_7 : SS.bdot w16 y7 = true := by decide
theorem dsB_w16_8 : SS.bdot w16 y8 = true := by decide
theorem dsB_w16_9 : SS.bdot w16 y9 = true := by decide
theorem dsB_w16_10 : SS.bdot w16 y10 = true := by decide
theorem dsB_w16_11 : SS.bdot w16 y11 = true := by decide
theorem dsB_w16_12 : SS.bdot w16 y12 = false := by decide
theorem dsB_w16_13 : SS.bdot w16 y13 = false := by decide
theorem dsB_w16_14 : SS.bdot w16 y14 = false := by decide
theorem dsB_w16_15 : SS.bdot w16 y15 = false := by decide
theorem dsT_w16_0 : SS.bdot w16 z0 = false := by decide
theorem dsT_w16_1 : SS.bdot w16 z1 = false := by decide
theorem dsT_w16_2 : SS.bdot w16 z2 = false := by decide
theorem dsT_w16_3 : SS.bdot w16 z3 = false := by decide
theorem dsT_w16_4 : SS.bdot w16 z4 = true := by decide
theorem dsT_w16_5 : SS.bdot w16 z5 = true := by decide
theorem dsT_w16_6 : SS.bdot w16 z6 = true := by decide
theorem dsT_w16_7 : SS.bdot w16 z7 = true := by decide
theorem dsT_w16_8 : SS.bdot w16 z8 = true := by decide
theorem dsT_w16_9 : SS.bdot w16 z9 = true := by decide
theorem dsT_w16_10 : SS.bdot w16 z10 = true := by decide
theorem dsT_w16_11 : SS.bdot w16 z11 = true := by decide
theorem dsT_w16_12 : SS.bdot w16 z12 = false := by decide
theorem dsT_w16_13 : SS.bdot w16 z13 = false := by decide
theorem dsT_w16_14 : SS.bdot w16 z14 = false := by decide
theorem dsT_w16_15 : SS.bdot w16 z15 = false := by decide
theorem dexB_w16 (c : SS.BitString 6 -> ℂ) :
    diagBot c efZ w16 = star (c y8) * c y0 + star (c y9) * c y1 + star (c y10) * c y2 + star (c y11) * c y3 - star (c y12) * c y4 - star (c y13) * c y5 - star (c y14) * c y6 - star (c y15) * c y7 - star (c y0) * c y8 - star (c y1) * c y9 - star (c y2) * c y10 - star (c y3) * c y11 + star (c y4) * c y12 + star (c y5) * c y13 + star (c y6) * c y14 + star (c y7) * c y15 := by
  unfold diagBot
  rw [dincB]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipB_0, dflipB_1, dflipB_2, dflipB_3, dflipB_4, dflipB_5, dflipB_6, dflipB_7, dflipB_8, dflipB_9, dflipB_10, dflipB_11, dflipB_12, dflipB_13, dflipB_14, dflipB_15]
  simp only [dsB_w16_0, dsB_w16_1, dsB_w16_2, dsB_w16_3, dsB_w16_4, dsB_w16_5, dsB_w16_6, dsB_w16_7, dsB_w16_8, dsB_w16_9, dsB_w16_10, dsB_w16_11, dsB_w16_12, dsB_w16_13, dsB_w16_14, dsB_w16_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem dexT_w16 (dd : SS.BitString 6 -> ℂ) :
    diagTop dd efZ w16 = star (dd z8) * dd z0 + star (dd z9) * dd z1 + star (dd z10) * dd z2 + star (dd z11) * dd z3 - star (dd z12) * dd z4 - star (dd z13) * dd z5 - star (dd z14) * dd z6 - star (dd z15) * dd z7 - star (dd z0) * dd z8 - star (dd z1) * dd z9 - star (dd z2) * dd z10 - star (dd z3) * dd z11 + star (dd z4) * dd z12 + star (dd z5) * dd z13 + star (dd z6) * dd z14 + star (dd z7) * dd z15 := by
  unfold diagTop
  rw [dincT]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipT_0, dflipT_1, dflipT_2, dflipT_3, dflipT_4, dflipT_5, dflipT_6, dflipT_7, dflipT_8, dflipT_9, dflipT_10, dflipT_11, dflipT_12, dflipT_13, dflipT_14, dflipT_15]
  simp only [dsT_w16_0, dsT_w16_1, dsT_w16_2, dsT_w16_3, dsT_w16_4, dsT_w16_5, dsT_w16_6, dsT_w16_7, dsT_w16_8, dsT_w16_9, dsT_w16_10, dsT_w16_11, dsT_w16_12, dsT_w16_13, dsT_w16_14, dsT_w16_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

/-! ## The moment system -/

structure MomentSystem (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real) : Prop where
  n0 : q0 + q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 + q9 + q10 + q11 + q12 + q13 + q14 + q15 = 1
  n1 : r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15 = 1
  m1 : q8 + q9 + q10 + q11 + q12 + q13 + q14 + q15 = r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15
  m2 : q4 + q5 + q6 + q7 + q12 + q13 + q14 + q15 = r4 + r5 + r6 + r7 + r12 + r13 + r14 + r15
  m3 : q2 + q3 + q6 + q7 + q10 + q11 + q14 + q15 = r2 + r3 + r6 + r7 + r10 + r11 + r14 + r15
  m4 : q2 + q3 + q4 + q5 + q10 + q11 + q12 + q13 = r2 + r3 + r4 + r5 + r10 + r11 + r12 + r13
  m5 : q1 + q3 + q5 + q7 + q9 + q11 + q13 + q15 = r1 + r3 + r5 + r7 + r9 + r11 + r13 + r15
  m6 : q1 + q2 + q4 + q6 + q9 + q10 + q12 + q14 = r0 + r3 + r5 + r7 + r8 + r11 + r13 + r15
  m12 : q12 + q13 + q14 + q15 = r12 + r13 + r14 + r15
  m13 : q10 + q11 + q14 + q15 = r10 + r11 + r14 + r15
  m14 : q10 + q11 + q12 + q13 = r10 + r11 + r12 + r13
  m15 : q9 + q11 + q13 + q15 = r9 + r11 + r13 + r15
  m16 : q9 + q10 + q12 + q14 = r8 + r11 + r13 + r15
  m23 : q6 + q7 + q14 + q15 = r6 + r7 + r14 + r15
  m24 : q4 + q5 + q12 + q13 = r4 + r5 + r12 + r13
  m25 : q5 + q7 + q13 + q15 = r5 + r7 + r13 + r15
  m26 : q4 + q6 + q12 + q14 = r5 + r7 + r13 + r15
  m34 : q2 + q3 + q10 + q11 = r2 + r3 + r10 + r11
  m35 : q3 + q7 + q11 + q15 = r3 + r7 + r11 + r15
  m36 : q2 + q6 + q10 + q14 = r3 + r7 + r11 + r15
  m45 : q3 + q5 + q11 + q13 = r3 + r5 + r11 + r13
  m46 : q2 + q4 + q10 + q12 = r3 + r5 + r11 + r13
  m56 : q1 + q9 = r3 + r5 + r7 + r11 + r13 + r15

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

/-- Per-block equality of the free-qubit diagonal frame entries. -/
theorem MomentSystem.frameA {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    q0 + q1 = r0 + r1 ∧ q8 + q9 = r8 + r9 ∧ q2 + q3 = r2 + r3 ∧ q10 + q11 = r10 + r11 ∧ q4 + q5 = r4 + r5 ∧ q12 + q13 = r12 + r13 ∧ q6 + q7 = r6 + r7 ∧ q14 + q15 = r14 + r15 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, m12, m13, m14, m15, m16, m23, m24, m25, m26, m34, m35, m36, m45, m46, m56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-! ## The no-go -/

/-- **Orbit 13 is impossible.** -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11)) (Complex.normSq (c y12)) (Complex.normSq (c y13)) (Complex.normSq (c y14)) (Complex.normSq (c y15))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)) (Complex.normSq (d z12)) (Complex.normSq (d z13)) (Complex.normSq (d z14)) (Complex.normSq (d z15)))
    (ho0 : offSum c d ef0 w0 = 0)
    (ho1 : offSum c d ef0 w1 = 0)
    (ho2 : offSum c d ef0 w2 = 0)
    (ho3 : offSum c d ef0 w3 = 0)
    (ho4 : offSum c d ef0 w4 = 0)
    (ho5 : offSum c d ef0 w5 = 0)
    (ho6 : offSum c d ef0 w7 = 0)
    (ho7 : offSum c d ef0 w8 = 0)
    (ho8 : offSum c d ef1 w0 = 0)
    (ho9 : offSum c d ef1 w1 = 0)
    (ho10 : offSum c d ef1 w2 = 0)
    (ho11 : offSum c d ef1 w3 = 0)
    (ho12 : offSum c d ef1 w4 = 0)
    (ho13 : offSum c d ef1 w6 = 0)
    (ho14 : offSum c d ef1 w7 = 0)
    (ho15 : offSum c d ef1 w9 = 0)
    (hd0 : diagBot c efZ w0 = diagTop d efZ w0)
    (hd1 : diagBot c efZ w4 = diagTop d efZ w4)
    (hd2 : diagBot c efZ w7 = diagTop d efZ w7)
    (hd3 : diagBot c efZ w10 = diagTop d efZ w10)
    (hd4 : diagBot c efZ w11 = diagTop d efZ w11)
    (hd5 : diagBot c efZ w14 = diagTop d efZ w14)
    (hd6 : diagBot c efZ w15 = diagTop d efZ w15)
    (hd7 : diagBot c efZ w16 = diagTop d efZ w16)
    : False := by
  rw [ex_ef0_w0] at ho0
  rw [ex_ef0_w1] at ho1
  rw [ex_ef0_w2] at ho2
  rw [ex_ef0_w3] at ho3
  rw [ex_ef0_w4] at ho4
  rw [ex_ef0_w5] at ho5
  rw [ex_ef0_w7] at ho6
  rw [ex_ef0_w8] at ho7
  rw [ex_ef1_w0] at ho8
  rw [ex_ef1_w1] at ho9
  rw [ex_ef1_w2] at ho10
  rw [ex_ef1_w3] at ho11
  rw [ex_ef1_w4] at ho12
  rw [ex_ef1_w6] at ho13
  rw [ex_ef1_w7] at ho14
  rw [ex_ef1_w9] at ho15
  rw [dexB_w0, dexT_w0] at hd0
  rw [dexB_w4, dexT_w4] at hd1
  rw [dexB_w7, dexT_w7] at hd2
  rw [dexB_w10, dexT_w10] at hd3
  rw [dexB_w11, dexT_w11] at hd4
  rw [dexB_w14, dexT_w14] at hd5
  rw [dexB_w15, dexT_w15] at hd6
  rw [dexB_w16, dexT_w16] at hd7
  obtain ⟨fa0, fa1, fa2, fa3, fa4, fa5, fa6, fa7⟩ := hm.frameA
  have o11_0 : star (c y0) * d z0 + star (c y8) * d z8 = 0 := by
    linear_combination (1/4 : ℂ) * ho0 + (-1/4 : ℂ) * ho1 + (1/4 : ℂ) * ho2 + (-1/4 : ℂ) * ho3
  have o12_0 : star (c y0) * d z1 + star (c y8) * d z9 = 0 := by
    linear_combination (1/4 : ℂ) * ho8 + (1/4 : ℂ) * ho9 + (-1/4 : ℂ) * ho10 + (-1/4 : ℂ) * ho11
  have o21_0 : star (c y1) * d z0 + star (c y9) * d z8 = 0 := by
    linear_combination (1/4 : ℂ) * ho8 + (-1/4 : ℂ) * ho9 + (1/4 : ℂ) * ho10 + (-1/4 : ℂ) * ho11
  have o22_0 : star (c y1) * d z1 + star (c y9) * d z9 = 0 := by
    linear_combination (1/4 : ℂ) * ho0 + (1/4 : ℂ) * ho1 + (-1/4 : ℂ) * ho2 + (-1/4 : ℂ) * ho3
  have fc_0 : c y0 * star (c y8) + c y1 * star (c y9)
      = d z0 * star (d z8) + d z1 * star (d z9) := by
    linear_combination (1/8 : ℂ) * hd0 + (1/8 : ℂ) * hd1 + (1/8 : ℂ) * hd2 + (1/8 : ℂ) * hd3 + (1/8 : ℂ) * hd4 + (1/8 : ℂ) * hd5 + (1/8 : ℂ) * hd6 + (1/8 : ℂ) * hd7
  have blk_0 : Complex.normSq (c y0) + Complex.normSq (c y1) = 0 := by
    exact SixQubit.Frame.block_zero o11_0 o12_0 o21_0 o22_0 fa0 fc_0
  have sfc_0 : c y8 * star (c y0) + c y9 * star (c y1)
      = d z8 * star (d z0) + d z9 * star (d z1) := by
    have hs := congrArg star fc_0
    simp only [star_add, star_mul' , star_star] at hs
    linear_combination hs
  have so11_0 : star (c y8) * d z8 + star (c y0) * d z0 = 0 := by
    linear_combination o11_0
  have so12_0 : star (c y8) * d z9 + star (c y0) * d z1 = 0 := by
    linear_combination o12_0
  have so21_0 : star (c y9) * d z8 + star (c y1) * d z0 = 0 := by
    linear_combination o21_0
  have so22_0 : star (c y9) * d z9 + star (c y1) * d z1 = 0 := by
    linear_combination o22_0
  have blkb_0 : Complex.normSq (c y8) + Complex.normSq (c y9) = 0 :=
    SixQubit.Frame.block_zero so11_0 so12_0 so21_0 so22_0 fa1 sfc_0
  have o11_1 : star (c y2) * d z2 + star (c y10) * d z10 = 0 := by
    linear_combination (1/4 : ℂ) * ho0 + (1/4 : ℂ) * ho1 + (-1/4 : ℂ) * ho2 + (-1/4 : ℂ) * ho3 + (-1/4 : ℂ) * ho4 + (-1/4 : ℂ) * ho5 + (-1/4 : ℂ) * ho6 + (-1/4 : ℂ) * ho7
  have o12_1 : star (c y2) * d z3 + star (c y10) * d z11 = 0 := by
    linear_combination (1/4 : ℂ) * ho8 + (1/4 : ℂ) * ho9 + (-1/4 : ℂ) * ho10 + (-1/4 : ℂ) * ho11 + (-1/4 : ℂ) * ho12 + (1/4 : ℂ) * ho13 + (-1/4 : ℂ) * ho14 + (1/4 : ℂ) * ho15
  have o21_1 : star (c y3) * d z2 + star (c y11) * d z10 = 0 := by
    linear_combination (1/4 : ℂ) * ho8 + (-1/4 : ℂ) * ho9 + (1/4 : ℂ) * ho10 + (-1/4 : ℂ) * ho11 + (-1/4 : ℂ) * ho12 + (-1/4 : ℂ) * ho13 + (-1/4 : ℂ) * ho14 + (-1/4 : ℂ) * ho15
  have o22_1 : star (c y3) * d z3 + star (c y11) * d z11 = 0 := by
    linear_combination (1/4 : ℂ) * ho0 + (-1/4 : ℂ) * ho1 + (1/4 : ℂ) * ho2 + (-1/4 : ℂ) * ho3 + (-1/4 : ℂ) * ho4 + (1/4 : ℂ) * ho5 + (-1/4 : ℂ) * ho6 + (1/4 : ℂ) * ho7
  have fc_1 : c y2 * star (c y10) + c y3 * star (c y11)
      = d z2 * star (d z10) + d z3 * star (d z11) := by
    linear_combination (1/8 : ℂ) * hd0 + (-1/8 : ℂ) * hd1 + (-1/8 : ℂ) * hd2 + (1/8 : ℂ) * hd3 + (1/8 : ℂ) * hd4 + (-1/8 : ℂ) * hd5 + (-1/8 : ℂ) * hd6 + (1/8 : ℂ) * hd7
  have blk_1 : Complex.normSq (c y2) + Complex.normSq (c y3) = 0 := by
    exact SixQubit.Frame.block_zero o11_1 o12_1 o21_1 o22_1 fa2 fc_1
  have sfc_1 : c y10 * star (c y2) + c y11 * star (c y3)
      = d z10 * star (d z2) + d z11 * star (d z3) := by
    have hs := congrArg star fc_1
    simp only [star_add, star_mul' , star_star] at hs
    linear_combination hs
  have so11_1 : star (c y10) * d z10 + star (c y2) * d z2 = 0 := by
    linear_combination o11_1
  have so12_1 : star (c y10) * d z11 + star (c y2) * d z3 = 0 := by
    linear_combination o12_1
  have so21_1 : star (c y11) * d z10 + star (c y3) * d z2 = 0 := by
    linear_combination o21_1
  have so22_1 : star (c y11) * d z11 + star (c y3) * d z3 = 0 := by
    linear_combination o22_1
  have blkb_1 : Complex.normSq (c y10) + Complex.normSq (c y11) = 0 :=
    SixQubit.Frame.block_zero so11_1 so12_1 so21_1 so22_1 fa3 sfc_1
  have o11_2 : star (c y4) * d z4 + star (c y12) * d z12 = 0 := by
    linear_combination (1/4 : ℂ) * ho2 + (1/4 : ℂ) * ho3 + (1/4 : ℂ) * ho6 + (1/4 : ℂ) * ho7
  have o12_2 : star (c y4) * d z5 + star (c y12) * d z13 = 0 := by
    linear_combination (-1/4 : ℂ) * ho9 + (1/4 : ℂ) * ho11 + (1/4 : ℂ) * ho14 + (-1/4 : ℂ) * ho15
  have o21_2 : star (c y5) * d z4 + star (c y13) * d z12 = 0 := by
    linear_combination (1/4 : ℂ) * ho9 + (1/4 : ℂ) * ho11 + (1/4 : ℂ) * ho14 + (1/4 : ℂ) * ho15
  have o22_2 : star (c y5) * d z5 + star (c y13) * d z13 = 0 := by
    linear_combination (-1/4 : ℂ) * ho2 + (1/4 : ℂ) * ho3 + (1/4 : ℂ) * ho6 + (-1/4 : ℂ) * ho7
  have fc_2 : c y4 * star (c y12) + c y5 * star (c y13)
      = d z4 * star (d z12) + d z5 * star (d z13) := by
    linear_combination (1/8 : ℂ) * hd0 + (-1/8 : ℂ) * hd1 + (1/8 : ℂ) * hd2 + (-1/8 : ℂ) * hd3 + (1/8 : ℂ) * hd4 + (-1/8 : ℂ) * hd5 + (1/8 : ℂ) * hd6 + (-1/8 : ℂ) * hd7
  have blk_2 : Complex.normSq (c y4) + Complex.normSq (c y5) = 0 := by
    exact SixQubit.Frame.block_zero o11_2 o12_2 o21_2 o22_2 fa4 fc_2
  have sfc_2 : c y12 * star (c y4) + c y13 * star (c y5)
      = d z12 * star (d z4) + d z13 * star (d z5) := by
    have hs := congrArg star fc_2
    simp only [star_add, star_mul' , star_star] at hs
    linear_combination hs
  have so11_2 : star (c y12) * d z12 + star (c y4) * d z4 = 0 := by
    linear_combination o11_2
  have so12_2 : star (c y12) * d z13 + star (c y4) * d z5 = 0 := by
    linear_combination o12_2
  have so21_2 : star (c y13) * d z12 + star (c y5) * d z4 = 0 := by
    linear_combination o21_2
  have so22_2 : star (c y13) * d z13 + star (c y5) * d z5 = 0 := by
    linear_combination o22_2
  have blkb_2 : Complex.normSq (c y12) + Complex.normSq (c y13) = 0 :=
    SixQubit.Frame.block_zero so11_2 so12_2 so21_2 so22_2 fa5 sfc_2
  have o11_3 : star (c y6) * d z6 + star (c y14) * d z14 = 0 := by
    linear_combination (1/4 : ℂ) * ho2 + (1/4 : ℂ) * ho3 + (1/4 : ℂ) * ho4 + (1/4 : ℂ) * ho5
  have o12_3 : star (c y6) * d z7 + star (c y14) * d z15 = 0 := by
    linear_combination (-1/4 : ℂ) * ho9 + (1/4 : ℂ) * ho11 + (1/4 : ℂ) * ho12 + (-1/4 : ℂ) * ho13
  have o21_3 : star (c y7) * d z6 + star (c y15) * d z14 = 0 := by
    linear_combination (1/4 : ℂ) * ho9 + (1/4 : ℂ) * ho11 + (1/4 : ℂ) * ho12 + (1/4 : ℂ) * ho13
  have o22_3 : star (c y7) * d z7 + star (c y15) * d z15 = 0 := by
    linear_combination (-1/4 : ℂ) * ho2 + (1/4 : ℂ) * ho3 + (1/4 : ℂ) * ho4 + (-1/4 : ℂ) * ho5
  have fc_3 : c y6 * star (c y14) + c y7 * star (c y15)
      = d z6 * star (d z14) + d z7 * star (d z15) := by
    linear_combination (1/8 : ℂ) * hd0 + (1/8 : ℂ) * hd1 + (-1/8 : ℂ) * hd2 + (-1/8 : ℂ) * hd3 + (1/8 : ℂ) * hd4 + (1/8 : ℂ) * hd5 + (-1/8 : ℂ) * hd6 + (-1/8 : ℂ) * hd7
  have blk_3 : Complex.normSq (c y6) + Complex.normSq (c y7) = 0 := by
    exact SixQubit.Frame.block_zero o11_3 o12_3 o21_3 o22_3 fa6 fc_3
  have sfc_3 : c y14 * star (c y6) + c y15 * star (c y7)
      = d z14 * star (d z6) + d z15 * star (d z7) := by
    have hs := congrArg star fc_3
    simp only [star_add, star_mul' , star_star] at hs
    linear_combination hs
  have so11_3 : star (c y14) * d z14 + star (c y6) * d z6 = 0 := by
    linear_combination o11_3
  have so12_3 : star (c y14) * d z15 + star (c y6) * d z7 = 0 := by
    linear_combination o12_3
  have so21_3 : star (c y15) * d z14 + star (c y7) * d z6 = 0 := by
    linear_combination o21_3
  have so22_3 : star (c y15) * d z15 + star (c y7) * d z7 = 0 := by
    linear_combination o22_3
  have blkb_3 : Complex.normSq (c y14) + Complex.normSq (c y15) = 0 :=
    SixQubit.Frame.block_zero so11_3 so12_3 so21_3 so22_3 fa7 sfc_3
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, m12, m13, m14, m15, m16, m23, m24, m25, m26, m34, m35, m36, m45, m46, m56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := hm
  linarith [blk_0, blk_1, blk_2, blk_3, blkb_0, blkb_1, blkb_2, blkb_3]

end

end SixQubit.Orbit13
