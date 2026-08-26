import Mathlib

import SS.FullKL
import SixQubit.Common
import SixQubit.Frame
import SixQubit.ParityFour

/-!
# Six-qubit no-go for moment orbit 15

Orbit 15 of `six_qubit_sslp.tex`: q = 4, angle vector
a = (0, 1, 2, 2, 2, 2), residues 0 and 2.

Qubit 2 is frozen to 0 on both fibers and qubits 3,4,5,6 carry the four effective parity bits.
Amplitudes are collected over the zero-angle qubit 1 into vectors in `ℂ²`, so
the fibers are indexed by `(free bit, effective four-bit string)`; the
bottom fiber carries the even strings and the top fiber the odd ones.

Effective coordinate %d has a weight-one physical `Z` character, which may
dress the free-qubit operators without leaving weight two.  Both of its
three-cube slices therefore inherit the full frame equality, and
`SixQubit.ParityFour.slice_zero` gives each slice zero mass.  The two
slices exhaust the fiber, contradicting normalization.

Everything computational is decided by the Lean kernel; `native_decide`
is not used.
-/

namespace SixQubit.Orbit15

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

/-! ## The two fibers -/

def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]

def y0 : SS.BitString 6 := bs false false false false false false  -- 000000
def y1 : SS.BitString 6 := bs false false false false true  true   -- 000011
def y2 : SS.BitString 6 := bs false false false true  false true   -- 000101
def y3 : SS.BitString 6 := bs false false false true  true  false  -- 000110
def y4 : SS.BitString 6 := bs false false true  false false true   -- 001001
def y5 : SS.BitString 6 := bs false false true  false true  false  -- 001010
def y6 : SS.BitString 6 := bs false false true  true  false false  -- 001100
def y7 : SS.BitString 6 := bs false false true  true  true  true   -- 001111
def y8 : SS.BitString 6 := bs true  false false false false false  -- 100000
def y9 : SS.BitString 6 := bs true  false false false true  true   -- 100011
def y10 : SS.BitString 6 := bs true  false false true  false true   -- 100101
def y11 : SS.BitString 6 := bs true  false false true  true  false  -- 100110
def y12 : SS.BitString 6 := bs true  false true  false false true   -- 101001
def y13 : SS.BitString 6 := bs true  false true  false true  false  -- 101010
def y14 : SS.BitString 6 := bs true  false true  true  false false  -- 101100
def y15 : SS.BitString 6 := bs true  false true  true  true  true   -- 101111

def z0 : SS.BitString 6 := bs false false false false false true   -- 000001
def z1 : SS.BitString 6 := bs false false false false true  false  -- 000010
def z2 : SS.BitString 6 := bs false false false true  false false  -- 000100
def z3 : SS.BitString 6 := bs false false false true  true  true   -- 000111
def z4 : SS.BitString 6 := bs false false true  false false false  -- 001000
def z5 : SS.BitString 6 := bs false false true  false true  true   -- 001011
def z6 : SS.BitString 6 := bs false false true  true  false true   -- 001101
def z7 : SS.BitString 6 := bs false false true  true  true  false  -- 001110
def z8 : SS.BitString 6 := bs true  false false false false true   -- 100001
def z9 : SS.BitString 6 := bs true  false false false true  false  -- 100010
def z10 : SS.BitString 6 := bs true  false false true  false false  -- 100100
def z11 : SS.BitString 6 := bs true  false false true  true  true   -- 100111
def z12 : SS.BitString 6 := bs true  false true  false false false  -- 101000
def z13 : SS.BitString 6 := bs true  false true  false true  true   -- 101011
def z14 : SS.BitString 6 := bs true  false true  true  false true   -- 101101
def z15 : SS.BitString 6 := bs true  false true  true  true  false  -- 101110

def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15}
def S1 : Finset (SS.BitString 6) := {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15}

def av : Fin 6 -> ZMod 4 := ![0, 1, 2, 2, 2, 2]

theorem S0_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 0) = S0 := by
  decide

theorem S1_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 2) = S1 := by
  decide

/-! ## Masks and dressings -/

def ef1 : SS.BitString 6 := bs false false false true  false false  -- 000100
def ef2 : SS.BitString 6 := bs false false false false true  false  -- 000010
def ef3 : SS.BitString 6 := bs false false false false false true   -- 000001
def efF : SS.BitString 6 := bs true  false false false false false  -- 100000
def w0 : SS.BitString 6 := bs false false false false false false  -- 000000
def w1 : SS.BitString 6 := bs false false false false false true   -- 000001
def w2 : SS.BitString 6 := bs false false false false true  false  -- 000010
def w3 : SS.BitString 6 := bs false false false false true  true   -- 000011
def w4 : SS.BitString 6 := bs false false false true  false false  -- 000100
def w5 : SS.BitString 6 := bs false false false true  false true   -- 000101
def w6 : SS.BitString 6 := bs false false false true  true  false  -- 000110
def w7 : SS.BitString 6 := bs false false true  false false false  -- 001000
def w8 : SS.BitString 6 := bs false false true  false false true   -- 001001
def w9 : SS.BitString 6 := bs false false true  false true  false  -- 001010
def w10 : SS.BitString 6 := bs false false true  true  false false  -- 001100
def w11 : SS.BitString 6 := bs true  false false false false false  -- 100000
def w12 : SS.BitString 6 := bs true  false true  false false false  -- 101000

/-! ## The off-diagonal layer -/

def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),
      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

theorem incidence_ef1 :
    S1.filter (fun y => SS.bxor y ef1 ∈ S0) = {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15} := by decide
theorem flip_ef1_0 : SS.bxor z0 ef1 = y2 := by decide
theorem flip_ef1_1 : SS.bxor z1 ef1 = y3 := by decide
theorem flip_ef1_2 : SS.bxor z2 ef1 = y0 := by decide
theorem flip_ef1_3 : SS.bxor z3 ef1 = y1 := by decide
theorem flip_ef1_4 : SS.bxor z4 ef1 = y6 := by decide
theorem flip_ef1_5 : SS.bxor z5 ef1 = y7 := by decide
theorem flip_ef1_6 : SS.bxor z6 ef1 = y4 := by decide
theorem flip_ef1_7 : SS.bxor z7 ef1 = y5 := by decide
theorem flip_ef1_8 : SS.bxor z8 ef1 = y10 := by decide
theorem flip_ef1_9 : SS.bxor z9 ef1 = y11 := by decide
theorem flip_ef1_10 : SS.bxor z10 ef1 = y8 := by decide
theorem flip_ef1_11 : SS.bxor z11 ef1 = y9 := by decide
theorem flip_ef1_12 : SS.bxor z12 ef1 = y14 := by decide
theorem flip_ef1_13 : SS.bxor z13 ef1 = y15 := by decide
theorem flip_ef1_14 : SS.bxor z14 ef1 = y12 := by decide
theorem flip_ef1_15 : SS.bxor z15 ef1 = y13 := by decide
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
    offSum c d ef1 w0 = star (c y2) * d z0 + star (c y3) * d z1 + star (c y0) * d z2 + star (c y1) * d z3 + star (c y6) * d z4 + star (c y7) * d z5 + star (c y4) * d z6 + star (c y5) * d z7 + star (c y10) * d z8 + star (c y11) * d z9 + star (c y8) * d z10 + star (c y9) * d z11 + star (c y14) * d z12 + star (c y15) * d z13 + star (c y12) * d z14 + star (c y13) * d z15 := by
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
theorem sg_ef1_w1_6 : SS.bdot w1 z6 = true := by decide
theorem sg_ef1_w1_7 : SS.bdot w1 z7 = false := by decide
theorem sg_ef1_w1_8 : SS.bdot w1 z8 = true := by decide
theorem sg_ef1_w1_9 : SS.bdot w1 z9 = false := by decide
theorem sg_ef1_w1_10 : SS.bdot w1 z10 = false := by decide
theorem sg_ef1_w1_11 : SS.bdot w1 z11 = true := by decide
theorem sg_ef1_w1_12 : SS.bdot w1 z12 = false := by decide
theorem sg_ef1_w1_13 : SS.bdot w1 z13 = true := by decide
theorem sg_ef1_w1_14 : SS.bdot w1 z14 = true := by decide
theorem sg_ef1_w1_15 : SS.bdot w1 z15 = false := by decide
theorem ex_ef1_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w1 = - star (c y2) * d z0 + star (c y3) * d z1 + star (c y0) * d z2 - star (c y1) * d z3 + star (c y6) * d z4 - star (c y7) * d z5 - star (c y4) * d z6 + star (c y5) * d z7 - star (c y10) * d z8 + star (c y11) * d z9 + star (c y8) * d z10 - star (c y9) * d z11 + star (c y14) * d z12 - star (c y15) * d z13 - star (c y12) * d z14 + star (c y13) * d z15 := by
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
    offSum c d ef1 w2 = star (c y2) * d z0 - star (c y3) * d z1 + star (c y0) * d z2 - star (c y1) * d z3 + star (c y6) * d z4 - star (c y7) * d z5 + star (c y4) * d z6 - star (c y5) * d z7 + star (c y10) * d z8 - star (c y11) * d z9 + star (c y8) * d z10 - star (c y9) * d z11 + star (c y14) * d z12 - star (c y15) * d z13 + star (c y12) * d z14 - star (c y13) * d z15 := by
  unfold offSum
  rw [incidence_ef1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef1_0, flip_ef1_1, flip_ef1_2, flip_ef1_3, flip_ef1_4, flip_ef1_5, flip_ef1_6, flip_ef1_7, flip_ef1_8, flip_ef1_9, flip_ef1_10, flip_ef1_11, flip_ef1_12, flip_ef1_13, flip_ef1_14, flip_ef1_15]
  simp only [sg_ef1_w2_0, sg_ef1_w2_1, sg_ef1_w2_2, sg_ef1_w2_3, sg_ef1_w2_4, sg_ef1_w2_5, sg_ef1_w2_6, sg_ef1_w2_7, sg_ef1_w2_8, sg_ef1_w2_9, sg_ef1_w2_10, sg_ef1_w2_11, sg_ef1_w2_12, sg_ef1_w2_13, sg_ef1_w2_14, sg_ef1_w2_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef1_w4_0 : SS.bdot w4 z0 = false := by decide
theorem sg_ef1_w4_1 : SS.bdot w4 z1 = false := by decide
theorem sg_ef1_w4_2 : SS.bdot w4 z2 = true := by decide
theorem sg_ef1_w4_3 : SS.bdot w4 z3 = true := by decide
theorem sg_ef1_w4_4 : SS.bdot w4 z4 = false := by decide
theorem sg_ef1_w4_5 : SS.bdot w4 z5 = false := by decide
theorem sg_ef1_w4_6 : SS.bdot w4 z6 = true := by decide
theorem sg_ef1_w4_7 : SS.bdot w4 z7 = true := by decide
theorem sg_ef1_w4_8 : SS.bdot w4 z8 = false := by decide
theorem sg_ef1_w4_9 : SS.bdot w4 z9 = false := by decide
theorem sg_ef1_w4_10 : SS.bdot w4 z10 = true := by decide
theorem sg_ef1_w4_11 : SS.bdot w4 z11 = true := by decide
theorem sg_ef1_w4_12 : SS.bdot w4 z12 = false := by decide
theorem sg_ef1_w4_13 : SS.bdot w4 z13 = false := by decide
theorem sg_ef1_w4_14 : SS.bdot w4 z14 = true := by decide
theorem sg_ef1_w4_15 : SS.bdot w4 z15 = true := by decide
theorem ex_ef1_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w4 = star (c y2) * d z0 + star (c y3) * d z1 - star (c y0) * d z2 - star (c y1) * d z3 + star (c y6) * d z4 + star (c y7) * d z5 - star (c y4) * d z6 - star (c y5) * d z7 + star (c y10) * d z8 + star (c y11) * d z9 - star (c y8) * d z10 - star (c y9) * d z11 + star (c y14) * d z12 + star (c y15) * d z13 - star (c y12) * d z14 - star (c y13) * d z15 := by
  unfold offSum
  rw [incidence_ef1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef1_0, flip_ef1_1, flip_ef1_2, flip_ef1_3, flip_ef1_4, flip_ef1_5, flip_ef1_6, flip_ef1_7, flip_ef1_8, flip_ef1_9, flip_ef1_10, flip_ef1_11, flip_ef1_12, flip_ef1_13, flip_ef1_14, flip_ef1_15]
  simp only [sg_ef1_w4_0, sg_ef1_w4_1, sg_ef1_w4_2, sg_ef1_w4_3, sg_ef1_w4_4, sg_ef1_w4_5, sg_ef1_w4_6, sg_ef1_w4_7, sg_ef1_w4_8, sg_ef1_w4_9, sg_ef1_w4_10, sg_ef1_w4_11, sg_ef1_w4_12, sg_ef1_w4_13, sg_ef1_w4_14, sg_ef1_w4_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef1_w5_0 : SS.bdot w5 z0 = true := by decide
theorem sg_ef1_w5_1 : SS.bdot w5 z1 = false := by decide
theorem sg_ef1_w5_2 : SS.bdot w5 z2 = true := by decide
theorem sg_ef1_w5_3 : SS.bdot w5 z3 = false := by decide
theorem sg_ef1_w5_4 : SS.bdot w5 z4 = false := by decide
theorem sg_ef1_w5_5 : SS.bdot w5 z5 = true := by decide
theorem sg_ef1_w5_6 : SS.bdot w5 z6 = false := by decide
theorem sg_ef1_w5_7 : SS.bdot w5 z7 = true := by decide
theorem sg_ef1_w5_8 : SS.bdot w5 z8 = true := by decide
theorem sg_ef1_w5_9 : SS.bdot w5 z9 = false := by decide
theorem sg_ef1_w5_10 : SS.bdot w5 z10 = true := by decide
theorem sg_ef1_w5_11 : SS.bdot w5 z11 = false := by decide
theorem sg_ef1_w5_12 : SS.bdot w5 z12 = false := by decide
theorem sg_ef1_w5_13 : SS.bdot w5 z13 = true := by decide
theorem sg_ef1_w5_14 : SS.bdot w5 z14 = false := by decide
theorem sg_ef1_w5_15 : SS.bdot w5 z15 = true := by decide
theorem ex_ef1_w5 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w5 = - star (c y2) * d z0 + star (c y3) * d z1 - star (c y0) * d z2 + star (c y1) * d z3 + star (c y6) * d z4 - star (c y7) * d z5 + star (c y4) * d z6 - star (c y5) * d z7 - star (c y10) * d z8 + star (c y11) * d z9 - star (c y8) * d z10 + star (c y9) * d z11 + star (c y14) * d z12 - star (c y15) * d z13 + star (c y12) * d z14 - star (c y13) * d z15 := by
  unfold offSum
  rw [incidence_ef1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef1_0, flip_ef1_1, flip_ef1_2, flip_ef1_3, flip_ef1_4, flip_ef1_5, flip_ef1_6, flip_ef1_7, flip_ef1_8, flip_ef1_9, flip_ef1_10, flip_ef1_11, flip_ef1_12, flip_ef1_13, flip_ef1_14, flip_ef1_15]
  simp only [sg_ef1_w5_0, sg_ef1_w5_1, sg_ef1_w5_2, sg_ef1_w5_3, sg_ef1_w5_4, sg_ef1_w5_5, sg_ef1_w5_6, sg_ef1_w5_7, sg_ef1_w5_8, sg_ef1_w5_9, sg_ef1_w5_10, sg_ef1_w5_11, sg_ef1_w5_12, sg_ef1_w5_13, sg_ef1_w5_14, sg_ef1_w5_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef1_w6_0 : SS.bdot w6 z0 = false := by decide
theorem sg_ef1_w6_1 : SS.bdot w6 z1 = true := by decide
theorem sg_ef1_w6_2 : SS.bdot w6 z2 = true := by decide
theorem sg_ef1_w6_3 : SS.bdot w6 z3 = false := by decide
theorem sg_ef1_w6_4 : SS.bdot w6 z4 = false := by decide
theorem sg_ef1_w6_5 : SS.bdot w6 z5 = true := by decide
theorem sg_ef1_w6_6 : SS.bdot w6 z6 = true := by decide
theorem sg_ef1_w6_7 : SS.bdot w6 z7 = false := by decide
theorem sg_ef1_w6_8 : SS.bdot w6 z8 = false := by decide
theorem sg_ef1_w6_9 : SS.bdot w6 z9 = true := by decide
theorem sg_ef1_w6_10 : SS.bdot w6 z10 = true := by decide
theorem sg_ef1_w6_11 : SS.bdot w6 z11 = false := by decide
theorem sg_ef1_w6_12 : SS.bdot w6 z12 = false := by decide
theorem sg_ef1_w6_13 : SS.bdot w6 z13 = true := by decide
theorem sg_ef1_w6_14 : SS.bdot w6 z14 = true := by decide
theorem sg_ef1_w6_15 : SS.bdot w6 z15 = false := by decide
theorem ex_ef1_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w6 = star (c y2) * d z0 - star (c y3) * d z1 - star (c y0) * d z2 + star (c y1) * d z3 + star (c y6) * d z4 - star (c y7) * d z5 - star (c y4) * d z6 + star (c y5) * d z7 + star (c y10) * d z8 - star (c y11) * d z9 - star (c y8) * d z10 + star (c y9) * d z11 + star (c y14) * d z12 - star (c y15) * d z13 - star (c y12) * d z14 + star (c y13) * d z15 := by
  unfold offSum
  rw [incidence_ef1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef1_0, flip_ef1_1, flip_ef1_2, flip_ef1_3, flip_ef1_4, flip_ef1_5, flip_ef1_6, flip_ef1_7, flip_ef1_8, flip_ef1_9, flip_ef1_10, flip_ef1_11, flip_ef1_12, flip_ef1_13, flip_ef1_14, flip_ef1_15]
  simp only [sg_ef1_w6_0, sg_ef1_w6_1, sg_ef1_w6_2, sg_ef1_w6_3, sg_ef1_w6_4, sg_ef1_w6_5, sg_ef1_w6_6, sg_ef1_w6_7, sg_ef1_w6_8, sg_ef1_w6_9, sg_ef1_w6_10, sg_ef1_w6_11, sg_ef1_w6_12, sg_ef1_w6_13, sg_ef1_w6_14, sg_ef1_w6_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef1_w7_0 : SS.bdot w7 z0 = false := by decide
theorem sg_ef1_w7_1 : SS.bdot w7 z1 = false := by decide
theorem sg_ef1_w7_2 : SS.bdot w7 z2 = false := by decide
theorem sg_ef1_w7_3 : SS.bdot w7 z3 = false := by decide
theorem sg_ef1_w7_4 : SS.bdot w7 z4 = true := by decide
theorem sg_ef1_w7_5 : SS.bdot w7 z5 = true := by decide
theorem sg_ef1_w7_6 : SS.bdot w7 z6 = true := by decide
theorem sg_ef1_w7_7 : SS.bdot w7 z7 = true := by decide
theorem sg_ef1_w7_8 : SS.bdot w7 z8 = false := by decide
theorem sg_ef1_w7_9 : SS.bdot w7 z9 = false := by decide
theorem sg_ef1_w7_10 : SS.bdot w7 z10 = false := by decide
theorem sg_ef1_w7_11 : SS.bdot w7 z11 = false := by decide
theorem sg_ef1_w7_12 : SS.bdot w7 z12 = true := by decide
theorem sg_ef1_w7_13 : SS.bdot w7 z13 = true := by decide
theorem sg_ef1_w7_14 : SS.bdot w7 z14 = true := by decide
theorem sg_ef1_w7_15 : SS.bdot w7 z15 = true := by decide
theorem ex_ef1_w7 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w7 = star (c y2) * d z0 + star (c y3) * d z1 + star (c y0) * d z2 + star (c y1) * d z3 - star (c y6) * d z4 - star (c y7) * d z5 - star (c y4) * d z6 - star (c y5) * d z7 + star (c y10) * d z8 + star (c y11) * d z9 + star (c y8) * d z10 + star (c y9) * d z11 - star (c y14) * d z12 - star (c y15) * d z13 - star (c y12) * d z14 - star (c y13) * d z15 := by
  unfold offSum
  rw [incidence_ef1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef1_0, flip_ef1_1, flip_ef1_2, flip_ef1_3, flip_ef1_4, flip_ef1_5, flip_ef1_6, flip_ef1_7, flip_ef1_8, flip_ef1_9, flip_ef1_10, flip_ef1_11, flip_ef1_12, flip_ef1_13, flip_ef1_14, flip_ef1_15]
  simp only [sg_ef1_w7_0, sg_ef1_w7_1, sg_ef1_w7_2, sg_ef1_w7_3, sg_ef1_w7_4, sg_ef1_w7_5, sg_ef1_w7_6, sg_ef1_w7_7, sg_ef1_w7_8, sg_ef1_w7_9, sg_ef1_w7_10, sg_ef1_w7_11, sg_ef1_w7_12, sg_ef1_w7_13, sg_ef1_w7_14, sg_ef1_w7_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef1_w10_0 : SS.bdot w10 z0 = false := by decide
theorem sg_ef1_w10_1 : SS.bdot w10 z1 = false := by decide
theorem sg_ef1_w10_2 : SS.bdot w10 z2 = true := by decide
theorem sg_ef1_w10_3 : SS.bdot w10 z3 = true := by decide
theorem sg_ef1_w10_4 : SS.bdot w10 z4 = true := by decide
theorem sg_ef1_w10_5 : SS.bdot w10 z5 = true := by decide
theorem sg_ef1_w10_6 : SS.bdot w10 z6 = false := by decide
theorem sg_ef1_w10_7 : SS.bdot w10 z7 = false := by decide
theorem sg_ef1_w10_8 : SS.bdot w10 z8 = false := by decide
theorem sg_ef1_w10_9 : SS.bdot w10 z9 = false := by decide
theorem sg_ef1_w10_10 : SS.bdot w10 z10 = true := by decide
theorem sg_ef1_w10_11 : SS.bdot w10 z11 = true := by decide
theorem sg_ef1_w10_12 : SS.bdot w10 z12 = true := by decide
theorem sg_ef1_w10_13 : SS.bdot w10 z13 = true := by decide
theorem sg_ef1_w10_14 : SS.bdot w10 z14 = false := by decide
theorem sg_ef1_w10_15 : SS.bdot w10 z15 = false := by decide
theorem ex_ef1_w10 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w10 = star (c y2) * d z0 + star (c y3) * d z1 - star (c y0) * d z2 - star (c y1) * d z3 - star (c y6) * d z4 - star (c y7) * d z5 + star (c y4) * d z6 + star (c y5) * d z7 + star (c y10) * d z8 + star (c y11) * d z9 - star (c y8) * d z10 - star (c y9) * d z11 - star (c y14) * d z12 - star (c y15) * d z13 + star (c y12) * d z14 + star (c y13) * d z15 := by
  unfold offSum
  rw [incidence_ef1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef1_0, flip_ef1_1, flip_ef1_2, flip_ef1_3, flip_ef1_4, flip_ef1_5, flip_ef1_6, flip_ef1_7, flip_ef1_8, flip_ef1_9, flip_ef1_10, flip_ef1_11, flip_ef1_12, flip_ef1_13, flip_ef1_14, flip_ef1_15]
  simp only [sg_ef1_w10_0, sg_ef1_w10_1, sg_ef1_w10_2, sg_ef1_w10_3, sg_ef1_w10_4, sg_ef1_w10_5, sg_ef1_w10_6, sg_ef1_w10_7, sg_ef1_w10_8, sg_ef1_w10_9, sg_ef1_w10_10, sg_ef1_w10_11, sg_ef1_w10_12, sg_ef1_w10_13, sg_ef1_w10_14, sg_ef1_w10_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem incidence_ef2 :
    S1.filter (fun y => SS.bxor y ef2 ∈ S0) = {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15} := by decide
theorem flip_ef2_0 : SS.bxor z0 ef2 = y1 := by decide
theorem flip_ef2_1 : SS.bxor z1 ef2 = y0 := by decide
theorem flip_ef2_2 : SS.bxor z2 ef2 = y3 := by decide
theorem flip_ef2_3 : SS.bxor z3 ef2 = y2 := by decide
theorem flip_ef2_4 : SS.bxor z4 ef2 = y5 := by decide
theorem flip_ef2_5 : SS.bxor z5 ef2 = y4 := by decide
theorem flip_ef2_6 : SS.bxor z6 ef2 = y7 := by decide
theorem flip_ef2_7 : SS.bxor z7 ef2 = y6 := by decide
theorem flip_ef2_8 : SS.bxor z8 ef2 = y9 := by decide
theorem flip_ef2_9 : SS.bxor z9 ef2 = y8 := by decide
theorem flip_ef2_10 : SS.bxor z10 ef2 = y11 := by decide
theorem flip_ef2_11 : SS.bxor z11 ef2 = y10 := by decide
theorem flip_ef2_12 : SS.bxor z12 ef2 = y13 := by decide
theorem flip_ef2_13 : SS.bxor z13 ef2 = y12 := by decide
theorem flip_ef2_14 : SS.bxor z14 ef2 = y15 := by decide
theorem flip_ef2_15 : SS.bxor z15 ef2 = y14 := by decide
theorem sg_ef2_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg_ef2_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg_ef2_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg_ef2_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg_ef2_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg_ef2_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg_ef2_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg_ef2_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg_ef2_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_ef2_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg_ef2_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg_ef2_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg_ef2_w0_12 : SS.bdot w0 z12 = false := by decide
theorem sg_ef2_w0_13 : SS.bdot w0 z13 = false := by decide
theorem sg_ef2_w0_14 : SS.bdot w0 z14 = false := by decide
theorem sg_ef2_w0_15 : SS.bdot w0 z15 = false := by decide
theorem ex_ef2_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w0 = star (c y1) * d z0 + star (c y0) * d z1 + star (c y3) * d z2 + star (c y2) * d z3 + star (c y5) * d z4 + star (c y4) * d z5 + star (c y7) * d z6 + star (c y6) * d z7 + star (c y9) * d z8 + star (c y8) * d z9 + star (c y11) * d z10 + star (c y10) * d z11 + star (c y13) * d z12 + star (c y12) * d z13 + star (c y15) * d z14 + star (c y14) * d z15 := by
  unfold offSum
  rw [incidence_ef2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef2_0, flip_ef2_1, flip_ef2_2, flip_ef2_3, flip_ef2_4, flip_ef2_5, flip_ef2_6, flip_ef2_7, flip_ef2_8, flip_ef2_9, flip_ef2_10, flip_ef2_11, flip_ef2_12, flip_ef2_13, flip_ef2_14, flip_ef2_15]
  simp only [sg_ef2_w0_0, sg_ef2_w0_1, sg_ef2_w0_2, sg_ef2_w0_3, sg_ef2_w0_4, sg_ef2_w0_5, sg_ef2_w0_6, sg_ef2_w0_7, sg_ef2_w0_8, sg_ef2_w0_9, sg_ef2_w0_10, sg_ef2_w0_11, sg_ef2_w0_12, sg_ef2_w0_13, sg_ef2_w0_14, sg_ef2_w0_15, SixQubit.signMul_false]
  try ring
theorem sg_ef2_w1_0 : SS.bdot w1 z0 = true := by decide
theorem sg_ef2_w1_1 : SS.bdot w1 z1 = false := by decide
theorem sg_ef2_w1_2 : SS.bdot w1 z2 = false := by decide
theorem sg_ef2_w1_3 : SS.bdot w1 z3 = true := by decide
theorem sg_ef2_w1_4 : SS.bdot w1 z4 = false := by decide
theorem sg_ef2_w1_5 : SS.bdot w1 z5 = true := by decide
theorem sg_ef2_w1_6 : SS.bdot w1 z6 = true := by decide
theorem sg_ef2_w1_7 : SS.bdot w1 z7 = false := by decide
theorem sg_ef2_w1_8 : SS.bdot w1 z8 = true := by decide
theorem sg_ef2_w1_9 : SS.bdot w1 z9 = false := by decide
theorem sg_ef2_w1_10 : SS.bdot w1 z10 = false := by decide
theorem sg_ef2_w1_11 : SS.bdot w1 z11 = true := by decide
theorem sg_ef2_w1_12 : SS.bdot w1 z12 = false := by decide
theorem sg_ef2_w1_13 : SS.bdot w1 z13 = true := by decide
theorem sg_ef2_w1_14 : SS.bdot w1 z14 = true := by decide
theorem sg_ef2_w1_15 : SS.bdot w1 z15 = false := by decide
theorem ex_ef2_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w1 = - star (c y1) * d z0 + star (c y0) * d z1 + star (c y3) * d z2 - star (c y2) * d z3 + star (c y5) * d z4 - star (c y4) * d z5 - star (c y7) * d z6 + star (c y6) * d z7 - star (c y9) * d z8 + star (c y8) * d z9 + star (c y11) * d z10 - star (c y10) * d z11 + star (c y13) * d z12 - star (c y12) * d z13 - star (c y15) * d z14 + star (c y14) * d z15 := by
  unfold offSum
  rw [incidence_ef2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef2_0, flip_ef2_1, flip_ef2_2, flip_ef2_3, flip_ef2_4, flip_ef2_5, flip_ef2_6, flip_ef2_7, flip_ef2_8, flip_ef2_9, flip_ef2_10, flip_ef2_11, flip_ef2_12, flip_ef2_13, flip_ef2_14, flip_ef2_15]
  simp only [sg_ef2_w1_0, sg_ef2_w1_1, sg_ef2_w1_2, sg_ef2_w1_3, sg_ef2_w1_4, sg_ef2_w1_5, sg_ef2_w1_6, sg_ef2_w1_7, sg_ef2_w1_8, sg_ef2_w1_9, sg_ef2_w1_10, sg_ef2_w1_11, sg_ef2_w1_12, sg_ef2_w1_13, sg_ef2_w1_14, sg_ef2_w1_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef2_w2_0 : SS.bdot w2 z0 = false := by decide
theorem sg_ef2_w2_1 : SS.bdot w2 z1 = true := by decide
theorem sg_ef2_w2_2 : SS.bdot w2 z2 = false := by decide
theorem sg_ef2_w2_3 : SS.bdot w2 z3 = true := by decide
theorem sg_ef2_w2_4 : SS.bdot w2 z4 = false := by decide
theorem sg_ef2_w2_5 : SS.bdot w2 z5 = true := by decide
theorem sg_ef2_w2_6 : SS.bdot w2 z6 = false := by decide
theorem sg_ef2_w2_7 : SS.bdot w2 z7 = true := by decide
theorem sg_ef2_w2_8 : SS.bdot w2 z8 = false := by decide
theorem sg_ef2_w2_9 : SS.bdot w2 z9 = true := by decide
theorem sg_ef2_w2_10 : SS.bdot w2 z10 = false := by decide
theorem sg_ef2_w2_11 : SS.bdot w2 z11 = true := by decide
theorem sg_ef2_w2_12 : SS.bdot w2 z12 = false := by decide
theorem sg_ef2_w2_13 : SS.bdot w2 z13 = true := by decide
theorem sg_ef2_w2_14 : SS.bdot w2 z14 = false := by decide
theorem sg_ef2_w2_15 : SS.bdot w2 z15 = true := by decide
theorem ex_ef2_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w2 = star (c y1) * d z0 - star (c y0) * d z1 + star (c y3) * d z2 - star (c y2) * d z3 + star (c y5) * d z4 - star (c y4) * d z5 + star (c y7) * d z6 - star (c y6) * d z7 + star (c y9) * d z8 - star (c y8) * d z9 + star (c y11) * d z10 - star (c y10) * d z11 + star (c y13) * d z12 - star (c y12) * d z13 + star (c y15) * d z14 - star (c y14) * d z15 := by
  unfold offSum
  rw [incidence_ef2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef2_0, flip_ef2_1, flip_ef2_2, flip_ef2_3, flip_ef2_4, flip_ef2_5, flip_ef2_6, flip_ef2_7, flip_ef2_8, flip_ef2_9, flip_ef2_10, flip_ef2_11, flip_ef2_12, flip_ef2_13, flip_ef2_14, flip_ef2_15]
  simp only [sg_ef2_w2_0, sg_ef2_w2_1, sg_ef2_w2_2, sg_ef2_w2_3, sg_ef2_w2_4, sg_ef2_w2_5, sg_ef2_w2_6, sg_ef2_w2_7, sg_ef2_w2_8, sg_ef2_w2_9, sg_ef2_w2_10, sg_ef2_w2_11, sg_ef2_w2_12, sg_ef2_w2_13, sg_ef2_w2_14, sg_ef2_w2_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef2_w3_0 : SS.bdot w3 z0 = true := by decide
theorem sg_ef2_w3_1 : SS.bdot w3 z1 = true := by decide
theorem sg_ef2_w3_2 : SS.bdot w3 z2 = false := by decide
theorem sg_ef2_w3_3 : SS.bdot w3 z3 = false := by decide
theorem sg_ef2_w3_4 : SS.bdot w3 z4 = false := by decide
theorem sg_ef2_w3_5 : SS.bdot w3 z5 = false := by decide
theorem sg_ef2_w3_6 : SS.bdot w3 z6 = true := by decide
theorem sg_ef2_w3_7 : SS.bdot w3 z7 = true := by decide
theorem sg_ef2_w3_8 : SS.bdot w3 z8 = true := by decide
theorem sg_ef2_w3_9 : SS.bdot w3 z9 = true := by decide
theorem sg_ef2_w3_10 : SS.bdot w3 z10 = false := by decide
theorem sg_ef2_w3_11 : SS.bdot w3 z11 = false := by decide
theorem sg_ef2_w3_12 : SS.bdot w3 z12 = false := by decide
theorem sg_ef2_w3_13 : SS.bdot w3 z13 = false := by decide
theorem sg_ef2_w3_14 : SS.bdot w3 z14 = true := by decide
theorem sg_ef2_w3_15 : SS.bdot w3 z15 = true := by decide
theorem ex_ef2_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w3 = - star (c y1) * d z0 - star (c y0) * d z1 + star (c y3) * d z2 + star (c y2) * d z3 + star (c y5) * d z4 + star (c y4) * d z5 - star (c y7) * d z6 - star (c y6) * d z7 - star (c y9) * d z8 - star (c y8) * d z9 + star (c y11) * d z10 + star (c y10) * d z11 + star (c y13) * d z12 + star (c y12) * d z13 - star (c y15) * d z14 - star (c y14) * d z15 := by
  unfold offSum
  rw [incidence_ef2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef2_0, flip_ef2_1, flip_ef2_2, flip_ef2_3, flip_ef2_4, flip_ef2_5, flip_ef2_6, flip_ef2_7, flip_ef2_8, flip_ef2_9, flip_ef2_10, flip_ef2_11, flip_ef2_12, flip_ef2_13, flip_ef2_14, flip_ef2_15]
  simp only [sg_ef2_w3_0, sg_ef2_w3_1, sg_ef2_w3_2, sg_ef2_w3_3, sg_ef2_w3_4, sg_ef2_w3_5, sg_ef2_w3_6, sg_ef2_w3_7, sg_ef2_w3_8, sg_ef2_w3_9, sg_ef2_w3_10, sg_ef2_w3_11, sg_ef2_w3_12, sg_ef2_w3_13, sg_ef2_w3_14, sg_ef2_w3_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef2_w4_0 : SS.bdot w4 z0 = false := by decide
theorem sg_ef2_w4_1 : SS.bdot w4 z1 = false := by decide
theorem sg_ef2_w4_2 : SS.bdot w4 z2 = true := by decide
theorem sg_ef2_w4_3 : SS.bdot w4 z3 = true := by decide
theorem sg_ef2_w4_4 : SS.bdot w4 z4 = false := by decide
theorem sg_ef2_w4_5 : SS.bdot w4 z5 = false := by decide
theorem sg_ef2_w4_6 : SS.bdot w4 z6 = true := by decide
theorem sg_ef2_w4_7 : SS.bdot w4 z7 = true := by decide
theorem sg_ef2_w4_8 : SS.bdot w4 z8 = false := by decide
theorem sg_ef2_w4_9 : SS.bdot w4 z9 = false := by decide
theorem sg_ef2_w4_10 : SS.bdot w4 z10 = true := by decide
theorem sg_ef2_w4_11 : SS.bdot w4 z11 = true := by decide
theorem sg_ef2_w4_12 : SS.bdot w4 z12 = false := by decide
theorem sg_ef2_w4_13 : SS.bdot w4 z13 = false := by decide
theorem sg_ef2_w4_14 : SS.bdot w4 z14 = true := by decide
theorem sg_ef2_w4_15 : SS.bdot w4 z15 = true := by decide
theorem ex_ef2_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w4 = star (c y1) * d z0 + star (c y0) * d z1 - star (c y3) * d z2 - star (c y2) * d z3 + star (c y5) * d z4 + star (c y4) * d z5 - star (c y7) * d z6 - star (c y6) * d z7 + star (c y9) * d z8 + star (c y8) * d z9 - star (c y11) * d z10 - star (c y10) * d z11 + star (c y13) * d z12 + star (c y12) * d z13 - star (c y15) * d z14 - star (c y14) * d z15 := by
  unfold offSum
  rw [incidence_ef2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef2_0, flip_ef2_1, flip_ef2_2, flip_ef2_3, flip_ef2_4, flip_ef2_5, flip_ef2_6, flip_ef2_7, flip_ef2_8, flip_ef2_9, flip_ef2_10, flip_ef2_11, flip_ef2_12, flip_ef2_13, flip_ef2_14, flip_ef2_15]
  simp only [sg_ef2_w4_0, sg_ef2_w4_1, sg_ef2_w4_2, sg_ef2_w4_3, sg_ef2_w4_4, sg_ef2_w4_5, sg_ef2_w4_6, sg_ef2_w4_7, sg_ef2_w4_8, sg_ef2_w4_9, sg_ef2_w4_10, sg_ef2_w4_11, sg_ef2_w4_12, sg_ef2_w4_13, sg_ef2_w4_14, sg_ef2_w4_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef2_w6_0 : SS.bdot w6 z0 = false := by decide
theorem sg_ef2_w6_1 : SS.bdot w6 z1 = true := by decide
theorem sg_ef2_w6_2 : SS.bdot w6 z2 = true := by decide
theorem sg_ef2_w6_3 : SS.bdot w6 z3 = false := by decide
theorem sg_ef2_w6_4 : SS.bdot w6 z4 = false := by decide
theorem sg_ef2_w6_5 : SS.bdot w6 z5 = true := by decide
theorem sg_ef2_w6_6 : SS.bdot w6 z6 = true := by decide
theorem sg_ef2_w6_7 : SS.bdot w6 z7 = false := by decide
theorem sg_ef2_w6_8 : SS.bdot w6 z8 = false := by decide
theorem sg_ef2_w6_9 : SS.bdot w6 z9 = true := by decide
theorem sg_ef2_w6_10 : SS.bdot w6 z10 = true := by decide
theorem sg_ef2_w6_11 : SS.bdot w6 z11 = false := by decide
theorem sg_ef2_w6_12 : SS.bdot w6 z12 = false := by decide
theorem sg_ef2_w6_13 : SS.bdot w6 z13 = true := by decide
theorem sg_ef2_w6_14 : SS.bdot w6 z14 = true := by decide
theorem sg_ef2_w6_15 : SS.bdot w6 z15 = false := by decide
theorem ex_ef2_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w6 = star (c y1) * d z0 - star (c y0) * d z1 - star (c y3) * d z2 + star (c y2) * d z3 + star (c y5) * d z4 - star (c y4) * d z5 - star (c y7) * d z6 + star (c y6) * d z7 + star (c y9) * d z8 - star (c y8) * d z9 - star (c y11) * d z10 + star (c y10) * d z11 + star (c y13) * d z12 - star (c y12) * d z13 - star (c y15) * d z14 + star (c y14) * d z15 := by
  unfold offSum
  rw [incidence_ef2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef2_0, flip_ef2_1, flip_ef2_2, flip_ef2_3, flip_ef2_4, flip_ef2_5, flip_ef2_6, flip_ef2_7, flip_ef2_8, flip_ef2_9, flip_ef2_10, flip_ef2_11, flip_ef2_12, flip_ef2_13, flip_ef2_14, flip_ef2_15]
  simp only [sg_ef2_w6_0, sg_ef2_w6_1, sg_ef2_w6_2, sg_ef2_w6_3, sg_ef2_w6_4, sg_ef2_w6_5, sg_ef2_w6_6, sg_ef2_w6_7, sg_ef2_w6_8, sg_ef2_w6_9, sg_ef2_w6_10, sg_ef2_w6_11, sg_ef2_w6_12, sg_ef2_w6_13, sg_ef2_w6_14, sg_ef2_w6_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef2_w7_0 : SS.bdot w7 z0 = false := by decide
theorem sg_ef2_w7_1 : SS.bdot w7 z1 = false := by decide
theorem sg_ef2_w7_2 : SS.bdot w7 z2 = false := by decide
theorem sg_ef2_w7_3 : SS.bdot w7 z3 = false := by decide
theorem sg_ef2_w7_4 : SS.bdot w7 z4 = true := by decide
theorem sg_ef2_w7_5 : SS.bdot w7 z5 = true := by decide
theorem sg_ef2_w7_6 : SS.bdot w7 z6 = true := by decide
theorem sg_ef2_w7_7 : SS.bdot w7 z7 = true := by decide
theorem sg_ef2_w7_8 : SS.bdot w7 z8 = false := by decide
theorem sg_ef2_w7_9 : SS.bdot w7 z9 = false := by decide
theorem sg_ef2_w7_10 : SS.bdot w7 z10 = false := by decide
theorem sg_ef2_w7_11 : SS.bdot w7 z11 = false := by decide
theorem sg_ef2_w7_12 : SS.bdot w7 z12 = true := by decide
theorem sg_ef2_w7_13 : SS.bdot w7 z13 = true := by decide
theorem sg_ef2_w7_14 : SS.bdot w7 z14 = true := by decide
theorem sg_ef2_w7_15 : SS.bdot w7 z15 = true := by decide
theorem ex_ef2_w7 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w7 = star (c y1) * d z0 + star (c y0) * d z1 + star (c y3) * d z2 + star (c y2) * d z3 - star (c y5) * d z4 - star (c y4) * d z5 - star (c y7) * d z6 - star (c y6) * d z7 + star (c y9) * d z8 + star (c y8) * d z9 + star (c y11) * d z10 + star (c y10) * d z11 - star (c y13) * d z12 - star (c y12) * d z13 - star (c y15) * d z14 - star (c y14) * d z15 := by
  unfold offSum
  rw [incidence_ef2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef2_0, flip_ef2_1, flip_ef2_2, flip_ef2_3, flip_ef2_4, flip_ef2_5, flip_ef2_6, flip_ef2_7, flip_ef2_8, flip_ef2_9, flip_ef2_10, flip_ef2_11, flip_ef2_12, flip_ef2_13, flip_ef2_14, flip_ef2_15]
  simp only [sg_ef2_w7_0, sg_ef2_w7_1, sg_ef2_w7_2, sg_ef2_w7_3, sg_ef2_w7_4, sg_ef2_w7_5, sg_ef2_w7_6, sg_ef2_w7_7, sg_ef2_w7_8, sg_ef2_w7_9, sg_ef2_w7_10, sg_ef2_w7_11, sg_ef2_w7_12, sg_ef2_w7_13, sg_ef2_w7_14, sg_ef2_w7_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef2_w9_0 : SS.bdot w9 z0 = false := by decide
theorem sg_ef2_w9_1 : SS.bdot w9 z1 = true := by decide
theorem sg_ef2_w9_2 : SS.bdot w9 z2 = false := by decide
theorem sg_ef2_w9_3 : SS.bdot w9 z3 = true := by decide
theorem sg_ef2_w9_4 : SS.bdot w9 z4 = true := by decide
theorem sg_ef2_w9_5 : SS.bdot w9 z5 = false := by decide
theorem sg_ef2_w9_6 : SS.bdot w9 z6 = true := by decide
theorem sg_ef2_w9_7 : SS.bdot w9 z7 = false := by decide
theorem sg_ef2_w9_8 : SS.bdot w9 z8 = false := by decide
theorem sg_ef2_w9_9 : SS.bdot w9 z9 = true := by decide
theorem sg_ef2_w9_10 : SS.bdot w9 z10 = false := by decide
theorem sg_ef2_w9_11 : SS.bdot w9 z11 = true := by decide
theorem sg_ef2_w9_12 : SS.bdot w9 z12 = true := by decide
theorem sg_ef2_w9_13 : SS.bdot w9 z13 = false := by decide
theorem sg_ef2_w9_14 : SS.bdot w9 z14 = true := by decide
theorem sg_ef2_w9_15 : SS.bdot w9 z15 = false := by decide
theorem ex_ef2_w9 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w9 = star (c y1) * d z0 - star (c y0) * d z1 + star (c y3) * d z2 - star (c y2) * d z3 - star (c y5) * d z4 + star (c y4) * d z5 - star (c y7) * d z6 + star (c y6) * d z7 + star (c y9) * d z8 - star (c y8) * d z9 + star (c y11) * d z10 - star (c y10) * d z11 - star (c y13) * d z12 + star (c y12) * d z13 - star (c y15) * d z14 + star (c y14) * d z15 := by
  unfold offSum
  rw [incidence_ef2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef2_0, flip_ef2_1, flip_ef2_2, flip_ef2_3, flip_ef2_4, flip_ef2_5, flip_ef2_6, flip_ef2_7, flip_ef2_8, flip_ef2_9, flip_ef2_10, flip_ef2_11, flip_ef2_12, flip_ef2_13, flip_ef2_14, flip_ef2_15]
  simp only [sg_ef2_w9_0, sg_ef2_w9_1, sg_ef2_w9_2, sg_ef2_w9_3, sg_ef2_w9_4, sg_ef2_w9_5, sg_ef2_w9_6, sg_ef2_w9_7, sg_ef2_w9_8, sg_ef2_w9_9, sg_ef2_w9_10, sg_ef2_w9_11, sg_ef2_w9_12, sg_ef2_w9_13, sg_ef2_w9_14, sg_ef2_w9_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem incidence_ef3 :
    S1.filter (fun y => SS.bxor y ef3 ∈ S0) = {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15} := by decide
theorem flip_ef3_0 : SS.bxor z0 ef3 = y0 := by decide
theorem flip_ef3_1 : SS.bxor z1 ef3 = y1 := by decide
theorem flip_ef3_2 : SS.bxor z2 ef3 = y2 := by decide
theorem flip_ef3_3 : SS.bxor z3 ef3 = y3 := by decide
theorem flip_ef3_4 : SS.bxor z4 ef3 = y4 := by decide
theorem flip_ef3_5 : SS.bxor z5 ef3 = y5 := by decide
theorem flip_ef3_6 : SS.bxor z6 ef3 = y6 := by decide
theorem flip_ef3_7 : SS.bxor z7 ef3 = y7 := by decide
theorem flip_ef3_8 : SS.bxor z8 ef3 = y8 := by decide
theorem flip_ef3_9 : SS.bxor z9 ef3 = y9 := by decide
theorem flip_ef3_10 : SS.bxor z10 ef3 = y10 := by decide
theorem flip_ef3_11 : SS.bxor z11 ef3 = y11 := by decide
theorem flip_ef3_12 : SS.bxor z12 ef3 = y12 := by decide
theorem flip_ef3_13 : SS.bxor z13 ef3 = y13 := by decide
theorem flip_ef3_14 : SS.bxor z14 ef3 = y14 := by decide
theorem flip_ef3_15 : SS.bxor z15 ef3 = y15 := by decide
theorem sg_ef3_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg_ef3_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg_ef3_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg_ef3_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg_ef3_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg_ef3_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg_ef3_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg_ef3_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg_ef3_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_ef3_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg_ef3_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg_ef3_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg_ef3_w0_12 : SS.bdot w0 z12 = false := by decide
theorem sg_ef3_w0_13 : SS.bdot w0 z13 = false := by decide
theorem sg_ef3_w0_14 : SS.bdot w0 z14 = false := by decide
theorem sg_ef3_w0_15 : SS.bdot w0 z15 = false := by decide
theorem ex_ef3_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w0 = star (c y0) * d z0 + star (c y1) * d z1 + star (c y2) * d z2 + star (c y3) * d z3 + star (c y4) * d z4 + star (c y5) * d z5 + star (c y6) * d z6 + star (c y7) * d z7 + star (c y8) * d z8 + star (c y9) * d z9 + star (c y10) * d z10 + star (c y11) * d z11 + star (c y12) * d z12 + star (c y13) * d z13 + star (c y14) * d z14 + star (c y15) * d z15 := by
  unfold offSum
  rw [incidence_ef3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef3_0, flip_ef3_1, flip_ef3_2, flip_ef3_3, flip_ef3_4, flip_ef3_5, flip_ef3_6, flip_ef3_7, flip_ef3_8, flip_ef3_9, flip_ef3_10, flip_ef3_11, flip_ef3_12, flip_ef3_13, flip_ef3_14, flip_ef3_15]
  simp only [sg_ef3_w0_0, sg_ef3_w0_1, sg_ef3_w0_2, sg_ef3_w0_3, sg_ef3_w0_4, sg_ef3_w0_5, sg_ef3_w0_6, sg_ef3_w0_7, sg_ef3_w0_8, sg_ef3_w0_9, sg_ef3_w0_10, sg_ef3_w0_11, sg_ef3_w0_12, sg_ef3_w0_13, sg_ef3_w0_14, sg_ef3_w0_15, SixQubit.signMul_false]
  try ring
theorem sg_ef3_w1_0 : SS.bdot w1 z0 = true := by decide
theorem sg_ef3_w1_1 : SS.bdot w1 z1 = false := by decide
theorem sg_ef3_w1_2 : SS.bdot w1 z2 = false := by decide
theorem sg_ef3_w1_3 : SS.bdot w1 z3 = true := by decide
theorem sg_ef3_w1_4 : SS.bdot w1 z4 = false := by decide
theorem sg_ef3_w1_5 : SS.bdot w1 z5 = true := by decide
theorem sg_ef3_w1_6 : SS.bdot w1 z6 = true := by decide
theorem sg_ef3_w1_7 : SS.bdot w1 z7 = false := by decide
theorem sg_ef3_w1_8 : SS.bdot w1 z8 = true := by decide
theorem sg_ef3_w1_9 : SS.bdot w1 z9 = false := by decide
theorem sg_ef3_w1_10 : SS.bdot w1 z10 = false := by decide
theorem sg_ef3_w1_11 : SS.bdot w1 z11 = true := by decide
theorem sg_ef3_w1_12 : SS.bdot w1 z12 = false := by decide
theorem sg_ef3_w1_13 : SS.bdot w1 z13 = true := by decide
theorem sg_ef3_w1_14 : SS.bdot w1 z14 = true := by decide
theorem sg_ef3_w1_15 : SS.bdot w1 z15 = false := by decide
theorem ex_ef3_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w1 = - star (c y0) * d z0 + star (c y1) * d z1 + star (c y2) * d z2 - star (c y3) * d z3 + star (c y4) * d z4 - star (c y5) * d z5 - star (c y6) * d z6 + star (c y7) * d z7 - star (c y8) * d z8 + star (c y9) * d z9 + star (c y10) * d z10 - star (c y11) * d z11 + star (c y12) * d z12 - star (c y13) * d z13 - star (c y14) * d z14 + star (c y15) * d z15 := by
  unfold offSum
  rw [incidence_ef3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef3_0, flip_ef3_1, flip_ef3_2, flip_ef3_3, flip_ef3_4, flip_ef3_5, flip_ef3_6, flip_ef3_7, flip_ef3_8, flip_ef3_9, flip_ef3_10, flip_ef3_11, flip_ef3_12, flip_ef3_13, flip_ef3_14, flip_ef3_15]
  simp only [sg_ef3_w1_0, sg_ef3_w1_1, sg_ef3_w1_2, sg_ef3_w1_3, sg_ef3_w1_4, sg_ef3_w1_5, sg_ef3_w1_6, sg_ef3_w1_7, sg_ef3_w1_8, sg_ef3_w1_9, sg_ef3_w1_10, sg_ef3_w1_11, sg_ef3_w1_12, sg_ef3_w1_13, sg_ef3_w1_14, sg_ef3_w1_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef3_w2_0 : SS.bdot w2 z0 = false := by decide
theorem sg_ef3_w2_1 : SS.bdot w2 z1 = true := by decide
theorem sg_ef3_w2_2 : SS.bdot w2 z2 = false := by decide
theorem sg_ef3_w2_3 : SS.bdot w2 z3 = true := by decide
theorem sg_ef3_w2_4 : SS.bdot w2 z4 = false := by decide
theorem sg_ef3_w2_5 : SS.bdot w2 z5 = true := by decide
theorem sg_ef3_w2_6 : SS.bdot w2 z6 = false := by decide
theorem sg_ef3_w2_7 : SS.bdot w2 z7 = true := by decide
theorem sg_ef3_w2_8 : SS.bdot w2 z8 = false := by decide
theorem sg_ef3_w2_9 : SS.bdot w2 z9 = true := by decide
theorem sg_ef3_w2_10 : SS.bdot w2 z10 = false := by decide
theorem sg_ef3_w2_11 : SS.bdot w2 z11 = true := by decide
theorem sg_ef3_w2_12 : SS.bdot w2 z12 = false := by decide
theorem sg_ef3_w2_13 : SS.bdot w2 z13 = true := by decide
theorem sg_ef3_w2_14 : SS.bdot w2 z14 = false := by decide
theorem sg_ef3_w2_15 : SS.bdot w2 z15 = true := by decide
theorem ex_ef3_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w2 = star (c y0) * d z0 - star (c y1) * d z1 + star (c y2) * d z2 - star (c y3) * d z3 + star (c y4) * d z4 - star (c y5) * d z5 + star (c y6) * d z6 - star (c y7) * d z7 + star (c y8) * d z8 - star (c y9) * d z9 + star (c y10) * d z10 - star (c y11) * d z11 + star (c y12) * d z12 - star (c y13) * d z13 + star (c y14) * d z14 - star (c y15) * d z15 := by
  unfold offSum
  rw [incidence_ef3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef3_0, flip_ef3_1, flip_ef3_2, flip_ef3_3, flip_ef3_4, flip_ef3_5, flip_ef3_6, flip_ef3_7, flip_ef3_8, flip_ef3_9, flip_ef3_10, flip_ef3_11, flip_ef3_12, flip_ef3_13, flip_ef3_14, flip_ef3_15]
  simp only [sg_ef3_w2_0, sg_ef3_w2_1, sg_ef3_w2_2, sg_ef3_w2_3, sg_ef3_w2_4, sg_ef3_w2_5, sg_ef3_w2_6, sg_ef3_w2_7, sg_ef3_w2_8, sg_ef3_w2_9, sg_ef3_w2_10, sg_ef3_w2_11, sg_ef3_w2_12, sg_ef3_w2_13, sg_ef3_w2_14, sg_ef3_w2_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef3_w3_0 : SS.bdot w3 z0 = true := by decide
theorem sg_ef3_w3_1 : SS.bdot w3 z1 = true := by decide
theorem sg_ef3_w3_2 : SS.bdot w3 z2 = false := by decide
theorem sg_ef3_w3_3 : SS.bdot w3 z3 = false := by decide
theorem sg_ef3_w3_4 : SS.bdot w3 z4 = false := by decide
theorem sg_ef3_w3_5 : SS.bdot w3 z5 = false := by decide
theorem sg_ef3_w3_6 : SS.bdot w3 z6 = true := by decide
theorem sg_ef3_w3_7 : SS.bdot w3 z7 = true := by decide
theorem sg_ef3_w3_8 : SS.bdot w3 z8 = true := by decide
theorem sg_ef3_w3_9 : SS.bdot w3 z9 = true := by decide
theorem sg_ef3_w3_10 : SS.bdot w3 z10 = false := by decide
theorem sg_ef3_w3_11 : SS.bdot w3 z11 = false := by decide
theorem sg_ef3_w3_12 : SS.bdot w3 z12 = false := by decide
theorem sg_ef3_w3_13 : SS.bdot w3 z13 = false := by decide
theorem sg_ef3_w3_14 : SS.bdot w3 z14 = true := by decide
theorem sg_ef3_w3_15 : SS.bdot w3 z15 = true := by decide
theorem ex_ef3_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w3 = - star (c y0) * d z0 - star (c y1) * d z1 + star (c y2) * d z2 + star (c y3) * d z3 + star (c y4) * d z4 + star (c y5) * d z5 - star (c y6) * d z6 - star (c y7) * d z7 - star (c y8) * d z8 - star (c y9) * d z9 + star (c y10) * d z10 + star (c y11) * d z11 + star (c y12) * d z12 + star (c y13) * d z13 - star (c y14) * d z14 - star (c y15) * d z15 := by
  unfold offSum
  rw [incidence_ef3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef3_0, flip_ef3_1, flip_ef3_2, flip_ef3_3, flip_ef3_4, flip_ef3_5, flip_ef3_6, flip_ef3_7, flip_ef3_8, flip_ef3_9, flip_ef3_10, flip_ef3_11, flip_ef3_12, flip_ef3_13, flip_ef3_14, flip_ef3_15]
  simp only [sg_ef3_w3_0, sg_ef3_w3_1, sg_ef3_w3_2, sg_ef3_w3_3, sg_ef3_w3_4, sg_ef3_w3_5, sg_ef3_w3_6, sg_ef3_w3_7, sg_ef3_w3_8, sg_ef3_w3_9, sg_ef3_w3_10, sg_ef3_w3_11, sg_ef3_w3_12, sg_ef3_w3_13, sg_ef3_w3_14, sg_ef3_w3_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef3_w4_0 : SS.bdot w4 z0 = false := by decide
theorem sg_ef3_w4_1 : SS.bdot w4 z1 = false := by decide
theorem sg_ef3_w4_2 : SS.bdot w4 z2 = true := by decide
theorem sg_ef3_w4_3 : SS.bdot w4 z3 = true := by decide
theorem sg_ef3_w4_4 : SS.bdot w4 z4 = false := by decide
theorem sg_ef3_w4_5 : SS.bdot w4 z5 = false := by decide
theorem sg_ef3_w4_6 : SS.bdot w4 z6 = true := by decide
theorem sg_ef3_w4_7 : SS.bdot w4 z7 = true := by decide
theorem sg_ef3_w4_8 : SS.bdot w4 z8 = false := by decide
theorem sg_ef3_w4_9 : SS.bdot w4 z9 = false := by decide
theorem sg_ef3_w4_10 : SS.bdot w4 z10 = true := by decide
theorem sg_ef3_w4_11 : SS.bdot w4 z11 = true := by decide
theorem sg_ef3_w4_12 : SS.bdot w4 z12 = false := by decide
theorem sg_ef3_w4_13 : SS.bdot w4 z13 = false := by decide
theorem sg_ef3_w4_14 : SS.bdot w4 z14 = true := by decide
theorem sg_ef3_w4_15 : SS.bdot w4 z15 = true := by decide
theorem ex_ef3_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w4 = star (c y0) * d z0 + star (c y1) * d z1 - star (c y2) * d z2 - star (c y3) * d z3 + star (c y4) * d z4 + star (c y5) * d z5 - star (c y6) * d z6 - star (c y7) * d z7 + star (c y8) * d z8 + star (c y9) * d z9 - star (c y10) * d z10 - star (c y11) * d z11 + star (c y12) * d z12 + star (c y13) * d z13 - star (c y14) * d z14 - star (c y15) * d z15 := by
  unfold offSum
  rw [incidence_ef3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef3_0, flip_ef3_1, flip_ef3_2, flip_ef3_3, flip_ef3_4, flip_ef3_5, flip_ef3_6, flip_ef3_7, flip_ef3_8, flip_ef3_9, flip_ef3_10, flip_ef3_11, flip_ef3_12, flip_ef3_13, flip_ef3_14, flip_ef3_15]
  simp only [sg_ef3_w4_0, sg_ef3_w4_1, sg_ef3_w4_2, sg_ef3_w4_3, sg_ef3_w4_4, sg_ef3_w4_5, sg_ef3_w4_6, sg_ef3_w4_7, sg_ef3_w4_8, sg_ef3_w4_9, sg_ef3_w4_10, sg_ef3_w4_11, sg_ef3_w4_12, sg_ef3_w4_13, sg_ef3_w4_14, sg_ef3_w4_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef3_w5_0 : SS.bdot w5 z0 = true := by decide
theorem sg_ef3_w5_1 : SS.bdot w5 z1 = false := by decide
theorem sg_ef3_w5_2 : SS.bdot w5 z2 = true := by decide
theorem sg_ef3_w5_3 : SS.bdot w5 z3 = false := by decide
theorem sg_ef3_w5_4 : SS.bdot w5 z4 = false := by decide
theorem sg_ef3_w5_5 : SS.bdot w5 z5 = true := by decide
theorem sg_ef3_w5_6 : SS.bdot w5 z6 = false := by decide
theorem sg_ef3_w5_7 : SS.bdot w5 z7 = true := by decide
theorem sg_ef3_w5_8 : SS.bdot w5 z8 = true := by decide
theorem sg_ef3_w5_9 : SS.bdot w5 z9 = false := by decide
theorem sg_ef3_w5_10 : SS.bdot w5 z10 = true := by decide
theorem sg_ef3_w5_11 : SS.bdot w5 z11 = false := by decide
theorem sg_ef3_w5_12 : SS.bdot w5 z12 = false := by decide
theorem sg_ef3_w5_13 : SS.bdot w5 z13 = true := by decide
theorem sg_ef3_w5_14 : SS.bdot w5 z14 = false := by decide
theorem sg_ef3_w5_15 : SS.bdot w5 z15 = true := by decide
theorem ex_ef3_w5 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w5 = - star (c y0) * d z0 + star (c y1) * d z1 - star (c y2) * d z2 + star (c y3) * d z3 + star (c y4) * d z4 - star (c y5) * d z5 + star (c y6) * d z6 - star (c y7) * d z7 - star (c y8) * d z8 + star (c y9) * d z9 - star (c y10) * d z10 + star (c y11) * d z11 + star (c y12) * d z12 - star (c y13) * d z13 + star (c y14) * d z14 - star (c y15) * d z15 := by
  unfold offSum
  rw [incidence_ef3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef3_0, flip_ef3_1, flip_ef3_2, flip_ef3_3, flip_ef3_4, flip_ef3_5, flip_ef3_6, flip_ef3_7, flip_ef3_8, flip_ef3_9, flip_ef3_10, flip_ef3_11, flip_ef3_12, flip_ef3_13, flip_ef3_14, flip_ef3_15]
  simp only [sg_ef3_w5_0, sg_ef3_w5_1, sg_ef3_w5_2, sg_ef3_w5_3, sg_ef3_w5_4, sg_ef3_w5_5, sg_ef3_w5_6, sg_ef3_w5_7, sg_ef3_w5_8, sg_ef3_w5_9, sg_ef3_w5_10, sg_ef3_w5_11, sg_ef3_w5_12, sg_ef3_w5_13, sg_ef3_w5_14, sg_ef3_w5_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef3_w7_0 : SS.bdot w7 z0 = false := by decide
theorem sg_ef3_w7_1 : SS.bdot w7 z1 = false := by decide
theorem sg_ef3_w7_2 : SS.bdot w7 z2 = false := by decide
theorem sg_ef3_w7_3 : SS.bdot w7 z3 = false := by decide
theorem sg_ef3_w7_4 : SS.bdot w7 z4 = true := by decide
theorem sg_ef3_w7_5 : SS.bdot w7 z5 = true := by decide
theorem sg_ef3_w7_6 : SS.bdot w7 z6 = true := by decide
theorem sg_ef3_w7_7 : SS.bdot w7 z7 = true := by decide
theorem sg_ef3_w7_8 : SS.bdot w7 z8 = false := by decide
theorem sg_ef3_w7_9 : SS.bdot w7 z9 = false := by decide
theorem sg_ef3_w7_10 : SS.bdot w7 z10 = false := by decide
theorem sg_ef3_w7_11 : SS.bdot w7 z11 = false := by decide
theorem sg_ef3_w7_12 : SS.bdot w7 z12 = true := by decide
theorem sg_ef3_w7_13 : SS.bdot w7 z13 = true := by decide
theorem sg_ef3_w7_14 : SS.bdot w7 z14 = true := by decide
theorem sg_ef3_w7_15 : SS.bdot w7 z15 = true := by decide
theorem ex_ef3_w7 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w7 = star (c y0) * d z0 + star (c y1) * d z1 + star (c y2) * d z2 + star (c y3) * d z3 - star (c y4) * d z4 - star (c y5) * d z5 - star (c y6) * d z6 - star (c y7) * d z7 + star (c y8) * d z8 + star (c y9) * d z9 + star (c y10) * d z10 + star (c y11) * d z11 - star (c y12) * d z12 - star (c y13) * d z13 - star (c y14) * d z14 - star (c y15) * d z15 := by
  unfold offSum
  rw [incidence_ef3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef3_0, flip_ef3_1, flip_ef3_2, flip_ef3_3, flip_ef3_4, flip_ef3_5, flip_ef3_6, flip_ef3_7, flip_ef3_8, flip_ef3_9, flip_ef3_10, flip_ef3_11, flip_ef3_12, flip_ef3_13, flip_ef3_14, flip_ef3_15]
  simp only [sg_ef3_w7_0, sg_ef3_w7_1, sg_ef3_w7_2, sg_ef3_w7_3, sg_ef3_w7_4, sg_ef3_w7_5, sg_ef3_w7_6, sg_ef3_w7_7, sg_ef3_w7_8, sg_ef3_w7_9, sg_ef3_w7_10, sg_ef3_w7_11, sg_ef3_w7_12, sg_ef3_w7_13, sg_ef3_w7_14, sg_ef3_w7_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef3_w8_0 : SS.bdot w8 z0 = true := by decide
theorem sg_ef3_w8_1 : SS.bdot w8 z1 = false := by decide
theorem sg_ef3_w8_2 : SS.bdot w8 z2 = false := by decide
theorem sg_ef3_w8_3 : SS.bdot w8 z3 = true := by decide
theorem sg_ef3_w8_4 : SS.bdot w8 z4 = true := by decide
theorem sg_ef3_w8_5 : SS.bdot w8 z5 = false := by decide
theorem sg_ef3_w8_6 : SS.bdot w8 z6 = false := by decide
theorem sg_ef3_w8_7 : SS.bdot w8 z7 = true := by decide
theorem sg_ef3_w8_8 : SS.bdot w8 z8 = true := by decide
theorem sg_ef3_w8_9 : SS.bdot w8 z9 = false := by decide
theorem sg_ef3_w8_10 : SS.bdot w8 z10 = false := by decide
theorem sg_ef3_w8_11 : SS.bdot w8 z11 = true := by decide
theorem sg_ef3_w8_12 : SS.bdot w8 z12 = true := by decide
theorem sg_ef3_w8_13 : SS.bdot w8 z13 = false := by decide
theorem sg_ef3_w8_14 : SS.bdot w8 z14 = false := by decide
theorem sg_ef3_w8_15 : SS.bdot w8 z15 = true := by decide
theorem ex_ef3_w8 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w8 = - star (c y0) * d z0 + star (c y1) * d z1 + star (c y2) * d z2 - star (c y3) * d z3 - star (c y4) * d z4 + star (c y5) * d z5 + star (c y6) * d z6 - star (c y7) * d z7 - star (c y8) * d z8 + star (c y9) * d z9 + star (c y10) * d z10 - star (c y11) * d z11 - star (c y12) * d z12 + star (c y13) * d z13 + star (c y14) * d z14 - star (c y15) * d z15 := by
  unfold offSum
  rw [incidence_ef3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef3_0, flip_ef3_1, flip_ef3_2, flip_ef3_3, flip_ef3_4, flip_ef3_5, flip_ef3_6, flip_ef3_7, flip_ef3_8, flip_ef3_9, flip_ef3_10, flip_ef3_11, flip_ef3_12, flip_ef3_13, flip_ef3_14, flip_ef3_15]
  simp only [sg_ef3_w8_0, sg_ef3_w8_1, sg_ef3_w8_2, sg_ef3_w8_3, sg_ef3_w8_4, sg_ef3_w8_5, sg_ef3_w8_6, sg_ef3_w8_7, sg_ef3_w8_8, sg_ef3_w8_9, sg_ef3_w8_10, sg_ef3_w8_11, sg_ef3_w8_12, sg_ef3_w8_13, sg_ef3_w8_14, sg_ef3_w8_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

/-! ## The diagonal layer on the free qubit -/

def diagBot (c : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ x ∈ S0.filter (fun x => SS.bxor x e ∈ S0),
      SixQubit.signMul (SS.bdot z x) (star (c (SS.bxor x e)) * c x)

def diagTop (dd : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S1),
      SixQubit.signMul (SS.bdot z y) (star (dd (SS.bxor y e)) * dd y)

theorem dincB : S0.filter (fun x => SS.bxor x efF ∈ S0) = {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15} := by decide
theorem dincT : S1.filter (fun y => SS.bxor y efF ∈ S1) = {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15} := by decide
theorem dflipB_0 : SS.bxor y0 efF = y8 := by decide
theorem dflipB_1 : SS.bxor y1 efF = y9 := by decide
theorem dflipB_2 : SS.bxor y2 efF = y10 := by decide
theorem dflipB_3 : SS.bxor y3 efF = y11 := by decide
theorem dflipB_4 : SS.bxor y4 efF = y12 := by decide
theorem dflipB_5 : SS.bxor y5 efF = y13 := by decide
theorem dflipB_6 : SS.bxor y6 efF = y14 := by decide
theorem dflipB_7 : SS.bxor y7 efF = y15 := by decide
theorem dflipB_8 : SS.bxor y8 efF = y0 := by decide
theorem dflipB_9 : SS.bxor y9 efF = y1 := by decide
theorem dflipB_10 : SS.bxor y10 efF = y2 := by decide
theorem dflipB_11 : SS.bxor y11 efF = y3 := by decide
theorem dflipB_12 : SS.bxor y12 efF = y4 := by decide
theorem dflipB_13 : SS.bxor y13 efF = y5 := by decide
theorem dflipB_14 : SS.bxor y14 efF = y6 := by decide
theorem dflipB_15 : SS.bxor y15 efF = y7 := by decide
theorem dflipT_0 : SS.bxor z0 efF = z8 := by decide
theorem dflipT_1 : SS.bxor z1 efF = z9 := by decide
theorem dflipT_2 : SS.bxor z2 efF = z10 := by decide
theorem dflipT_3 : SS.bxor z3 efF = z11 := by decide
theorem dflipT_4 : SS.bxor z4 efF = z12 := by decide
theorem dflipT_5 : SS.bxor z5 efF = z13 := by decide
theorem dflipT_6 : SS.bxor z6 efF = z14 := by decide
theorem dflipT_7 : SS.bxor z7 efF = z15 := by decide
theorem dflipT_8 : SS.bxor z8 efF = z0 := by decide
theorem dflipT_9 : SS.bxor z9 efF = z1 := by decide
theorem dflipT_10 : SS.bxor z10 efF = z2 := by decide
theorem dflipT_11 : SS.bxor z11 efF = z3 := by decide
theorem dflipT_12 : SS.bxor z12 efF = z4 := by decide
theorem dflipT_13 : SS.bxor z13 efF = z5 := by decide
theorem dflipT_14 : SS.bxor z14 efF = z6 := by decide
theorem dflipT_15 : SS.bxor z15 efF = z7 := by decide

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
    diagBot c efF w0 = star (c y8) * c y0 + star (c y9) * c y1 + star (c y10) * c y2 + star (c y11) * c y3 + star (c y12) * c y4 + star (c y13) * c y5 + star (c y14) * c y6 + star (c y15) * c y7 + star (c y0) * c y8 + star (c y1) * c y9 + star (c y2) * c y10 + star (c y3) * c y11 + star (c y4) * c y12 + star (c y5) * c y13 + star (c y6) * c y14 + star (c y7) * c y15 := by
  unfold diagBot
  rw [dincB]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipB_0, dflipB_1, dflipB_2, dflipB_3, dflipB_4, dflipB_5, dflipB_6, dflipB_7, dflipB_8, dflipB_9, dflipB_10, dflipB_11, dflipB_12, dflipB_13, dflipB_14, dflipB_15]
  simp only [dsB_w0_0, dsB_w0_1, dsB_w0_2, dsB_w0_3, dsB_w0_4, dsB_w0_5, dsB_w0_6, dsB_w0_7, dsB_w0_8, dsB_w0_9, dsB_w0_10, dsB_w0_11, dsB_w0_12, dsB_w0_13, dsB_w0_14, dsB_w0_15, SixQubit.signMul_false]
  try ring
theorem dexT_w0 (dd : SS.BitString 6 -> ℂ) :
    diagTop dd efF w0 = star (dd z8) * dd z0 + star (dd z9) * dd z1 + star (dd z10) * dd z2 + star (dd z11) * dd z3 + star (dd z12) * dd z4 + star (dd z13) * dd z5 + star (dd z14) * dd z6 + star (dd z15) * dd z7 + star (dd z0) * dd z8 + star (dd z1) * dd z9 + star (dd z2) * dd z10 + star (dd z3) * dd z11 + star (dd z4) * dd z12 + star (dd z5) * dd z13 + star (dd z6) * dd z14 + star (dd z7) * dd z15 := by
  unfold diagTop
  rw [dincT]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipT_0, dflipT_1, dflipT_2, dflipT_3, dflipT_4, dflipT_5, dflipT_6, dflipT_7, dflipT_8, dflipT_9, dflipT_10, dflipT_11, dflipT_12, dflipT_13, dflipT_14, dflipT_15]
  simp only [dsT_w0_0, dsT_w0_1, dsT_w0_2, dsT_w0_3, dsT_w0_4, dsT_w0_5, dsT_w0_6, dsT_w0_7, dsT_w0_8, dsT_w0_9, dsT_w0_10, dsT_w0_11, dsT_w0_12, dsT_w0_13, dsT_w0_14, dsT_w0_15, SixQubit.signMul_false]
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
    diagBot c efF w11 = star (c y8) * c y0 + star (c y9) * c y1 + star (c y10) * c y2 + star (c y11) * c y3 + star (c y12) * c y4 + star (c y13) * c y5 + star (c y14) * c y6 + star (c y15) * c y7 - star (c y0) * c y8 - star (c y1) * c y9 - star (c y2) * c y10 - star (c y3) * c y11 - star (c y4) * c y12 - star (c y5) * c y13 - star (c y6) * c y14 - star (c y7) * c y15 := by
  unfold diagBot
  rw [dincB]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipB_0, dflipB_1, dflipB_2, dflipB_3, dflipB_4, dflipB_5, dflipB_6, dflipB_7, dflipB_8, dflipB_9, dflipB_10, dflipB_11, dflipB_12, dflipB_13, dflipB_14, dflipB_15]
  simp only [dsB_w11_0, dsB_w11_1, dsB_w11_2, dsB_w11_3, dsB_w11_4, dsB_w11_5, dsB_w11_6, dsB_w11_7, dsB_w11_8, dsB_w11_9, dsB_w11_10, dsB_w11_11, dsB_w11_12, dsB_w11_13, dsB_w11_14, dsB_w11_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem dexT_w11 (dd : SS.BitString 6 -> ℂ) :
    diagTop dd efF w11 = star (dd z8) * dd z0 + star (dd z9) * dd z1 + star (dd z10) * dd z2 + star (dd z11) * dd z3 + star (dd z12) * dd z4 + star (dd z13) * dd z5 + star (dd z14) * dd z6 + star (dd z15) * dd z7 - star (dd z0) * dd z8 - star (dd z1) * dd z9 - star (dd z2) * dd z10 - star (dd z3) * dd z11 - star (dd z4) * dd z12 - star (dd z5) * dd z13 - star (dd z6) * dd z14 - star (dd z7) * dd z15 := by
  unfold diagTop
  rw [dincT]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipT_0, dflipT_1, dflipT_2, dflipT_3, dflipT_4, dflipT_5, dflipT_6, dflipT_7, dflipT_8, dflipT_9, dflipT_10, dflipT_11, dflipT_12, dflipT_13, dflipT_14, dflipT_15]
  simp only [dsT_w11_0, dsT_w11_1, dsT_w11_2, dsT_w11_3, dsT_w11_4, dsT_w11_5, dsT_w11_6, dsT_w11_7, dsT_w11_8, dsT_w11_9, dsT_w11_10, dsT_w11_11, dsT_w11_12, dsT_w11_13, dsT_w11_14, dsT_w11_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dsB_w7_0 : SS.bdot w7 y0 = false := by decide
theorem dsB_w7_1 : SS.bdot w7 y1 = false := by decide
theorem dsB_w7_2 : SS.bdot w7 y2 = false := by decide
theorem dsB_w7_3 : SS.bdot w7 y3 = false := by decide
theorem dsB_w7_4 : SS.bdot w7 y4 = true := by decide
theorem dsB_w7_5 : SS.bdot w7 y5 = true := by decide
theorem dsB_w7_6 : SS.bdot w7 y6 = true := by decide
theorem dsB_w7_7 : SS.bdot w7 y7 = true := by decide
theorem dsB_w7_8 : SS.bdot w7 y8 = false := by decide
theorem dsB_w7_9 : SS.bdot w7 y9 = false := by decide
theorem dsB_w7_10 : SS.bdot w7 y10 = false := by decide
theorem dsB_w7_11 : SS.bdot w7 y11 = false := by decide
theorem dsB_w7_12 : SS.bdot w7 y12 = true := by decide
theorem dsB_w7_13 : SS.bdot w7 y13 = true := by decide
theorem dsB_w7_14 : SS.bdot w7 y14 = true := by decide
theorem dsB_w7_15 : SS.bdot w7 y15 = true := by decide
theorem dsT_w7_0 : SS.bdot w7 z0 = false := by decide
theorem dsT_w7_1 : SS.bdot w7 z1 = false := by decide
theorem dsT_w7_2 : SS.bdot w7 z2 = false := by decide
theorem dsT_w7_3 : SS.bdot w7 z3 = false := by decide
theorem dsT_w7_4 : SS.bdot w7 z4 = true := by decide
theorem dsT_w7_5 : SS.bdot w7 z5 = true := by decide
theorem dsT_w7_6 : SS.bdot w7 z6 = true := by decide
theorem dsT_w7_7 : SS.bdot w7 z7 = true := by decide
theorem dsT_w7_8 : SS.bdot w7 z8 = false := by decide
theorem dsT_w7_9 : SS.bdot w7 z9 = false := by decide
theorem dsT_w7_10 : SS.bdot w7 z10 = false := by decide
theorem dsT_w7_11 : SS.bdot w7 z11 = false := by decide
theorem dsT_w7_12 : SS.bdot w7 z12 = true := by decide
theorem dsT_w7_13 : SS.bdot w7 z13 = true := by decide
theorem dsT_w7_14 : SS.bdot w7 z14 = true := by decide
theorem dsT_w7_15 : SS.bdot w7 z15 = true := by decide
theorem dexB_w7 (c : SS.BitString 6 -> ℂ) :
    diagBot c efF w7 = star (c y8) * c y0 + star (c y9) * c y1 + star (c y10) * c y2 + star (c y11) * c y3 - star (c y12) * c y4 - star (c y13) * c y5 - star (c y14) * c y6 - star (c y15) * c y7 + star (c y0) * c y8 + star (c y1) * c y9 + star (c y2) * c y10 + star (c y3) * c y11 - star (c y4) * c y12 - star (c y5) * c y13 - star (c y6) * c y14 - star (c y7) * c y15 := by
  unfold diagBot
  rw [dincB]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipB_0, dflipB_1, dflipB_2, dflipB_3, dflipB_4, dflipB_5, dflipB_6, dflipB_7, dflipB_8, dflipB_9, dflipB_10, dflipB_11, dflipB_12, dflipB_13, dflipB_14, dflipB_15]
  simp only [dsB_w7_0, dsB_w7_1, dsB_w7_2, dsB_w7_3, dsB_w7_4, dsB_w7_5, dsB_w7_6, dsB_w7_7, dsB_w7_8, dsB_w7_9, dsB_w7_10, dsB_w7_11, dsB_w7_12, dsB_w7_13, dsB_w7_14, dsB_w7_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem dexT_w7 (dd : SS.BitString 6 -> ℂ) :
    diagTop dd efF w7 = star (dd z8) * dd z0 + star (dd z9) * dd z1 + star (dd z10) * dd z2 + star (dd z11) * dd z3 - star (dd z12) * dd z4 - star (dd z13) * dd z5 - star (dd z14) * dd z6 - star (dd z15) * dd z7 + star (dd z0) * dd z8 + star (dd z1) * dd z9 + star (dd z2) * dd z10 + star (dd z3) * dd z11 - star (dd z4) * dd z12 - star (dd z5) * dd z13 - star (dd z6) * dd z14 - star (dd z7) * dd z15 := by
  unfold diagTop
  rw [dincT]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipT_0, dflipT_1, dflipT_2, dflipT_3, dflipT_4, dflipT_5, dflipT_6, dflipT_7, dflipT_8, dflipT_9, dflipT_10, dflipT_11, dflipT_12, dflipT_13, dflipT_14, dflipT_15]
  simp only [dsT_w7_0, dsT_w7_1, dsT_w7_2, dsT_w7_3, dsT_w7_4, dsT_w7_5, dsT_w7_6, dsT_w7_7, dsT_w7_8, dsT_w7_9, dsT_w7_10, dsT_w7_11, dsT_w7_12, dsT_w7_13, dsT_w7_14, dsT_w7_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dsB_w12_0 : SS.bdot w12 y0 = false := by decide
theorem dsB_w12_1 : SS.bdot w12 y1 = false := by decide
theorem dsB_w12_2 : SS.bdot w12 y2 = false := by decide
theorem dsB_w12_3 : SS.bdot w12 y3 = false := by decide
theorem dsB_w12_4 : SS.bdot w12 y4 = true := by decide
theorem dsB_w12_5 : SS.bdot w12 y5 = true := by decide
theorem dsB_w12_6 : SS.bdot w12 y6 = true := by decide
theorem dsB_w12_7 : SS.bdot w12 y7 = true := by decide
theorem dsB_w12_8 : SS.bdot w12 y8 = true := by decide
theorem dsB_w12_9 : SS.bdot w12 y9 = true := by decide
theorem dsB_w12_10 : SS.bdot w12 y10 = true := by decide
theorem dsB_w12_11 : SS.bdot w12 y11 = true := by decide
theorem dsB_w12_12 : SS.bdot w12 y12 = false := by decide
theorem dsB_w12_13 : SS.bdot w12 y13 = false := by decide
theorem dsB_w12_14 : SS.bdot w12 y14 = false := by decide
theorem dsB_w12_15 : SS.bdot w12 y15 = false := by decide
theorem dsT_w12_0 : SS.bdot w12 z0 = false := by decide
theorem dsT_w12_1 : SS.bdot w12 z1 = false := by decide
theorem dsT_w12_2 : SS.bdot w12 z2 = false := by decide
theorem dsT_w12_3 : SS.bdot w12 z3 = false := by decide
theorem dsT_w12_4 : SS.bdot w12 z4 = true := by decide
theorem dsT_w12_5 : SS.bdot w12 z5 = true := by decide
theorem dsT_w12_6 : SS.bdot w12 z6 = true := by decide
theorem dsT_w12_7 : SS.bdot w12 z7 = true := by decide
theorem dsT_w12_8 : SS.bdot w12 z8 = true := by decide
theorem dsT_w12_9 : SS.bdot w12 z9 = true := by decide
theorem dsT_w12_10 : SS.bdot w12 z10 = true := by decide
theorem dsT_w12_11 : SS.bdot w12 z11 = true := by decide
theorem dsT_w12_12 : SS.bdot w12 z12 = false := by decide
theorem dsT_w12_13 : SS.bdot w12 z13 = false := by decide
theorem dsT_w12_14 : SS.bdot w12 z14 = false := by decide
theorem dsT_w12_15 : SS.bdot w12 z15 = false := by decide
theorem dexB_w12 (c : SS.BitString 6 -> ℂ) :
    diagBot c efF w12 = star (c y8) * c y0 + star (c y9) * c y1 + star (c y10) * c y2 + star (c y11) * c y3 - star (c y12) * c y4 - star (c y13) * c y5 - star (c y14) * c y6 - star (c y15) * c y7 - star (c y0) * c y8 - star (c y1) * c y9 - star (c y2) * c y10 - star (c y3) * c y11 + star (c y4) * c y12 + star (c y5) * c y13 + star (c y6) * c y14 + star (c y7) * c y15 := by
  unfold diagBot
  rw [dincB]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipB_0, dflipB_1, dflipB_2, dflipB_3, dflipB_4, dflipB_5, dflipB_6, dflipB_7, dflipB_8, dflipB_9, dflipB_10, dflipB_11, dflipB_12, dflipB_13, dflipB_14, dflipB_15]
  simp only [dsB_w12_0, dsB_w12_1, dsB_w12_2, dsB_w12_3, dsB_w12_4, dsB_w12_5, dsB_w12_6, dsB_w12_7, dsB_w12_8, dsB_w12_9, dsB_w12_10, dsB_w12_11, dsB_w12_12, dsB_w12_13, dsB_w12_14, dsB_w12_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem dexT_w12 (dd : SS.BitString 6 -> ℂ) :
    diagTop dd efF w12 = star (dd z8) * dd z0 + star (dd z9) * dd z1 + star (dd z10) * dd z2 + star (dd z11) * dd z3 - star (dd z12) * dd z4 - star (dd z13) * dd z5 - star (dd z14) * dd z6 - star (dd z15) * dd z7 - star (dd z0) * dd z8 - star (dd z1) * dd z9 - star (dd z2) * dd z10 - star (dd z3) * dd z11 + star (dd z4) * dd z12 + star (dd z5) * dd z13 + star (dd z6) * dd z14 + star (dd z7) * dd z15 := by
  unfold diagTop
  rw [dincT]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipT_0, dflipT_1, dflipT_2, dflipT_3, dflipT_4, dflipT_5, dflipT_6, dflipT_7, dflipT_8, dflipT_9, dflipT_10, dflipT_11, dflipT_12, dflipT_13, dflipT_14, dflipT_15]
  simp only [dsT_w12_0, dsT_w12_1, dsT_w12_2, dsT_w12_3, dsT_w12_4, dsT_w12_5, dsT_w12_6, dsT_w12_7, dsT_w12_8, dsT_w12_9, dsT_w12_10, dsT_w12_11, dsT_w12_12, dsT_w12_13, dsT_w12_14, dsT_w12_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

/-! ## The moment system -/

/-- The two normalizations, the twenty-one moment equalities, and the
nonnegativity of every probability. -/
structure MomentSystem (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real) : Prop where
  n0 : q0 + q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 + q9 + q10 + q11 + q12 + q13 + q14 + q15 = 1
  n1 : r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15 = 1
  m1 : q8 + q9 + q10 + q11 + q12 + q13 + q14 + q15 = r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15
  m2 : 0 = 0
  m3 : q4 + q5 + q6 + q7 + q12 + q13 + q14 + q15 = r4 + r5 + r6 + r7 + r12 + r13 + r14 + r15
  m4 : q2 + q3 + q6 + q7 + q10 + q11 + q14 + q15 = r2 + r3 + r6 + r7 + r10 + r11 + r14 + r15
  m5 : q1 + q3 + q5 + q7 + q9 + q11 + q13 + q15 = r1 + r3 + r5 + r7 + r9 + r11 + r13 + r15
  m6 : q1 + q2 + q4 + q7 + q9 + q10 + q12 + q15 = r0 + r3 + r5 + r6 + r8 + r11 + r13 + r14
  m12 : 0 = 0
  m13 : q12 + q13 + q14 + q15 = r12 + r13 + r14 + r15
  m14 : q10 + q11 + q14 + q15 = r10 + r11 + r14 + r15
  m15 : q9 + q11 + q13 + q15 = r9 + r11 + r13 + r15
  m16 : q9 + q10 + q12 + q15 = r8 + r11 + r13 + r14
  m23 : 0 = 0
  m24 : 0 = 0
  m25 : 0 = 0
  m26 : 0 = 0
  m34 : q6 + q7 + q14 + q15 = r6 + r7 + r14 + r15
  m35 : q5 + q7 + q13 + q15 = r5 + r7 + r13 + r15
  m36 : q4 + q7 + q12 + q15 = r5 + r6 + r13 + r14
  m45 : q3 + q7 + q11 + q15 = r3 + r7 + r11 + r15
  m46 : q2 + q7 + q10 + q15 = r3 + r6 + r11 + r14
  m56 : q1 + q7 + q9 + q15 = r3 + r5 + r11 + r13

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

/-- Everything the slice argument needs from the moment polytope: the two
slice frame diagonals and the four neighbour-sum identities, per slice. -/
theorem MomentSystem.sliceData {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    (q0 + q1 + q2 + q3 = r3 + r2 + r1 + r0)
      ∧ (q8 + q9 + q10 + q11 = r11 + r10 + r9 + r8)
      ∧ (r2 + r10 + r1 + r9 + r0 + r8 = (q0 + q8 + q1 + q9 + q2 + q10 + q3 + q11) / 2 + (q0 + q8))
      ∧ (r3 + r11 + r1 + r9 + r0 + r8 = (q0 + q8 + q1 + q9 + q2 + q10 + q3 + q11) / 2 + (q1 + q9))
      ∧ (r3 + r11 + r2 + r10 + r0 + r8 = (q0 + q8 + q1 + q9 + q2 + q10 + q3 + q11) / 2 + (q2 + q10))
      ∧ (r3 + r11 + r2 + r10 + r1 + r9 = (q0 + q8 + q1 + q9 + q2 + q10 + q3 + q11) / 2 + (q3 + q11))
      ∧ (q4 + q5 + q6 + q7 = r7 + r6 + r5 + r4)
      ∧ (q12 + q13 + q14 + q15 = r15 + r14 + r13 + r12)
      ∧ (r6 + r14 + r5 + r13 + r4 + r12 = (q4 + q12 + q5 + q13 + q6 + q14 + q7 + q15) / 2 + (q4 + q12))
      ∧ (r7 + r15 + r5 + r13 + r4 + r12 = (q4 + q12 + q5 + q13 + q6 + q14 + q7 + q15) / 2 + (q5 + q13))
      ∧ (r7 + r15 + r6 + r14 + r4 + r12 = (q4 + q12 + q5 + q13 + q6 + q14 + q7 + q15) / 2 + (q6 + q14))
      ∧ (r7 + r15 + r6 + r14 + r5 + r13 = (q4 + q12 + q5 + q13 + q6 + q14 + q7 + q15) / 2 + (q7 + q15))
    := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, m12, m13, m14, m15, m16, m23, m24, m25, m26, m34, m35, m36, m45, m46, m56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-! ## The no-go -/

/-- **Orbit 15 is impossible.** -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11)) (Complex.normSq (c y12)) (Complex.normSq (c y13)) (Complex.normSq (c y14)) (Complex.normSq (c y15))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)) (Complex.normSq (d z12)) (Complex.normSq (d z13)) (Complex.normSq (d z14)) (Complex.normSq (d z15)))
    (ho_ef1_w0 : offSum c d ef1 w0 = 0)
    (ho_ef1_w1 : offSum c d ef1 w1 = 0)
    (ho_ef1_w2 : offSum c d ef1 w2 = 0)
    (ho_ef1_w4 : offSum c d ef1 w4 = 0)
    (ho_ef1_w5 : offSum c d ef1 w5 = 0)
    (ho_ef1_w6 : offSum c d ef1 w6 = 0)
    (ho_ef1_w7 : offSum c d ef1 w7 = 0)
    (ho_ef1_w10 : offSum c d ef1 w10 = 0)
    (ho_ef2_w0 : offSum c d ef2 w0 = 0)
    (ho_ef2_w1 : offSum c d ef2 w1 = 0)
    (ho_ef2_w2 : offSum c d ef2 w2 = 0)
    (ho_ef2_w3 : offSum c d ef2 w3 = 0)
    (ho_ef2_w4 : offSum c d ef2 w4 = 0)
    (ho_ef2_w6 : offSum c d ef2 w6 = 0)
    (ho_ef2_w7 : offSum c d ef2 w7 = 0)
    (ho_ef2_w9 : offSum c d ef2 w9 = 0)
    (ho_ef3_w0 : offSum c d ef3 w0 = 0)
    (ho_ef3_w1 : offSum c d ef3 w1 = 0)
    (ho_ef3_w2 : offSum c d ef3 w2 = 0)
    (ho_ef3_w3 : offSum c d ef3 w3 = 0)
    (ho_ef3_w4 : offSum c d ef3 w4 = 0)
    (ho_ef3_w5 : offSum c d ef3 w5 = 0)
    (ho_ef3_w7 : offSum c d ef3 w7 = 0)
    (ho_ef3_w8 : offSum c d ef3 w8 = 0)
    (hd_w0 : diagBot c efF w0 = diagTop d efF w0)
    (hd_w11 : diagBot c efF w11 = diagTop d efF w11)
    (hd_w7 : diagBot c efF w7 = diagTop d efF w7)
    (hd_w12 : diagBot c efF w12 = diagTop d efF w12)
    : False := by
  rw [ex_ef1_w0] at ho_ef1_w0
  rw [ex_ef1_w1] at ho_ef1_w1
  rw [ex_ef1_w2] at ho_ef1_w2
  rw [ex_ef1_w4] at ho_ef1_w4
  rw [ex_ef1_w5] at ho_ef1_w5
  rw [ex_ef1_w6] at ho_ef1_w6
  rw [ex_ef1_w7] at ho_ef1_w7
  rw [ex_ef1_w10] at ho_ef1_w10
  rw [ex_ef2_w0] at ho_ef2_w0
  rw [ex_ef2_w1] at ho_ef2_w1
  rw [ex_ef2_w2] at ho_ef2_w2
  rw [ex_ef2_w3] at ho_ef2_w3
  rw [ex_ef2_w4] at ho_ef2_w4
  rw [ex_ef2_w6] at ho_ef2_w6
  rw [ex_ef2_w7] at ho_ef2_w7
  rw [ex_ef2_w9] at ho_ef2_w9
  rw [ex_ef3_w0] at ho_ef3_w0
  rw [ex_ef3_w1] at ho_ef3_w1
  rw [ex_ef3_w2] at ho_ef3_w2
  rw [ex_ef3_w3] at ho_ef3_w3
  rw [ex_ef3_w4] at ho_ef3_w4
  rw [ex_ef3_w5] at ho_ef3_w5
  rw [ex_ef3_w7] at ho_ef3_w7
  rw [ex_ef3_w8] at ho_ef3_w8
  rw [dexB_w0, dexT_w0] at hd_w0
  rw [dexB_w11, dexT_w11] at hd_w11
  rw [dexB_w7, dexT_w7] at hd_w7
  rw [dexB_w12, dexT_w12] at hd_w12
  obtain ⟨sd0, sd1, sd2, sd3, sd4, sd5, sd6, sd7, sd8, sd9, sd10, sd11⟩ := hm.sliceData
  have s0o12 : star (c y0) * d z2 + star (c y8) * d z10 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef1_w0 + (1/8 : ℂ) * ho_ef1_w1 + (1/8 : ℂ) * ho_ef1_w2 + (-1/8 : ℂ) * ho_ef1_w4 + (-1/8 : ℂ) * ho_ef1_w5 + (-1/8 : ℂ) * ho_ef1_w6 + (1/8 : ℂ) * ho_ef1_w7 + (-1/8 : ℂ) * ho_ef1_w10
  have s0o13 : star (c y0) * d z1 + star (c y8) * d z9 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef2_w0 + (1/8 : ℂ) * ho_ef2_w1 + (-1/8 : ℂ) * ho_ef2_w2 + (-1/8 : ℂ) * ho_ef2_w3 + (1/8 : ℂ) * ho_ef2_w4 + (-1/8 : ℂ) * ho_ef2_w6 + (1/8 : ℂ) * ho_ef2_w7 + (-1/8 : ℂ) * ho_ef2_w9
  have s0o14 : star (c y0) * d z0 + star (c y8) * d z8 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef3_w0 + (-1/8 : ℂ) * ho_ef3_w1 + (1/8 : ℂ) * ho_ef3_w2 + (-1/8 : ℂ) * ho_ef3_w3 + (1/8 : ℂ) * ho_ef3_w4 + (-1/8 : ℂ) * ho_ef3_w5 + (1/8 : ℂ) * ho_ef3_w7 + (-1/8 : ℂ) * ho_ef3_w8
  have s0o21 : star (c y1) * d z3 + star (c y9) * d z11 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef1_w0 + (-1/8 : ℂ) * ho_ef1_w1 + (-1/8 : ℂ) * ho_ef1_w2 + (-1/8 : ℂ) * ho_ef1_w4 + (1/8 : ℂ) * ho_ef1_w5 + (1/8 : ℂ) * ho_ef1_w6 + (1/8 : ℂ) * ho_ef1_w7 + (-1/8 : ℂ) * ho_ef1_w10
  have s0o23 : star (c y1) * d z1 + star (c y9) * d z9 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef3_w0 + (1/8 : ℂ) * ho_ef3_w1 + (-1/8 : ℂ) * ho_ef3_w2 + (-1/8 : ℂ) * ho_ef3_w3 + (1/8 : ℂ) * ho_ef3_w4 + (1/8 : ℂ) * ho_ef3_w5 + (1/8 : ℂ) * ho_ef3_w7 + (1/8 : ℂ) * ho_ef3_w8
  have s0o24 : star (c y1) * d z0 + star (c y9) * d z8 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef2_w0 + (-1/8 : ℂ) * ho_ef2_w1 + (1/8 : ℂ) * ho_ef2_w2 + (-1/8 : ℂ) * ho_ef2_w3 + (1/8 : ℂ) * ho_ef2_w4 + (1/8 : ℂ) * ho_ef2_w6 + (1/8 : ℂ) * ho_ef2_w7 + (1/8 : ℂ) * ho_ef2_w9
  have s0o31 : star (c y2) * d z3 + star (c y10) * d z11 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef2_w0 + (-1/8 : ℂ) * ho_ef2_w1 + (-1/8 : ℂ) * ho_ef2_w2 + (1/8 : ℂ) * ho_ef2_w3 + (-1/8 : ℂ) * ho_ef2_w4 + (1/8 : ℂ) * ho_ef2_w6 + (1/8 : ℂ) * ho_ef2_w7 + (-1/8 : ℂ) * ho_ef2_w9
  have s0o32 : star (c y2) * d z2 + star (c y10) * d z10 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef3_w0 + (1/8 : ℂ) * ho_ef3_w1 + (1/8 : ℂ) * ho_ef3_w2 + (1/8 : ℂ) * ho_ef3_w3 + (-1/8 : ℂ) * ho_ef3_w4 + (-1/8 : ℂ) * ho_ef3_w5 + (1/8 : ℂ) * ho_ef3_w7 + (1/8 : ℂ) * ho_ef3_w8
  have s0o34 : star (c y2) * d z0 + star (c y10) * d z8 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef1_w0 + (-1/8 : ℂ) * ho_ef1_w1 + (1/8 : ℂ) * ho_ef1_w2 + (1/8 : ℂ) * ho_ef1_w4 + (-1/8 : ℂ) * ho_ef1_w5 + (1/8 : ℂ) * ho_ef1_w6 + (1/8 : ℂ) * ho_ef1_w7 + (1/8 : ℂ) * ho_ef1_w10
  have s0o41 : star (c y3) * d z3 + star (c y11) * d z11 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef3_w0 + (-1/8 : ℂ) * ho_ef3_w1 + (-1/8 : ℂ) * ho_ef3_w2 + (1/8 : ℂ) * ho_ef3_w3 + (-1/8 : ℂ) * ho_ef3_w4 + (1/8 : ℂ) * ho_ef3_w5 + (1/8 : ℂ) * ho_ef3_w7 + (-1/8 : ℂ) * ho_ef3_w8
  have s0o42 : star (c y3) * d z2 + star (c y11) * d z10 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef2_w0 + (1/8 : ℂ) * ho_ef2_w1 + (1/8 : ℂ) * ho_ef2_w2 + (1/8 : ℂ) * ho_ef2_w3 + (-1/8 : ℂ) * ho_ef2_w4 + (-1/8 : ℂ) * ho_ef2_w6 + (1/8 : ℂ) * ho_ef2_w7 + (1/8 : ℂ) * ho_ef2_w9
  have s0o43 : star (c y3) * d z1 + star (c y11) * d z9 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef1_w0 + (1/8 : ℂ) * ho_ef1_w1 + (-1/8 : ℂ) * ho_ef1_w2 + (1/8 : ℂ) * ho_ef1_w4 + (1/8 : ℂ) * ho_ef1_w5 + (-1/8 : ℂ) * ho_ef1_w6 + (1/8 : ℂ) * ho_ef1_w7 + (1/8 : ℂ) * ho_ef1_w10
  have s0fB : c y0 * star (c y8) + c y1 * star (c y9) + c y2 * star (c y10) + c y3 * star (c y11)
      = d z3 * star (d z11) + d z2 * star (d z10) + d z1 * star (d z9) + d z0 * star (d z8) := by
    linear_combination (1/4 : ℂ) * hd_w0 + (1/4 : ℂ) * hd_w11 + (1/4 : ℂ) * hd_w7 + (1/4 : ℂ) * hd_w12
  have s0z : Complex.normSq (c y0) + Complex.normSq (c y8) + Complex.normSq (c y1) + Complex.normSq (c y9) + Complex.normSq (c y2) + Complex.normSq (c y10) + Complex.normSq (c y3) + Complex.normSq (c y11) = 0 :=
    SixQubit.ParityFour.slice_zero s0o12 s0o13 s0o14 s0o21 s0o23 s0o24 s0o31 s0o32 s0o34 s0o41 s0o42 s0o43 sd0 sd1 s0fB sd2 sd3 sd4 sd5
  have s1o12 : star (c y4) * d z6 + star (c y12) * d z14 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef1_w0 + (-1/8 : ℂ) * ho_ef1_w1 + (1/8 : ℂ) * ho_ef1_w2 + (-1/8 : ℂ) * ho_ef1_w4 + (1/8 : ℂ) * ho_ef1_w5 + (-1/8 : ℂ) * ho_ef1_w6 + (-1/8 : ℂ) * ho_ef1_w7 + (1/8 : ℂ) * ho_ef1_w10
  have s1o13 : star (c y4) * d z5 + star (c y12) * d z13 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef2_w0 + (-1/8 : ℂ) * ho_ef2_w1 + (-1/8 : ℂ) * ho_ef2_w2 + (1/8 : ℂ) * ho_ef2_w3 + (1/8 : ℂ) * ho_ef2_w4 + (-1/8 : ℂ) * ho_ef2_w6 + (-1/8 : ℂ) * ho_ef2_w7 + (1/8 : ℂ) * ho_ef2_w9
  have s1o14 : star (c y4) * d z4 + star (c y12) * d z12 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef3_w0 + (1/8 : ℂ) * ho_ef3_w1 + (1/8 : ℂ) * ho_ef3_w2 + (1/8 : ℂ) * ho_ef3_w3 + (1/8 : ℂ) * ho_ef3_w4 + (1/8 : ℂ) * ho_ef3_w5 + (-1/8 : ℂ) * ho_ef3_w7 + (-1/8 : ℂ) * ho_ef3_w8
  have s1o21 : star (c y5) * d z7 + star (c y13) * d z15 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef1_w0 + (1/8 : ℂ) * ho_ef1_w1 + (-1/8 : ℂ) * ho_ef1_w2 + (-1/8 : ℂ) * ho_ef1_w4 + (-1/8 : ℂ) * ho_ef1_w5 + (1/8 : ℂ) * ho_ef1_w6 + (-1/8 : ℂ) * ho_ef1_w7 + (1/8 : ℂ) * ho_ef1_w10
  have s1o23 : star (c y5) * d z5 + star (c y13) * d z13 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef3_w0 + (-1/8 : ℂ) * ho_ef3_w1 + (-1/8 : ℂ) * ho_ef3_w2 + (1/8 : ℂ) * ho_ef3_w3 + (1/8 : ℂ) * ho_ef3_w4 + (-1/8 : ℂ) * ho_ef3_w5 + (-1/8 : ℂ) * ho_ef3_w7 + (1/8 : ℂ) * ho_ef3_w8
  have s1o24 : star (c y5) * d z4 + star (c y13) * d z12 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef2_w0 + (1/8 : ℂ) * ho_ef2_w1 + (1/8 : ℂ) * ho_ef2_w2 + (1/8 : ℂ) * ho_ef2_w3 + (1/8 : ℂ) * ho_ef2_w4 + (1/8 : ℂ) * ho_ef2_w6 + (-1/8 : ℂ) * ho_ef2_w7 + (-1/8 : ℂ) * ho_ef2_w9
  have s1o31 : star (c y6) * d z7 + star (c y14) * d z15 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef2_w0 + (1/8 : ℂ) * ho_ef2_w1 + (-1/8 : ℂ) * ho_ef2_w2 + (-1/8 : ℂ) * ho_ef2_w3 + (-1/8 : ℂ) * ho_ef2_w4 + (1/8 : ℂ) * ho_ef2_w6 + (-1/8 : ℂ) * ho_ef2_w7 + (1/8 : ℂ) * ho_ef2_w9
  have s1o32 : star (c y6) * d z6 + star (c y14) * d z14 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef3_w0 + (-1/8 : ℂ) * ho_ef3_w1 + (1/8 : ℂ) * ho_ef3_w2 + (-1/8 : ℂ) * ho_ef3_w3 + (-1/8 : ℂ) * ho_ef3_w4 + (1/8 : ℂ) * ho_ef3_w5 + (-1/8 : ℂ) * ho_ef3_w7 + (1/8 : ℂ) * ho_ef3_w8
  have s1o34 : star (c y6) * d z4 + star (c y14) * d z12 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef1_w0 + (1/8 : ℂ) * ho_ef1_w1 + (1/8 : ℂ) * ho_ef1_w2 + (1/8 : ℂ) * ho_ef1_w4 + (1/8 : ℂ) * ho_ef1_w5 + (1/8 : ℂ) * ho_ef1_w6 + (-1/8 : ℂ) * ho_ef1_w7 + (-1/8 : ℂ) * ho_ef1_w10
  have s1o41 : star (c y7) * d z7 + star (c y15) * d z15 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef3_w0 + (1/8 : ℂ) * ho_ef3_w1 + (-1/8 : ℂ) * ho_ef3_w2 + (-1/8 : ℂ) * ho_ef3_w3 + (-1/8 : ℂ) * ho_ef3_w4 + (-1/8 : ℂ) * ho_ef3_w5 + (-1/8 : ℂ) * ho_ef3_w7 + (-1/8 : ℂ) * ho_ef3_w8
  have s1o42 : star (c y7) * d z6 + star (c y15) * d z14 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef2_w0 + (-1/8 : ℂ) * ho_ef2_w1 + (1/8 : ℂ) * ho_ef2_w2 + (-1/8 : ℂ) * ho_ef2_w3 + (-1/8 : ℂ) * ho_ef2_w4 + (-1/8 : ℂ) * ho_ef2_w6 + (-1/8 : ℂ) * ho_ef2_w7 + (-1/8 : ℂ) * ho_ef2_w9
  have s1o43 : star (c y7) * d z5 + star (c y15) * d z13 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef1_w0 + (-1/8 : ℂ) * ho_ef1_w1 + (-1/8 : ℂ) * ho_ef1_w2 + (1/8 : ℂ) * ho_ef1_w4 + (-1/8 : ℂ) * ho_ef1_w5 + (-1/8 : ℂ) * ho_ef1_w6 + (-1/8 : ℂ) * ho_ef1_w7 + (-1/8 : ℂ) * ho_ef1_w10
  have s1fB : c y4 * star (c y12) + c y5 * star (c y13) + c y6 * star (c y14) + c y7 * star (c y15)
      = d z7 * star (d z15) + d z6 * star (d z14) + d z5 * star (d z13) + d z4 * star (d z12) := by
    linear_combination (1/4 : ℂ) * hd_w0 + (1/4 : ℂ) * hd_w11 + (-1/4 : ℂ) * hd_w7 + (-1/4 : ℂ) * hd_w12
  have s1z : Complex.normSq (c y4) + Complex.normSq (c y12) + Complex.normSq (c y5) + Complex.normSq (c y13) + Complex.normSq (c y6) + Complex.normSq (c y14) + Complex.normSq (c y7) + Complex.normSq (c y15) = 0 :=
    SixQubit.ParityFour.slice_zero s1o12 s1o13 s1o14 s1o21 s1o23 s1o24 s1o31 s1o32 s1o34 s1o41 s1o42 s1o43 sd6 sd7 s1fB sd8 sd9 sd10 sd11
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, m12, m13, m14, m15, m16, m23, m24, m25, m26, m34, m35, m36, m45, m46, m56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := hm
  linarith [s0z, s1z]

end

end SixQubit.Orbit15
