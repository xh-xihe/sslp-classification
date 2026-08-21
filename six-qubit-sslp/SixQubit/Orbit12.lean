import Mathlib

import SS.FullKL
import SixQubit.Common
import SixQubit.Spinor

/-!
# Six-qubit no-go for moment orbit 12

Orbit 12 of `six_qubit_sslp.tex`: q = 4, angle vector
a = (0, 1, 1, 1, 1, 2), residues 0 and 2.

Qubit 1 has angle zero, so the amplitudes group into spinors in `ℂ²`.
Qubit 6 has the half angle; on the two-qubit subsystem it spans with the
zero-angle qubit, the cross Knill--Laflamme block reads

```
ut * u† + vt * v† = 0 ,
```

a cancellation of two rank-one matrices whose four anchors all have
squared norm 1/4.  Two complementary physical-pair rows then eliminate
against it -- see `SixQubit.Spinor.cancel_perp`, which does this without
spans, unit vectors or division -- leaving the top edge vector `b_ebar`
orthogonal to both anchors.  The `H = 0` diagonal block of the equality
of the two reduced states on that subsystem then kills `b_ebar` outright
(`SixQubit.Spinor.edge_zero`), while the moment polytope forces the three
complementary pair masses to sum to 1/4, so one of them is positive.

Everything computational is decided by the Lean kernel; `native_decide`
is not used.
-/

namespace SixQubit.Orbit12

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

/-! ## The two fibers -/

def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]

def y0 : SS.BitString 6 := bs false false false false false false  -- 000000
def y1 : SS.BitString 6 := bs false false false true  true  true   -- 000111
def y2 : SS.BitString 6 := bs false false true  false true  true   -- 001011
def y3 : SS.BitString 6 := bs false false true  true  false true   -- 001101
def y4 : SS.BitString 6 := bs false true  false false true  true   -- 010011
def y5 : SS.BitString 6 := bs false true  false true  false true   -- 010101
def y6 : SS.BitString 6 := bs false true  true  false false true   -- 011001
def y7 : SS.BitString 6 := bs false true  true  true  true  false  -- 011110
def y8 : SS.BitString 6 := bs true  false false false false false  -- 100000
def y9 : SS.BitString 6 := bs true  false false true  true  true   -- 100111
def y10 : SS.BitString 6 := bs true  false true  false true  true   -- 101011
def y11 : SS.BitString 6 := bs true  false true  true  false true   -- 101101
def y12 : SS.BitString 6 := bs true  true  false false true  true   -- 110011
def y13 : SS.BitString 6 := bs true  true  false true  false true   -- 110101
def y14 : SS.BitString 6 := bs true  true  true  false false true   -- 111001
def y15 : SS.BitString 6 := bs true  true  true  true  true  false  -- 111110

def z0 : SS.BitString 6 := bs false false false false false true   -- 000001
def z1 : SS.BitString 6 := bs false false false true  true  false  -- 000110
def z2 : SS.BitString 6 := bs false false true  false true  false  -- 001010
def z3 : SS.BitString 6 := bs false false true  true  false false  -- 001100
def z4 : SS.BitString 6 := bs false true  false false true  false  -- 010010
def z5 : SS.BitString 6 := bs false true  false true  false false  -- 010100
def z6 : SS.BitString 6 := bs false true  true  false false false  -- 011000
def z7 : SS.BitString 6 := bs false true  true  true  true  true   -- 011111
def z8 : SS.BitString 6 := bs true  false false false false true   -- 100001
def z9 : SS.BitString 6 := bs true  false false true  true  false  -- 100110
def z10 : SS.BitString 6 := bs true  false true  false true  false  -- 101010
def z11 : SS.BitString 6 := bs true  false true  true  false false  -- 101100
def z12 : SS.BitString 6 := bs true  true  false false true  false  -- 110010
def z13 : SS.BitString 6 := bs true  true  false true  false false  -- 110100
def z14 : SS.BitString 6 := bs true  true  true  false false false  -- 111000
def z15 : SS.BitString 6 := bs true  true  true  true  true  true   -- 111111

def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15}
def S1 : Finset (SS.BitString 6) := {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15}

def av : Fin 6 -> ZMod 4 := ![0, 1, 1, 1, 1, 2]

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
def ef1 : SS.BitString 6 := bs true  false false false false true   -- 100001
def ef2 : SS.BitString 6 := bs false true  true  false false false  -- 011000
def ef3 : SS.BitString 6 := bs false false false true  true  false  -- 000110
def ef4 : SS.BitString 6 := bs false true  false true  false false  -- 010100
def ef5 : SS.BitString 6 := bs false false true  false true  false  -- 001010
def ef6 : SS.BitString 6 := bs false true  false false true  false  -- 010010
def ef7 : SS.BitString 6 := bs false false true  true  false false  -- 001100
def efA : SS.BitString 6 := bs true  false false false false false  -- 100000
def w0 : SS.BitString 6 := bs false false false false false false  -- 000000
def w1 : SS.BitString 6 := bs false false false false false true   -- 000001
def w2 : SS.BitString 6 := bs false false false false true  false  -- 000010
def w3 : SS.BitString 6 := bs false false false true  false false  -- 000100
def w4 : SS.BitString 6 := bs false false true  false false false  -- 001000
def w5 : SS.BitString 6 := bs true  false false false false false  -- 100000
def w6 : SS.BitString 6 := bs true  false false false false true   -- 100001

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
theorem sg_ef0_w1_3 : SS.bdot w1 z3 = false := by decide
theorem sg_ef0_w1_4 : SS.bdot w1 z4 = false := by decide
theorem sg_ef0_w1_5 : SS.bdot w1 z5 = false := by decide
theorem sg_ef0_w1_6 : SS.bdot w1 z6 = false := by decide
theorem sg_ef0_w1_7 : SS.bdot w1 z7 = true := by decide
theorem sg_ef0_w1_8 : SS.bdot w1 z8 = true := by decide
theorem sg_ef0_w1_9 : SS.bdot w1 z9 = false := by decide
theorem sg_ef0_w1_10 : SS.bdot w1 z10 = false := by decide
theorem sg_ef0_w1_11 : SS.bdot w1 z11 = false := by decide
theorem sg_ef0_w1_12 : SS.bdot w1 z12 = false := by decide
theorem sg_ef0_w1_13 : SS.bdot w1 z13 = false := by decide
theorem sg_ef0_w1_14 : SS.bdot w1 z14 = false := by decide
theorem sg_ef0_w1_15 : SS.bdot w1 z15 = true := by decide
theorem ex_ef0_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w1 = - star (c y0) * d z0 + star (c y1) * d z1 + star (c y2) * d z2 + star (c y3) * d z3 + star (c y4) * d z4 + star (c y5) * d z5 + star (c y6) * d z6 - star (c y7) * d z7 - star (c y8) * d z8 + star (c y9) * d z9 + star (c y10) * d z10 + star (c y11) * d z11 + star (c y12) * d z12 + star (c y13) * d z13 + star (c y14) * d z14 - star (c y15) * d z15 := by
  unfold offSum
  rw [incidence_ef0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef0_0, flip_ef0_1, flip_ef0_2, flip_ef0_3, flip_ef0_4, flip_ef0_5, flip_ef0_6, flip_ef0_7, flip_ef0_8, flip_ef0_9, flip_ef0_10, flip_ef0_11, flip_ef0_12, flip_ef0_13, flip_ef0_14, flip_ef0_15]
  simp only [sg_ef0_w1_0, sg_ef0_w1_1, sg_ef0_w1_2, sg_ef0_w1_3, sg_ef0_w1_4, sg_ef0_w1_5, sg_ef0_w1_6, sg_ef0_w1_7, sg_ef0_w1_8, sg_ef0_w1_9, sg_ef0_w1_10, sg_ef0_w1_11, sg_ef0_w1_12, sg_ef0_w1_13, sg_ef0_w1_14, sg_ef0_w1_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef0_w5_0 : SS.bdot w5 z0 = false := by decide
theorem sg_ef0_w5_1 : SS.bdot w5 z1 = false := by decide
theorem sg_ef0_w5_2 : SS.bdot w5 z2 = false := by decide
theorem sg_ef0_w5_3 : SS.bdot w5 z3 = false := by decide
theorem sg_ef0_w5_4 : SS.bdot w5 z4 = false := by decide
theorem sg_ef0_w5_5 : SS.bdot w5 z5 = false := by decide
theorem sg_ef0_w5_6 : SS.bdot w5 z6 = false := by decide
theorem sg_ef0_w5_7 : SS.bdot w5 z7 = false := by decide
theorem sg_ef0_w5_8 : SS.bdot w5 z8 = true := by decide
theorem sg_ef0_w5_9 : SS.bdot w5 z9 = true := by decide
theorem sg_ef0_w5_10 : SS.bdot w5 z10 = true := by decide
theorem sg_ef0_w5_11 : SS.bdot w5 z11 = true := by decide
theorem sg_ef0_w5_12 : SS.bdot w5 z12 = true := by decide
theorem sg_ef0_w5_13 : SS.bdot w5 z13 = true := by decide
theorem sg_ef0_w5_14 : SS.bdot w5 z14 = true := by decide
theorem sg_ef0_w5_15 : SS.bdot w5 z15 = true := by decide
theorem ex_ef0_w5 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w5 = star (c y0) * d z0 + star (c y1) * d z1 + star (c y2) * d z2 + star (c y3) * d z3 + star (c y4) * d z4 + star (c y5) * d z5 + star (c y6) * d z6 + star (c y7) * d z7 - star (c y8) * d z8 - star (c y9) * d z9 - star (c y10) * d z10 - star (c y11) * d z11 - star (c y12) * d z12 - star (c y13) * d z13 - star (c y14) * d z14 - star (c y15) * d z15 := by
  unfold offSum
  rw [incidence_ef0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef0_0, flip_ef0_1, flip_ef0_2, flip_ef0_3, flip_ef0_4, flip_ef0_5, flip_ef0_6, flip_ef0_7, flip_ef0_8, flip_ef0_9, flip_ef0_10, flip_ef0_11, flip_ef0_12, flip_ef0_13, flip_ef0_14, flip_ef0_15]
  simp only [sg_ef0_w5_0, sg_ef0_w5_1, sg_ef0_w5_2, sg_ef0_w5_3, sg_ef0_w5_4, sg_ef0_w5_5, sg_ef0_w5_6, sg_ef0_w5_7, sg_ef0_w5_8, sg_ef0_w5_9, sg_ef0_w5_10, sg_ef0_w5_11, sg_ef0_w5_12, sg_ef0_w5_13, sg_ef0_w5_14, sg_ef0_w5_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef0_w6_0 : SS.bdot w6 z0 = true := by decide
theorem sg_ef0_w6_1 : SS.bdot w6 z1 = false := by decide
theorem sg_ef0_w6_2 : SS.bdot w6 z2 = false := by decide
theorem sg_ef0_w6_3 : SS.bdot w6 z3 = false := by decide
theorem sg_ef0_w6_4 : SS.bdot w6 z4 = false := by decide
theorem sg_ef0_w6_5 : SS.bdot w6 z5 = false := by decide
theorem sg_ef0_w6_6 : SS.bdot w6 z6 = false := by decide
theorem sg_ef0_w6_7 : SS.bdot w6 z7 = true := by decide
theorem sg_ef0_w6_8 : SS.bdot w6 z8 = false := by decide
theorem sg_ef0_w6_9 : SS.bdot w6 z9 = true := by decide
theorem sg_ef0_w6_10 : SS.bdot w6 z10 = true := by decide
theorem sg_ef0_w6_11 : SS.bdot w6 z11 = true := by decide
theorem sg_ef0_w6_12 : SS.bdot w6 z12 = true := by decide
theorem sg_ef0_w6_13 : SS.bdot w6 z13 = true := by decide
theorem sg_ef0_w6_14 : SS.bdot w6 z14 = true := by decide
theorem sg_ef0_w6_15 : SS.bdot w6 z15 = false := by decide
theorem ex_ef0_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w6 = - star (c y0) * d z0 + star (c y1) * d z1 + star (c y2) * d z2 + star (c y3) * d z3 + star (c y4) * d z4 + star (c y5) * d z5 + star (c y6) * d z6 - star (c y7) * d z7 + star (c y8) * d z8 - star (c y9) * d z9 - star (c y10) * d z10 - star (c y11) * d z11 - star (c y12) * d z12 - star (c y13) * d z13 - star (c y14) * d z14 + star (c y15) * d z15 := by
  unfold offSum
  rw [incidence_ef0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef0_0, flip_ef0_1, flip_ef0_2, flip_ef0_3, flip_ef0_4, flip_ef0_5, flip_ef0_6, flip_ef0_7, flip_ef0_8, flip_ef0_9, flip_ef0_10, flip_ef0_11, flip_ef0_12, flip_ef0_13, flip_ef0_14, flip_ef0_15]
  simp only [sg_ef0_w6_0, sg_ef0_w6_1, sg_ef0_w6_2, sg_ef0_w6_3, sg_ef0_w6_4, sg_ef0_w6_5, sg_ef0_w6_6, sg_ef0_w6_7, sg_ef0_w6_8, sg_ef0_w6_9, sg_ef0_w6_10, sg_ef0_w6_11, sg_ef0_w6_12, sg_ef0_w6_13, sg_ef0_w6_14, sg_ef0_w6_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem incidence_ef1 :
    S1.filter (fun y => SS.bxor y ef1 ∈ S0) = {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15} := by decide
theorem flip_ef1_0 : SS.bxor z0 ef1 = y8 := by decide
theorem flip_ef1_1 : SS.bxor z1 ef1 = y9 := by decide
theorem flip_ef1_2 : SS.bxor z2 ef1 = y10 := by decide
theorem flip_ef1_3 : SS.bxor z3 ef1 = y11 := by decide
theorem flip_ef1_4 : SS.bxor z4 ef1 = y12 := by decide
theorem flip_ef1_5 : SS.bxor z5 ef1 = y13 := by decide
theorem flip_ef1_6 : SS.bxor z6 ef1 = y14 := by decide
theorem flip_ef1_7 : SS.bxor z7 ef1 = y15 := by decide
theorem flip_ef1_8 : SS.bxor z8 ef1 = y0 := by decide
theorem flip_ef1_9 : SS.bxor z9 ef1 = y1 := by decide
theorem flip_ef1_10 : SS.bxor z10 ef1 = y2 := by decide
theorem flip_ef1_11 : SS.bxor z11 ef1 = y3 := by decide
theorem flip_ef1_12 : SS.bxor z12 ef1 = y4 := by decide
theorem flip_ef1_13 : SS.bxor z13 ef1 = y5 := by decide
theorem flip_ef1_14 : SS.bxor z14 ef1 = y6 := by decide
theorem flip_ef1_15 : SS.bxor z15 ef1 = y7 := by decide
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
    offSum c d ef1 w0 = star (c y8) * d z0 + star (c y9) * d z1 + star (c y10) * d z2 + star (c y11) * d z3 + star (c y12) * d z4 + star (c y13) * d z5 + star (c y14) * d z6 + star (c y15) * d z7 + star (c y0) * d z8 + star (c y1) * d z9 + star (c y2) * d z10 + star (c y3) * d z11 + star (c y4) * d z12 + star (c y5) * d z13 + star (c y6) * d z14 + star (c y7) * d z15 := by
  unfold offSum
  rw [incidence_ef1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef1_0, flip_ef1_1, flip_ef1_2, flip_ef1_3, flip_ef1_4, flip_ef1_5, flip_ef1_6, flip_ef1_7, flip_ef1_8, flip_ef1_9, flip_ef1_10, flip_ef1_11, flip_ef1_12, flip_ef1_13, flip_ef1_14, flip_ef1_15]
  simp only [sg_ef1_w0_0, sg_ef1_w0_1, sg_ef1_w0_2, sg_ef1_w0_3, sg_ef1_w0_4, sg_ef1_w0_5, sg_ef1_w0_6, sg_ef1_w0_7, sg_ef1_w0_8, sg_ef1_w0_9, sg_ef1_w0_10, sg_ef1_w0_11, sg_ef1_w0_12, sg_ef1_w0_13, sg_ef1_w0_14, sg_ef1_w0_15, SixQubit.signMul_false]
  try ring
theorem sg_ef1_w1_0 : SS.bdot w1 z0 = true := by decide
theorem sg_ef1_w1_1 : SS.bdot w1 z1 = false := by decide
theorem sg_ef1_w1_2 : SS.bdot w1 z2 = false := by decide
theorem sg_ef1_w1_3 : SS.bdot w1 z3 = false := by decide
theorem sg_ef1_w1_4 : SS.bdot w1 z4 = false := by decide
theorem sg_ef1_w1_5 : SS.bdot w1 z5 = false := by decide
theorem sg_ef1_w1_6 : SS.bdot w1 z6 = false := by decide
theorem sg_ef1_w1_7 : SS.bdot w1 z7 = true := by decide
theorem sg_ef1_w1_8 : SS.bdot w1 z8 = true := by decide
theorem sg_ef1_w1_9 : SS.bdot w1 z9 = false := by decide
theorem sg_ef1_w1_10 : SS.bdot w1 z10 = false := by decide
theorem sg_ef1_w1_11 : SS.bdot w1 z11 = false := by decide
theorem sg_ef1_w1_12 : SS.bdot w1 z12 = false := by decide
theorem sg_ef1_w1_13 : SS.bdot w1 z13 = false := by decide
theorem sg_ef1_w1_14 : SS.bdot w1 z14 = false := by decide
theorem sg_ef1_w1_15 : SS.bdot w1 z15 = true := by decide
theorem ex_ef1_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w1 = - star (c y8) * d z0 + star (c y9) * d z1 + star (c y10) * d z2 + star (c y11) * d z3 + star (c y12) * d z4 + star (c y13) * d z5 + star (c y14) * d z6 - star (c y15) * d z7 - star (c y0) * d z8 + star (c y1) * d z9 + star (c y2) * d z10 + star (c y3) * d z11 + star (c y4) * d z12 + star (c y5) * d z13 + star (c y6) * d z14 - star (c y7) * d z15 := by
  unfold offSum
  rw [incidence_ef1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef1_0, flip_ef1_1, flip_ef1_2, flip_ef1_3, flip_ef1_4, flip_ef1_5, flip_ef1_6, flip_ef1_7, flip_ef1_8, flip_ef1_9, flip_ef1_10, flip_ef1_11, flip_ef1_12, flip_ef1_13, flip_ef1_14, flip_ef1_15]
  simp only [sg_ef1_w1_0, sg_ef1_w1_1, sg_ef1_w1_2, sg_ef1_w1_3, sg_ef1_w1_4, sg_ef1_w1_5, sg_ef1_w1_6, sg_ef1_w1_7, sg_ef1_w1_8, sg_ef1_w1_9, sg_ef1_w1_10, sg_ef1_w1_11, sg_ef1_w1_12, sg_ef1_w1_13, sg_ef1_w1_14, sg_ef1_w1_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef1_w5_0 : SS.bdot w5 z0 = false := by decide
theorem sg_ef1_w5_1 : SS.bdot w5 z1 = false := by decide
theorem sg_ef1_w5_2 : SS.bdot w5 z2 = false := by decide
theorem sg_ef1_w5_3 : SS.bdot w5 z3 = false := by decide
theorem sg_ef1_w5_4 : SS.bdot w5 z4 = false := by decide
theorem sg_ef1_w5_5 : SS.bdot w5 z5 = false := by decide
theorem sg_ef1_w5_6 : SS.bdot w5 z6 = false := by decide
theorem sg_ef1_w5_7 : SS.bdot w5 z7 = false := by decide
theorem sg_ef1_w5_8 : SS.bdot w5 z8 = true := by decide
theorem sg_ef1_w5_9 : SS.bdot w5 z9 = true := by decide
theorem sg_ef1_w5_10 : SS.bdot w5 z10 = true := by decide
theorem sg_ef1_w5_11 : SS.bdot w5 z11 = true := by decide
theorem sg_ef1_w5_12 : SS.bdot w5 z12 = true := by decide
theorem sg_ef1_w5_13 : SS.bdot w5 z13 = true := by decide
theorem sg_ef1_w5_14 : SS.bdot w5 z14 = true := by decide
theorem sg_ef1_w5_15 : SS.bdot w5 z15 = true := by decide
theorem ex_ef1_w5 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w5 = star (c y8) * d z0 + star (c y9) * d z1 + star (c y10) * d z2 + star (c y11) * d z3 + star (c y12) * d z4 + star (c y13) * d z5 + star (c y14) * d z6 + star (c y15) * d z7 - star (c y0) * d z8 - star (c y1) * d z9 - star (c y2) * d z10 - star (c y3) * d z11 - star (c y4) * d z12 - star (c y5) * d z13 - star (c y6) * d z14 - star (c y7) * d z15 := by
  unfold offSum
  rw [incidence_ef1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef1_0, flip_ef1_1, flip_ef1_2, flip_ef1_3, flip_ef1_4, flip_ef1_5, flip_ef1_6, flip_ef1_7, flip_ef1_8, flip_ef1_9, flip_ef1_10, flip_ef1_11, flip_ef1_12, flip_ef1_13, flip_ef1_14, flip_ef1_15]
  simp only [sg_ef1_w5_0, sg_ef1_w5_1, sg_ef1_w5_2, sg_ef1_w5_3, sg_ef1_w5_4, sg_ef1_w5_5, sg_ef1_w5_6, sg_ef1_w5_7, sg_ef1_w5_8, sg_ef1_w5_9, sg_ef1_w5_10, sg_ef1_w5_11, sg_ef1_w5_12, sg_ef1_w5_13, sg_ef1_w5_14, sg_ef1_w5_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef1_w6_0 : SS.bdot w6 z0 = true := by decide
theorem sg_ef1_w6_1 : SS.bdot w6 z1 = false := by decide
theorem sg_ef1_w6_2 : SS.bdot w6 z2 = false := by decide
theorem sg_ef1_w6_3 : SS.bdot w6 z3 = false := by decide
theorem sg_ef1_w6_4 : SS.bdot w6 z4 = false := by decide
theorem sg_ef1_w6_5 : SS.bdot w6 z5 = false := by decide
theorem sg_ef1_w6_6 : SS.bdot w6 z6 = false := by decide
theorem sg_ef1_w6_7 : SS.bdot w6 z7 = true := by decide
theorem sg_ef1_w6_8 : SS.bdot w6 z8 = false := by decide
theorem sg_ef1_w6_9 : SS.bdot w6 z9 = true := by decide
theorem sg_ef1_w6_10 : SS.bdot w6 z10 = true := by decide
theorem sg_ef1_w6_11 : SS.bdot w6 z11 = true := by decide
theorem sg_ef1_w6_12 : SS.bdot w6 z12 = true := by decide
theorem sg_ef1_w6_13 : SS.bdot w6 z13 = true := by decide
theorem sg_ef1_w6_14 : SS.bdot w6 z14 = true := by decide
theorem sg_ef1_w6_15 : SS.bdot w6 z15 = false := by decide
theorem ex_ef1_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w6 = - star (c y8) * d z0 + star (c y9) * d z1 + star (c y10) * d z2 + star (c y11) * d z3 + star (c y12) * d z4 + star (c y13) * d z5 + star (c y14) * d z6 - star (c y15) * d z7 + star (c y0) * d z8 - star (c y1) * d z9 - star (c y2) * d z10 - star (c y3) * d z11 - star (c y4) * d z12 - star (c y5) * d z13 - star (c y6) * d z14 + star (c y7) * d z15 := by
  unfold offSum
  rw [incidence_ef1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef1_0, flip_ef1_1, flip_ef1_2, flip_ef1_3, flip_ef1_4, flip_ef1_5, flip_ef1_6, flip_ef1_7, flip_ef1_8, flip_ef1_9, flip_ef1_10, flip_ef1_11, flip_ef1_12, flip_ef1_13, flip_ef1_14, flip_ef1_15]
  simp only [sg_ef1_w6_0, sg_ef1_w6_1, sg_ef1_w6_2, sg_ef1_w6_3, sg_ef1_w6_4, sg_ef1_w6_5, sg_ef1_w6_6, sg_ef1_w6_7, sg_ef1_w6_8, sg_ef1_w6_9, sg_ef1_w6_10, sg_ef1_w6_11, sg_ef1_w6_12, sg_ef1_w6_13, sg_ef1_w6_14, sg_ef1_w6_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem incidence_ef2 :
    S1.filter (fun y => SS.bxor y ef2 ∈ S0) = {z0, z1, z6, z7, z8, z9, z14, z15} := by decide
theorem flip_ef2_0 : SS.bxor z0 ef2 = y6 := by decide
theorem flip_ef2_1 : SS.bxor z1 ef2 = y7 := by decide
theorem flip_ef2_6 : SS.bxor z6 ef2 = y0 := by decide
theorem flip_ef2_7 : SS.bxor z7 ef2 = y1 := by decide
theorem flip_ef2_8 : SS.bxor z8 ef2 = y14 := by decide
theorem flip_ef2_9 : SS.bxor z9 ef2 = y15 := by decide
theorem flip_ef2_14 : SS.bxor z14 ef2 = y8 := by decide
theorem flip_ef2_15 : SS.bxor z15 ef2 = y9 := by decide
theorem sg_ef2_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg_ef2_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg_ef2_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg_ef2_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg_ef2_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_ef2_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg_ef2_w0_14 : SS.bdot w0 z14 = false := by decide
theorem sg_ef2_w0_15 : SS.bdot w0 z15 = false := by decide
theorem ex_ef2_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w0 = star (c y6) * d z0 + star (c y7) * d z1 + star (c y0) * d z6 + star (c y1) * d z7 + star (c y14) * d z8 + star (c y15) * d z9 + star (c y8) * d z14 + star (c y9) * d z15 := by
  unfold offSum
  rw [incidence_ef2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef2_0, flip_ef2_1, flip_ef2_6, flip_ef2_7, flip_ef2_8, flip_ef2_9, flip_ef2_14, flip_ef2_15]
  simp only [sg_ef2_w0_0, sg_ef2_w0_1, sg_ef2_w0_6, sg_ef2_w0_7, sg_ef2_w0_8, sg_ef2_w0_9, sg_ef2_w0_14, sg_ef2_w0_15, SixQubit.signMul_false]
  try ring
theorem sg_ef2_w4_0 : SS.bdot w4 z0 = false := by decide
theorem sg_ef2_w4_1 : SS.bdot w4 z1 = false := by decide
theorem sg_ef2_w4_6 : SS.bdot w4 z6 = true := by decide
theorem sg_ef2_w4_7 : SS.bdot w4 z7 = true := by decide
theorem sg_ef2_w4_8 : SS.bdot w4 z8 = false := by decide
theorem sg_ef2_w4_9 : SS.bdot w4 z9 = false := by decide
theorem sg_ef2_w4_14 : SS.bdot w4 z14 = true := by decide
theorem sg_ef2_w4_15 : SS.bdot w4 z15 = true := by decide
theorem ex_ef2_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w4 = star (c y6) * d z0 + star (c y7) * d z1 - star (c y0) * d z6 - star (c y1) * d z7 + star (c y14) * d z8 + star (c y15) * d z9 - star (c y8) * d z14 - star (c y9) * d z15 := by
  unfold offSum
  rw [incidence_ef2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef2_0, flip_ef2_1, flip_ef2_6, flip_ef2_7, flip_ef2_8, flip_ef2_9, flip_ef2_14, flip_ef2_15]
  simp only [sg_ef2_w4_0, sg_ef2_w4_1, sg_ef2_w4_6, sg_ef2_w4_7, sg_ef2_w4_8, sg_ef2_w4_9, sg_ef2_w4_14, sg_ef2_w4_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem incidence_ef3 :
    S1.filter (fun y => SS.bxor y ef3 ∈ S0) = {z0, z1, z6, z7, z8, z9, z14, z15} := by decide
theorem flip_ef3_0 : SS.bxor z0 ef3 = y1 := by decide
theorem flip_ef3_1 : SS.bxor z1 ef3 = y0 := by decide
theorem flip_ef3_6 : SS.bxor z6 ef3 = y7 := by decide
theorem flip_ef3_7 : SS.bxor z7 ef3 = y6 := by decide
theorem flip_ef3_8 : SS.bxor z8 ef3 = y9 := by decide
theorem flip_ef3_9 : SS.bxor z9 ef3 = y8 := by decide
theorem flip_ef3_14 : SS.bxor z14 ef3 = y15 := by decide
theorem flip_ef3_15 : SS.bxor z15 ef3 = y14 := by decide
theorem sg_ef3_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg_ef3_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg_ef3_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg_ef3_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg_ef3_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_ef3_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg_ef3_w0_14 : SS.bdot w0 z14 = false := by decide
theorem sg_ef3_w0_15 : SS.bdot w0 z15 = false := by decide
theorem ex_ef3_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w0 = star (c y1) * d z0 + star (c y0) * d z1 + star (c y7) * d z6 + star (c y6) * d z7 + star (c y9) * d z8 + star (c y8) * d z9 + star (c y15) * d z14 + star (c y14) * d z15 := by
  unfold offSum
  rw [incidence_ef3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef3_0, flip_ef3_1, flip_ef3_6, flip_ef3_7, flip_ef3_8, flip_ef3_9, flip_ef3_14, flip_ef3_15]
  simp only [sg_ef3_w0_0, sg_ef3_w0_1, sg_ef3_w0_6, sg_ef3_w0_7, sg_ef3_w0_8, sg_ef3_w0_9, sg_ef3_w0_14, sg_ef3_w0_15, SixQubit.signMul_false]
  try ring
theorem sg_ef3_w2_0 : SS.bdot w2 z0 = false := by decide
theorem sg_ef3_w2_1 : SS.bdot w2 z1 = true := by decide
theorem sg_ef3_w2_6 : SS.bdot w2 z6 = false := by decide
theorem sg_ef3_w2_7 : SS.bdot w2 z7 = true := by decide
theorem sg_ef3_w2_8 : SS.bdot w2 z8 = false := by decide
theorem sg_ef3_w2_9 : SS.bdot w2 z9 = true := by decide
theorem sg_ef3_w2_14 : SS.bdot w2 z14 = false := by decide
theorem sg_ef3_w2_15 : SS.bdot w2 z15 = true := by decide
theorem ex_ef3_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w2 = star (c y1) * d z0 - star (c y0) * d z1 + star (c y7) * d z6 - star (c y6) * d z7 + star (c y9) * d z8 - star (c y8) * d z9 + star (c y15) * d z14 - star (c y14) * d z15 := by
  unfold offSum
  rw [incidence_ef3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef3_0, flip_ef3_1, flip_ef3_6, flip_ef3_7, flip_ef3_8, flip_ef3_9, flip_ef3_14, flip_ef3_15]
  simp only [sg_ef3_w2_0, sg_ef3_w2_1, sg_ef3_w2_6, sg_ef3_w2_7, sg_ef3_w2_8, sg_ef3_w2_9, sg_ef3_w2_14, sg_ef3_w2_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem incidence_ef4 :
    S1.filter (fun y => SS.bxor y ef4 ∈ S0) = {z0, z2, z5, z7, z8, z10, z13, z15} := by decide
theorem flip_ef4_0 : SS.bxor z0 ef4 = y5 := by decide
theorem flip_ef4_2 : SS.bxor z2 ef4 = y7 := by decide
theorem flip_ef4_5 : SS.bxor z5 ef4 = y0 := by decide
theorem flip_ef4_7 : SS.bxor z7 ef4 = y2 := by decide
theorem flip_ef4_8 : SS.bxor z8 ef4 = y13 := by decide
theorem flip_ef4_10 : SS.bxor z10 ef4 = y15 := by decide
theorem flip_ef4_13 : SS.bxor z13 ef4 = y8 := by decide
theorem flip_ef4_15 : SS.bxor z15 ef4 = y10 := by decide
theorem sg_ef4_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg_ef4_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg_ef4_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg_ef4_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg_ef4_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_ef4_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg_ef4_w0_13 : SS.bdot w0 z13 = false := by decide
theorem sg_ef4_w0_15 : SS.bdot w0 z15 = false := by decide
theorem ex_ef4_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w0 = star (c y5) * d z0 + star (c y7) * d z2 + star (c y0) * d z5 + star (c y2) * d z7 + star (c y13) * d z8 + star (c y15) * d z10 + star (c y8) * d z13 + star (c y10) * d z15 := by
  unfold offSum
  rw [incidence_ef4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef4_0, flip_ef4_2, flip_ef4_5, flip_ef4_7, flip_ef4_8, flip_ef4_10, flip_ef4_13, flip_ef4_15]
  simp only [sg_ef4_w0_0, sg_ef4_w0_2, sg_ef4_w0_5, sg_ef4_w0_7, sg_ef4_w0_8, sg_ef4_w0_10, sg_ef4_w0_13, sg_ef4_w0_15, SixQubit.signMul_false]
  try ring
theorem sg_ef4_w3_0 : SS.bdot w3 z0 = false := by decide
theorem sg_ef4_w3_2 : SS.bdot w3 z2 = false := by decide
theorem sg_ef4_w3_5 : SS.bdot w3 z5 = true := by decide
theorem sg_ef4_w3_7 : SS.bdot w3 z7 = true := by decide
theorem sg_ef4_w3_8 : SS.bdot w3 z8 = false := by decide
theorem sg_ef4_w3_10 : SS.bdot w3 z10 = false := by decide
theorem sg_ef4_w3_13 : SS.bdot w3 z13 = true := by decide
theorem sg_ef4_w3_15 : SS.bdot w3 z15 = true := by decide
theorem ex_ef4_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w3 = star (c y5) * d z0 + star (c y7) * d z2 - star (c y0) * d z5 - star (c y2) * d z7 + star (c y13) * d z8 + star (c y15) * d z10 - star (c y8) * d z13 - star (c y10) * d z15 := by
  unfold offSum
  rw [incidence_ef4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef4_0, flip_ef4_2, flip_ef4_5, flip_ef4_7, flip_ef4_8, flip_ef4_10, flip_ef4_13, flip_ef4_15]
  simp only [sg_ef4_w3_0, sg_ef4_w3_2, sg_ef4_w3_5, sg_ef4_w3_7, sg_ef4_w3_8, sg_ef4_w3_10, sg_ef4_w3_13, sg_ef4_w3_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem incidence_ef5 :
    S1.filter (fun y => SS.bxor y ef5 ∈ S0) = {z0, z2, z5, z7, z8, z10, z13, z15} := by decide
theorem flip_ef5_0 : SS.bxor z0 ef5 = y2 := by decide
theorem flip_ef5_2 : SS.bxor z2 ef5 = y0 := by decide
theorem flip_ef5_5 : SS.bxor z5 ef5 = y7 := by decide
theorem flip_ef5_7 : SS.bxor z7 ef5 = y5 := by decide
theorem flip_ef5_8 : SS.bxor z8 ef5 = y10 := by decide
theorem flip_ef5_10 : SS.bxor z10 ef5 = y8 := by decide
theorem flip_ef5_13 : SS.bxor z13 ef5 = y15 := by decide
theorem flip_ef5_15 : SS.bxor z15 ef5 = y13 := by decide
theorem sg_ef5_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg_ef5_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg_ef5_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg_ef5_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg_ef5_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_ef5_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg_ef5_w0_13 : SS.bdot w0 z13 = false := by decide
theorem sg_ef5_w0_15 : SS.bdot w0 z15 = false := by decide
theorem ex_ef5_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef5 w0 = star (c y2) * d z0 + star (c y0) * d z2 + star (c y7) * d z5 + star (c y5) * d z7 + star (c y10) * d z8 + star (c y8) * d z10 + star (c y15) * d z13 + star (c y13) * d z15 := by
  unfold offSum
  rw [incidence_ef5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef5_0, flip_ef5_2, flip_ef5_5, flip_ef5_7, flip_ef5_8, flip_ef5_10, flip_ef5_13, flip_ef5_15]
  simp only [sg_ef5_w0_0, sg_ef5_w0_2, sg_ef5_w0_5, sg_ef5_w0_7, sg_ef5_w0_8, sg_ef5_w0_10, sg_ef5_w0_13, sg_ef5_w0_15, SixQubit.signMul_false]
  try ring
theorem sg_ef5_w2_0 : SS.bdot w2 z0 = false := by decide
theorem sg_ef5_w2_2 : SS.bdot w2 z2 = true := by decide
theorem sg_ef5_w2_5 : SS.bdot w2 z5 = false := by decide
theorem sg_ef5_w2_7 : SS.bdot w2 z7 = true := by decide
theorem sg_ef5_w2_8 : SS.bdot w2 z8 = false := by decide
theorem sg_ef5_w2_10 : SS.bdot w2 z10 = true := by decide
theorem sg_ef5_w2_13 : SS.bdot w2 z13 = false := by decide
theorem sg_ef5_w2_15 : SS.bdot w2 z15 = true := by decide
theorem ex_ef5_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef5 w2 = star (c y2) * d z0 - star (c y0) * d z2 + star (c y7) * d z5 - star (c y5) * d z7 + star (c y10) * d z8 - star (c y8) * d z10 + star (c y15) * d z13 - star (c y13) * d z15 := by
  unfold offSum
  rw [incidence_ef5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef5_0, flip_ef5_2, flip_ef5_5, flip_ef5_7, flip_ef5_8, flip_ef5_10, flip_ef5_13, flip_ef5_15]
  simp only [sg_ef5_w2_0, sg_ef5_w2_2, sg_ef5_w2_5, sg_ef5_w2_7, sg_ef5_w2_8, sg_ef5_w2_10, sg_ef5_w2_13, sg_ef5_w2_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem incidence_ef6 :
    S1.filter (fun y => SS.bxor y ef6 ∈ S0) = {z0, z3, z4, z7, z8, z11, z12, z15} := by decide
theorem flip_ef6_0 : SS.bxor z0 ef6 = y4 := by decide
theorem flip_ef6_3 : SS.bxor z3 ef6 = y7 := by decide
theorem flip_ef6_4 : SS.bxor z4 ef6 = y0 := by decide
theorem flip_ef6_7 : SS.bxor z7 ef6 = y3 := by decide
theorem flip_ef6_8 : SS.bxor z8 ef6 = y12 := by decide
theorem flip_ef6_11 : SS.bxor z11 ef6 = y15 := by decide
theorem flip_ef6_12 : SS.bxor z12 ef6 = y8 := by decide
theorem flip_ef6_15 : SS.bxor z15 ef6 = y11 := by decide
theorem sg_ef6_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg_ef6_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg_ef6_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg_ef6_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg_ef6_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_ef6_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg_ef6_w0_12 : SS.bdot w0 z12 = false := by decide
theorem sg_ef6_w0_15 : SS.bdot w0 z15 = false := by decide
theorem ex_ef6_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w0 = star (c y4) * d z0 + star (c y7) * d z3 + star (c y0) * d z4 + star (c y3) * d z7 + star (c y12) * d z8 + star (c y15) * d z11 + star (c y8) * d z12 + star (c y11) * d z15 := by
  unfold offSum
  rw [incidence_ef6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef6_0, flip_ef6_3, flip_ef6_4, flip_ef6_7, flip_ef6_8, flip_ef6_11, flip_ef6_12, flip_ef6_15]
  simp only [sg_ef6_w0_0, sg_ef6_w0_3, sg_ef6_w0_4, sg_ef6_w0_7, sg_ef6_w0_8, sg_ef6_w0_11, sg_ef6_w0_12, sg_ef6_w0_15, SixQubit.signMul_false]
  try ring
theorem sg_ef6_w2_0 : SS.bdot w2 z0 = false := by decide
theorem sg_ef6_w2_3 : SS.bdot w2 z3 = false := by decide
theorem sg_ef6_w2_4 : SS.bdot w2 z4 = true := by decide
theorem sg_ef6_w2_7 : SS.bdot w2 z7 = true := by decide
theorem sg_ef6_w2_8 : SS.bdot w2 z8 = false := by decide
theorem sg_ef6_w2_11 : SS.bdot w2 z11 = false := by decide
theorem sg_ef6_w2_12 : SS.bdot w2 z12 = true := by decide
theorem sg_ef6_w2_15 : SS.bdot w2 z15 = true := by decide
theorem ex_ef6_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w2 = star (c y4) * d z0 + star (c y7) * d z3 - star (c y0) * d z4 - star (c y3) * d z7 + star (c y12) * d z8 + star (c y15) * d z11 - star (c y8) * d z12 - star (c y11) * d z15 := by
  unfold offSum
  rw [incidence_ef6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef6_0, flip_ef6_3, flip_ef6_4, flip_ef6_7, flip_ef6_8, flip_ef6_11, flip_ef6_12, flip_ef6_15]
  simp only [sg_ef6_w2_0, sg_ef6_w2_3, sg_ef6_w2_4, sg_ef6_w2_7, sg_ef6_w2_8, sg_ef6_w2_11, sg_ef6_w2_12, sg_ef6_w2_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem incidence_ef7 :
    S1.filter (fun y => SS.bxor y ef7 ∈ S0) = {z0, z3, z4, z7, z8, z11, z12, z15} := by decide
theorem flip_ef7_0 : SS.bxor z0 ef7 = y3 := by decide
theorem flip_ef7_3 : SS.bxor z3 ef7 = y0 := by decide
theorem flip_ef7_4 : SS.bxor z4 ef7 = y7 := by decide
theorem flip_ef7_7 : SS.bxor z7 ef7 = y4 := by decide
theorem flip_ef7_8 : SS.bxor z8 ef7 = y11 := by decide
theorem flip_ef7_11 : SS.bxor z11 ef7 = y8 := by decide
theorem flip_ef7_12 : SS.bxor z12 ef7 = y15 := by decide
theorem flip_ef7_15 : SS.bxor z15 ef7 = y12 := by decide
theorem sg_ef7_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg_ef7_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg_ef7_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg_ef7_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg_ef7_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_ef7_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg_ef7_w0_12 : SS.bdot w0 z12 = false := by decide
theorem sg_ef7_w0_15 : SS.bdot w0 z15 = false := by decide
theorem ex_ef7_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef7 w0 = star (c y3) * d z0 + star (c y0) * d z3 + star (c y7) * d z4 + star (c y4) * d z7 + star (c y11) * d z8 + star (c y8) * d z11 + star (c y15) * d z12 + star (c y12) * d z15 := by
  unfold offSum
  rw [incidence_ef7]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef7_0, flip_ef7_3, flip_ef7_4, flip_ef7_7, flip_ef7_8, flip_ef7_11, flip_ef7_12, flip_ef7_15]
  simp only [sg_ef7_w0_0, sg_ef7_w0_3, sg_ef7_w0_4, sg_ef7_w0_7, sg_ef7_w0_8, sg_ef7_w0_11, sg_ef7_w0_12, sg_ef7_w0_15, SixQubit.signMul_false]
  try ring
theorem sg_ef7_w3_0 : SS.bdot w3 z0 = false := by decide
theorem sg_ef7_w3_3 : SS.bdot w3 z3 = true := by decide
theorem sg_ef7_w3_4 : SS.bdot w3 z4 = false := by decide
theorem sg_ef7_w3_7 : SS.bdot w3 z7 = true := by decide
theorem sg_ef7_w3_8 : SS.bdot w3 z8 = false := by decide
theorem sg_ef7_w3_11 : SS.bdot w3 z11 = true := by decide
theorem sg_ef7_w3_12 : SS.bdot w3 z12 = false := by decide
theorem sg_ef7_w3_15 : SS.bdot w3 z15 = true := by decide
theorem ex_ef7_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef7 w3 = star (c y3) * d z0 - star (c y0) * d z3 + star (c y7) * d z4 - star (c y4) * d z7 + star (c y11) * d z8 - star (c y8) * d z11 + star (c y15) * d z12 - star (c y12) * d z15 := by
  unfold offSum
  rw [incidence_ef7]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef7_0, flip_ef7_3, flip_ef7_4, flip_ef7_7, flip_ef7_8, flip_ef7_11, flip_ef7_12, flip_ef7_15]
  simp only [sg_ef7_w3_0, sg_ef7_w3_3, sg_ef7_w3_4, sg_ef7_w3_7, sg_ef7_w3_8, sg_ef7_w3_11, sg_ef7_w3_12, sg_ef7_w3_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

/-! ## The diagonal layer on the zero-angle qubit -/

def diagBot (c : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ x ∈ S0.filter (fun x => SS.bxor x e ∈ S0),
      SixQubit.signMul (SS.bdot z x) (star (c (SS.bxor x e)) * c x)

def diagTop (dd : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S1),
      SixQubit.signMul (SS.bdot z y) (star (dd (SS.bxor y e)) * dd y)

theorem dincB : S0.filter (fun x => SS.bxor x efA ∈ S0) = {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15} := by decide
theorem dincT : S1.filter (fun y => SS.bxor y efA ∈ S1) = {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15} := by decide
theorem dflipB_0 : SS.bxor y0 efA = y8 := by decide
theorem dflipB_1 : SS.bxor y1 efA = y9 := by decide
theorem dflipB_2 : SS.bxor y2 efA = y10 := by decide
theorem dflipB_3 : SS.bxor y3 efA = y11 := by decide
theorem dflipB_4 : SS.bxor y4 efA = y12 := by decide
theorem dflipB_5 : SS.bxor y5 efA = y13 := by decide
theorem dflipB_6 : SS.bxor y6 efA = y14 := by decide
theorem dflipB_7 : SS.bxor y7 efA = y15 := by decide
theorem dflipB_8 : SS.bxor y8 efA = y0 := by decide
theorem dflipB_9 : SS.bxor y9 efA = y1 := by decide
theorem dflipB_10 : SS.bxor y10 efA = y2 := by decide
theorem dflipB_11 : SS.bxor y11 efA = y3 := by decide
theorem dflipB_12 : SS.bxor y12 efA = y4 := by decide
theorem dflipB_13 : SS.bxor y13 efA = y5 := by decide
theorem dflipB_14 : SS.bxor y14 efA = y6 := by decide
theorem dflipB_15 : SS.bxor y15 efA = y7 := by decide
theorem dflipT_0 : SS.bxor z0 efA = z8 := by decide
theorem dflipT_1 : SS.bxor z1 efA = z9 := by decide
theorem dflipT_2 : SS.bxor z2 efA = z10 := by decide
theorem dflipT_3 : SS.bxor z3 efA = z11 := by decide
theorem dflipT_4 : SS.bxor z4 efA = z12 := by decide
theorem dflipT_5 : SS.bxor z5 efA = z13 := by decide
theorem dflipT_6 : SS.bxor z6 efA = z14 := by decide
theorem dflipT_7 : SS.bxor z7 efA = z15 := by decide
theorem dflipT_8 : SS.bxor z8 efA = z0 := by decide
theorem dflipT_9 : SS.bxor z9 efA = z1 := by decide
theorem dflipT_10 : SS.bxor z10 efA = z2 := by decide
theorem dflipT_11 : SS.bxor z11 efA = z3 := by decide
theorem dflipT_12 : SS.bxor z12 efA = z4 := by decide
theorem dflipT_13 : SS.bxor z13 efA = z5 := by decide
theorem dflipT_14 : SS.bxor z14 efA = z6 := by decide
theorem dflipT_15 : SS.bxor z15 efA = z7 := by decide

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
theorem dexB_w0 (c : SS.BitString 6 -> ℂ) :
    diagBot c efA w0 = star (c y8) * c y0 + star (c y9) * c y1 + star (c y10) * c y2 + star (c y11) * c y3 + star (c y12) * c y4 + star (c y13) * c y5 + star (c y14) * c y6 + star (c y15) * c y7 + star (c y0) * c y8 + star (c y1) * c y9 + star (c y2) * c y10 + star (c y3) * c y11 + star (c y4) * c y12 + star (c y5) * c y13 + star (c y6) * c y14 + star (c y7) * c y15 := by
  unfold diagBot
  rw [dincB]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipB_0, dflipB_1, dflipB_2, dflipB_3, dflipB_4, dflipB_5, dflipB_6, dflipB_7, dflipB_8, dflipB_9, dflipB_10, dflipB_11, dflipB_12, dflipB_13, dflipB_14, dflipB_15]
  simp only [dsB_w0_0, dsB_w0_1, dsB_w0_2, dsB_w0_3, dsB_w0_4, dsB_w0_5, dsB_w0_6, dsB_w0_7, dsB_w0_8, dsB_w0_9, dsB_w0_10, dsB_w0_11, dsB_w0_12, dsB_w0_13, dsB_w0_14, dsB_w0_15, SixQubit.signMul_false]
  try ring
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
theorem dexT_w0 (dd : SS.BitString 6 -> ℂ) :
    diagTop dd efA w0 = star (dd z8) * dd z0 + star (dd z9) * dd z1 + star (dd z10) * dd z2 + star (dd z11) * dd z3 + star (dd z12) * dd z4 + star (dd z13) * dd z5 + star (dd z14) * dd z6 + star (dd z15) * dd z7 + star (dd z0) * dd z8 + star (dd z1) * dd z9 + star (dd z2) * dd z10 + star (dd z3) * dd z11 + star (dd z4) * dd z12 + star (dd z5) * dd z13 + star (dd z6) * dd z14 + star (dd z7) * dd z15 := by
  unfold diagTop
  rw [dincT]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipT_0, dflipT_1, dflipT_2, dflipT_3, dflipT_4, dflipT_5, dflipT_6, dflipT_7, dflipT_8, dflipT_9, dflipT_10, dflipT_11, dflipT_12, dflipT_13, dflipT_14, dflipT_15]
  simp only [dsT_w0_0, dsT_w0_1, dsT_w0_2, dsT_w0_3, dsT_w0_4, dsT_w0_5, dsT_w0_6, dsT_w0_7, dsT_w0_8, dsT_w0_9, dsT_w0_10, dsT_w0_11, dsT_w0_12, dsT_w0_13, dsT_w0_14, dsT_w0_15, SixQubit.signMul_false]
  try ring

theorem dsB_w1_0 : SS.bdot w1 y0 = false := by decide
theorem dsB_w1_1 : SS.bdot w1 y1 = true := by decide
theorem dsB_w1_2 : SS.bdot w1 y2 = true := by decide
theorem dsB_w1_3 : SS.bdot w1 y3 = true := by decide
theorem dsB_w1_4 : SS.bdot w1 y4 = true := by decide
theorem dsB_w1_5 : SS.bdot w1 y5 = true := by decide
theorem dsB_w1_6 : SS.bdot w1 y6 = true := by decide
theorem dsB_w1_7 : SS.bdot w1 y7 = false := by decide
theorem dsB_w1_8 : SS.bdot w1 y8 = false := by decide
theorem dsB_w1_9 : SS.bdot w1 y9 = true := by decide
theorem dsB_w1_10 : SS.bdot w1 y10 = true := by decide
theorem dsB_w1_11 : SS.bdot w1 y11 = true := by decide
theorem dsB_w1_12 : SS.bdot w1 y12 = true := by decide
theorem dsB_w1_13 : SS.bdot w1 y13 = true := by decide
theorem dsB_w1_14 : SS.bdot w1 y14 = true := by decide
theorem dsB_w1_15 : SS.bdot w1 y15 = false := by decide
theorem dexB_w1 (c : SS.BitString 6 -> ℂ) :
    diagBot c efA w1 = star (c y8) * c y0 - star (c y9) * c y1 - star (c y10) * c y2 - star (c y11) * c y3 - star (c y12) * c y4 - star (c y13) * c y5 - star (c y14) * c y6 + star (c y15) * c y7 + star (c y0) * c y8 - star (c y1) * c y9 - star (c y2) * c y10 - star (c y3) * c y11 - star (c y4) * c y12 - star (c y5) * c y13 - star (c y6) * c y14 + star (c y7) * c y15 := by
  unfold diagBot
  rw [dincB]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipB_0, dflipB_1, dflipB_2, dflipB_3, dflipB_4, dflipB_5, dflipB_6, dflipB_7, dflipB_8, dflipB_9, dflipB_10, dflipB_11, dflipB_12, dflipB_13, dflipB_14, dflipB_15]
  simp only [dsB_w1_0, dsB_w1_1, dsB_w1_2, dsB_w1_3, dsB_w1_4, dsB_w1_5, dsB_w1_6, dsB_w1_7, dsB_w1_8, dsB_w1_9, dsB_w1_10, dsB_w1_11, dsB_w1_12, dsB_w1_13, dsB_w1_14, dsB_w1_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem dsT_w1_0 : SS.bdot w1 z0 = true := by decide
theorem dsT_w1_1 : SS.bdot w1 z1 = false := by decide
theorem dsT_w1_2 : SS.bdot w1 z2 = false := by decide
theorem dsT_w1_3 : SS.bdot w1 z3 = false := by decide
theorem dsT_w1_4 : SS.bdot w1 z4 = false := by decide
theorem dsT_w1_5 : SS.bdot w1 z5 = false := by decide
theorem dsT_w1_6 : SS.bdot w1 z6 = false := by decide
theorem dsT_w1_7 : SS.bdot w1 z7 = true := by decide
theorem dsT_w1_8 : SS.bdot w1 z8 = true := by decide
theorem dsT_w1_9 : SS.bdot w1 z9 = false := by decide
theorem dsT_w1_10 : SS.bdot w1 z10 = false := by decide
theorem dsT_w1_11 : SS.bdot w1 z11 = false := by decide
theorem dsT_w1_12 : SS.bdot w1 z12 = false := by decide
theorem dsT_w1_13 : SS.bdot w1 z13 = false := by decide
theorem dsT_w1_14 : SS.bdot w1 z14 = false := by decide
theorem dsT_w1_15 : SS.bdot w1 z15 = true := by decide
theorem dexT_w1 (dd : SS.BitString 6 -> ℂ) :
    diagTop dd efA w1 = - star (dd z8) * dd z0 + star (dd z9) * dd z1 + star (dd z10) * dd z2 + star (dd z11) * dd z3 + star (dd z12) * dd z4 + star (dd z13) * dd z5 + star (dd z14) * dd z6 - star (dd z15) * dd z7 - star (dd z0) * dd z8 + star (dd z1) * dd z9 + star (dd z2) * dd z10 + star (dd z3) * dd z11 + star (dd z4) * dd z12 + star (dd z5) * dd z13 + star (dd z6) * dd z14 - star (dd z7) * dd z15 := by
  unfold diagTop
  rw [dincT]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipT_0, dflipT_1, dflipT_2, dflipT_3, dflipT_4, dflipT_5, dflipT_6, dflipT_7, dflipT_8, dflipT_9, dflipT_10, dflipT_11, dflipT_12, dflipT_13, dflipT_14, dflipT_15]
  simp only [dsT_w1_0, dsT_w1_1, dsT_w1_2, dsT_w1_3, dsT_w1_4, dsT_w1_5, dsT_w1_6, dsT_w1_7, dsT_w1_8, dsT_w1_9, dsT_w1_10, dsT_w1_11, dsT_w1_12, dsT_w1_13, dsT_w1_14, dsT_w1_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dsB_w5_0 : SS.bdot w5 y0 = false := by decide
theorem dsB_w5_1 : SS.bdot w5 y1 = false := by decide
theorem dsB_w5_2 : SS.bdot w5 y2 = false := by decide
theorem dsB_w5_3 : SS.bdot w5 y3 = false := by decide
theorem dsB_w5_4 : SS.bdot w5 y4 = false := by decide
theorem dsB_w5_5 : SS.bdot w5 y5 = false := by decide
theorem dsB_w5_6 : SS.bdot w5 y6 = false := by decide
theorem dsB_w5_7 : SS.bdot w5 y7 = false := by decide
theorem dsB_w5_8 : SS.bdot w5 y8 = true := by decide
theorem dsB_w5_9 : SS.bdot w5 y9 = true := by decide
theorem dsB_w5_10 : SS.bdot w5 y10 = true := by decide
theorem dsB_w5_11 : SS.bdot w5 y11 = true := by decide
theorem dsB_w5_12 : SS.bdot w5 y12 = true := by decide
theorem dsB_w5_13 : SS.bdot w5 y13 = true := by decide
theorem dsB_w5_14 : SS.bdot w5 y14 = true := by decide
theorem dsB_w5_15 : SS.bdot w5 y15 = true := by decide
theorem dexB_w5 (c : SS.BitString 6 -> ℂ) :
    diagBot c efA w5 = star (c y8) * c y0 + star (c y9) * c y1 + star (c y10) * c y2 + star (c y11) * c y3 + star (c y12) * c y4 + star (c y13) * c y5 + star (c y14) * c y6 + star (c y15) * c y7 - star (c y0) * c y8 - star (c y1) * c y9 - star (c y2) * c y10 - star (c y3) * c y11 - star (c y4) * c y12 - star (c y5) * c y13 - star (c y6) * c y14 - star (c y7) * c y15 := by
  unfold diagBot
  rw [dincB]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipB_0, dflipB_1, dflipB_2, dflipB_3, dflipB_4, dflipB_5, dflipB_6, dflipB_7, dflipB_8, dflipB_9, dflipB_10, dflipB_11, dflipB_12, dflipB_13, dflipB_14, dflipB_15]
  simp only [dsB_w5_0, dsB_w5_1, dsB_w5_2, dsB_w5_3, dsB_w5_4, dsB_w5_5, dsB_w5_6, dsB_w5_7, dsB_w5_8, dsB_w5_9, dsB_w5_10, dsB_w5_11, dsB_w5_12, dsB_w5_13, dsB_w5_14, dsB_w5_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem dsT_w5_0 : SS.bdot w5 z0 = false := by decide
theorem dsT_w5_1 : SS.bdot w5 z1 = false := by decide
theorem dsT_w5_2 : SS.bdot w5 z2 = false := by decide
theorem dsT_w5_3 : SS.bdot w5 z3 = false := by decide
theorem dsT_w5_4 : SS.bdot w5 z4 = false := by decide
theorem dsT_w5_5 : SS.bdot w5 z5 = false := by decide
theorem dsT_w5_6 : SS.bdot w5 z6 = false := by decide
theorem dsT_w5_7 : SS.bdot w5 z7 = false := by decide
theorem dsT_w5_8 : SS.bdot w5 z8 = true := by decide
theorem dsT_w5_9 : SS.bdot w5 z9 = true := by decide
theorem dsT_w5_10 : SS.bdot w5 z10 = true := by decide
theorem dsT_w5_11 : SS.bdot w5 z11 = true := by decide
theorem dsT_w5_12 : SS.bdot w5 z12 = true := by decide
theorem dsT_w5_13 : SS.bdot w5 z13 = true := by decide
theorem dsT_w5_14 : SS.bdot w5 z14 = true := by decide
theorem dsT_w5_15 : SS.bdot w5 z15 = true := by decide
theorem dexT_w5 (dd : SS.BitString 6 -> ℂ) :
    diagTop dd efA w5 = star (dd z8) * dd z0 + star (dd z9) * dd z1 + star (dd z10) * dd z2 + star (dd z11) * dd z3 + star (dd z12) * dd z4 + star (dd z13) * dd z5 + star (dd z14) * dd z6 + star (dd z15) * dd z7 - star (dd z0) * dd z8 - star (dd z1) * dd z9 - star (dd z2) * dd z10 - star (dd z3) * dd z11 - star (dd z4) * dd z12 - star (dd z5) * dd z13 - star (dd z6) * dd z14 - star (dd z7) * dd z15 := by
  unfold diagTop
  rw [dincT]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipT_0, dflipT_1, dflipT_2, dflipT_3, dflipT_4, dflipT_5, dflipT_6, dflipT_7, dflipT_8, dflipT_9, dflipT_10, dflipT_11, dflipT_12, dflipT_13, dflipT_14, dflipT_15]
  simp only [dsT_w5_0, dsT_w5_1, dsT_w5_2, dsT_w5_3, dsT_w5_4, dsT_w5_5, dsT_w5_6, dsT_w5_7, dsT_w5_8, dsT_w5_9, dsT_w5_10, dsT_w5_11, dsT_w5_12, dsT_w5_13, dsT_w5_14, dsT_w5_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dsB_w6_0 : SS.bdot w6 y0 = false := by decide
theorem dsB_w6_1 : SS.bdot w6 y1 = true := by decide
theorem dsB_w6_2 : SS.bdot w6 y2 = true := by decide
theorem dsB_w6_3 : SS.bdot w6 y3 = true := by decide
theorem dsB_w6_4 : SS.bdot w6 y4 = true := by decide
theorem dsB_w6_5 : SS.bdot w6 y5 = true := by decide
theorem dsB_w6_6 : SS.bdot w6 y6 = true := by decide
theorem dsB_w6_7 : SS.bdot w6 y7 = false := by decide
theorem dsB_w6_8 : SS.bdot w6 y8 = true := by decide
theorem dsB_w6_9 : SS.bdot w6 y9 = false := by decide
theorem dsB_w6_10 : SS.bdot w6 y10 = false := by decide
theorem dsB_w6_11 : SS.bdot w6 y11 = false := by decide
theorem dsB_w6_12 : SS.bdot w6 y12 = false := by decide
theorem dsB_w6_13 : SS.bdot w6 y13 = false := by decide
theorem dsB_w6_14 : SS.bdot w6 y14 = false := by decide
theorem dsB_w6_15 : SS.bdot w6 y15 = true := by decide
theorem dexB_w6 (c : SS.BitString 6 -> ℂ) :
    diagBot c efA w6 = star (c y8) * c y0 - star (c y9) * c y1 - star (c y10) * c y2 - star (c y11) * c y3 - star (c y12) * c y4 - star (c y13) * c y5 - star (c y14) * c y6 + star (c y15) * c y7 - star (c y0) * c y8 + star (c y1) * c y9 + star (c y2) * c y10 + star (c y3) * c y11 + star (c y4) * c y12 + star (c y5) * c y13 + star (c y6) * c y14 - star (c y7) * c y15 := by
  unfold diagBot
  rw [dincB]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipB_0, dflipB_1, dflipB_2, dflipB_3, dflipB_4, dflipB_5, dflipB_6, dflipB_7, dflipB_8, dflipB_9, dflipB_10, dflipB_11, dflipB_12, dflipB_13, dflipB_14, dflipB_15]
  simp only [dsB_w6_0, dsB_w6_1, dsB_w6_2, dsB_w6_3, dsB_w6_4, dsB_w6_5, dsB_w6_6, dsB_w6_7, dsB_w6_8, dsB_w6_9, dsB_w6_10, dsB_w6_11, dsB_w6_12, dsB_w6_13, dsB_w6_14, dsB_w6_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem dsT_w6_0 : SS.bdot w6 z0 = true := by decide
theorem dsT_w6_1 : SS.bdot w6 z1 = false := by decide
theorem dsT_w6_2 : SS.bdot w6 z2 = false := by decide
theorem dsT_w6_3 : SS.bdot w6 z3 = false := by decide
theorem dsT_w6_4 : SS.bdot w6 z4 = false := by decide
theorem dsT_w6_5 : SS.bdot w6 z5 = false := by decide
theorem dsT_w6_6 : SS.bdot w6 z6 = false := by decide
theorem dsT_w6_7 : SS.bdot w6 z7 = true := by decide
theorem dsT_w6_8 : SS.bdot w6 z8 = false := by decide
theorem dsT_w6_9 : SS.bdot w6 z9 = true := by decide
theorem dsT_w6_10 : SS.bdot w6 z10 = true := by decide
theorem dsT_w6_11 : SS.bdot w6 z11 = true := by decide
theorem dsT_w6_12 : SS.bdot w6 z12 = true := by decide
theorem dsT_w6_13 : SS.bdot w6 z13 = true := by decide
theorem dsT_w6_14 : SS.bdot w6 z14 = true := by decide
theorem dsT_w6_15 : SS.bdot w6 z15 = false := by decide
theorem dexT_w6 (dd : SS.BitString 6 -> ℂ) :
    diagTop dd efA w6 = - star (dd z8) * dd z0 + star (dd z9) * dd z1 + star (dd z10) * dd z2 + star (dd z11) * dd z3 + star (dd z12) * dd z4 + star (dd z13) * dd z5 + star (dd z14) * dd z6 - star (dd z15) * dd z7 + star (dd z0) * dd z8 - star (dd z1) * dd z9 - star (dd z2) * dd z10 - star (dd z3) * dd z11 - star (dd z4) * dd z12 - star (dd z5) * dd z13 - star (dd z6) * dd z14 + star (dd z7) * dd z15 := by
  unfold diagTop
  rw [dincT]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipT_0, dflipT_1, dflipT_2, dflipT_3, dflipT_4, dflipT_5, dflipT_6, dflipT_7, dflipT_8, dflipT_9, dflipT_10, dflipT_11, dflipT_12, dflipT_13, dflipT_14, dflipT_15]
  simp only [dsT_w6_0, dsT_w6_1, dsT_w6_2, dsT_w6_3, dsT_w6_4, dsT_w6_5, dsT_w6_6, dsT_w6_7, dsT_w6_8, dsT_w6_9, dsT_w6_10, dsT_w6_11, dsT_w6_12, dsT_w6_13, dsT_w6_14, dsT_w6_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

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
  m5 : q1 + q2 + q4 + q7 + q9 + q10 + q12 + q15 = r1 + r2 + r4 + r7 + r9 + r10 + r12 + r15
  m6 : q1 + q2 + q3 + q4 + q5 + q6 + q9 + q10 + q11 + q12 + q13 + q14 = r0 + r7 + r8 + r15
  m12 : q12 + q13 + q14 + q15 = r12 + r13 + r14 + r15
  m13 : q10 + q11 + q14 + q15 = r10 + r11 + r14 + r15
  m14 : q9 + q11 + q13 + q15 = r9 + r11 + r13 + r15
  m15 : q9 + q10 + q12 + q15 = r9 + r10 + r12 + r15
  m16 : q9 + q10 + q11 + q12 + q13 + q14 = r8 + r15
  m23 : q6 + q7 + q14 + q15 = r6 + r7 + r14 + r15
  m24 : q5 + q7 + q13 + q15 = r5 + r7 + r13 + r15
  m25 : q4 + q7 + q12 + q15 = r4 + r7 + r12 + r15
  m26 : q4 + q5 + q6 + q12 + q13 + q14 = r7 + r15
  m34 : q3 + q7 + q11 + q15 = r3 + r7 + r11 + r15
  m35 : q2 + q7 + q10 + q15 = r2 + r7 + r10 + r15
  m36 : q2 + q3 + q6 + q10 + q11 + q14 = r7 + r15
  m45 : q1 + q7 + q9 + q15 = r1 + r7 + r9 + r15
  m46 : q1 + q3 + q5 + q9 + q11 + q13 = r7 + r15
  m56 : q1 + q2 + q4 + q9 + q10 + q12 = r7 + r15

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

/-- The anchor masses, the two diagonal entries of the `H = 0` block, and
the total mass of the three complementary pair representatives. -/
theorem MomentSystem.facts {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    q0 + q8 = 1/4 ∧ q7 + q15 = 1/4
    ∧ q0 + q7 = r6 + r5 + r4 + r3 + r2 + r1
    ∧ q8 + q15 = r14 + r13 + r12 + r11 + r10 + r9
    ∧ (r1 + r9) + (r2 + r10) + (r3 + r11) = 1/4 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, m12, m13, m14, m15, m16, m23, m24, m25, m26, m34, m35, m36, m45, m46, m56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-! ## The no-go -/

/-- **Orbit 12 is impossible.** -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11)) (Complex.normSq (c y12)) (Complex.normSq (c y13)) (Complex.normSq (c y14)) (Complex.normSq (c y15))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)) (Complex.normSq (d z12)) (Complex.normSq (d z13)) (Complex.normSq (d z14)) (Complex.normSq (d z15)))
    (ho0 : offSum c d ef0 w0 = 0)
    (ho1 : offSum c d ef0 w1 = 0)
    (ho2 : offSum c d ef0 w5 = 0)
    (ho3 : offSum c d ef0 w6 = 0)
    (ho4 : offSum c d ef1 w0 = 0)
    (ho5 : offSum c d ef1 w1 = 0)
    (ho6 : offSum c d ef1 w5 = 0)
    (ho7 : offSum c d ef1 w6 = 0)
    (ho8 : offSum c d ef2 w0 = 0)
    (ho9 : offSum c d ef2 w4 = 0)
    (ho10 : offSum c d ef3 w0 = 0)
    (ho11 : offSum c d ef3 w2 = 0)
    (ho12 : offSum c d ef4 w0 = 0)
    (ho13 : offSum c d ef4 w3 = 0)
    (ho14 : offSum c d ef5 w0 = 0)
    (ho15 : offSum c d ef5 w2 = 0)
    (ho16 : offSum c d ef6 w0 = 0)
    (ho17 : offSum c d ef6 w2 = 0)
    (ho18 : offSum c d ef7 w0 = 0)
    (ho19 : offSum c d ef7 w3 = 0)
    (hd0 : diagBot c efA w0 = diagTop d efA w0)
    (hd1 : diagBot c efA w1 = diagTop d efA w1)
    (hd2 : diagBot c efA w5 = diagTop d efA w5)
    (hd3 : diagBot c efA w6 = diagTop d efA w6)
    : False := by
  rw [ex_ef0_w0] at ho0
  rw [ex_ef0_w1] at ho1
  rw [ex_ef0_w5] at ho2
  rw [ex_ef0_w6] at ho3
  rw [ex_ef1_w0] at ho4
  rw [ex_ef1_w1] at ho5
  rw [ex_ef1_w5] at ho6
  rw [ex_ef1_w6] at ho7
  rw [ex_ef2_w0] at ho8
  rw [ex_ef2_w4] at ho9
  rw [ex_ef3_w0] at ho10
  rw [ex_ef3_w2] at ho11
  rw [ex_ef4_w0] at ho12
  rw [ex_ef4_w3] at ho13
  rw [ex_ef5_w0] at ho14
  rw [ex_ef5_w2] at ho15
  rw [ex_ef6_w0] at ho16
  rw [ex_ef6_w2] at ho17
  rw [ex_ef7_w0] at ho18
  rw [ex_ef7_w3] at ho19
  rw [dexB_w0, dexT_w0] at hd0
  rw [dexB_w1, dexT_w1] at hd1
  rw [dexB_w5, dexT_w5] at hd2
  rw [dexB_w6, dexT_w6] at hd3
  have K00 : star (c y0) * d z0 + star (c y7) * d z7 = 0 := by
    linear_combination (1/4 : ℂ) * ho0 + (-1/4 : ℂ) * ho1 + (1/4 : ℂ) * ho2 + (-1/4 : ℂ) * ho3
  have K01 : star (c y0) * d z8 + star (c y7) * d z15 = 0 := by
    linear_combination (1/4 : ℂ) * ho4 + (-1/4 : ℂ) * ho5 + (-1/4 : ℂ) * ho6 + (1/4 : ℂ) * ho7
  have K10 : star (c y8) * d z0 + star (c y15) * d z7 = 0 := by
    linear_combination (1/4 : ℂ) * ho4 + (-1/4 : ℂ) * ho5 + (1/4 : ℂ) * ho6 + (-1/4 : ℂ) * ho7
  have K11 : star (c y8) * d z8 + star (c y15) * d z15 = 0 := by
    linear_combination (1/4 : ℂ) * ho0 + (-1/4 : ℂ) * ho1 + (-1/4 : ℂ) * ho2 + (1/4 : ℂ) * ho3
  have Doff : star (c y8) * c y0 + star (c y15) * c y7 = star (d z14) * d z6 + star (d z13) * d z5 + star (d z12) * d z4 + star (d z11) * d z3 + star (d z10) * d z2 + star (d z9) * d z1 := by
    linear_combination (1/4 : ℂ) * hd0 + (1/4 : ℂ) * hd1 + (1/4 : ℂ) * hd2 + (1/4 : ℂ) * hd3
  obtain ⟨hu4, hv4, D0, D1, hsum⟩ := hm.facts
  have hu : (0:ℝ) < Complex.normSq (c y0) + Complex.normSq (c y8) := by linarith
  have hv : (0:ℝ) < Complex.normSq (c y7) + Complex.normSq (c y15) := by linarith
  have htri : (0:ℝ) < Complex.normSq (d z1) + Complex.normSq (d z9) ∨ (0:ℝ) < Complex.normSq (d z2) + Complex.normSq (d z10) ∨ (0:ℝ) < Complex.normSq (d z3) + Complex.normSq (d z11) := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨t1, t2, t3⟩ := hcon
    linarith
  rcases htri with hpos | hpos | hpos
  · have P1 : star (c y6) * d z0 + star (c y14) * d z8
        + (star (c y7) * d z1 + star (c y15) * d z9) = 0 := by
      linear_combination (1/2 : ℂ) * ho8 + (1/2 : ℂ) * ho9
    have P2 : star (c y0) * d z1 + star (c y8) * d z9
        + (star (c y6) * d z7 + star (c y14) * d z15) = 0 := by
      linear_combination (1/2 : ℂ) * ho10 + (-1/2 : ℂ) * ho11
    obtain ⟨hBu, hBv⟩ :=
      SixQubit.Spinor.cancel_perp K00 K01 K10 K11 P1 P2 hu hv
    have D0a : Complex.normSq (c y0) + Complex.normSq (c y7)
        = Complex.normSq (d z1) + Complex.normSq (d z6) + Complex.normSq (d z5) + Complex.normSq (d z4) + Complex.normSq (d z3) + Complex.normSq (d z2) := by linarith
    have D1a : Complex.normSq (c y8) + Complex.normSq (c y15)
        = Complex.normSq (d z9) + Complex.normSq (d z14) + Complex.normSq (d z13) + Complex.normSq (d z12) + Complex.normSq (d z11) + Complex.normSq (d z10) := by linarith
    have Doffa : star (c y8) * c y0 + star (c y15) * c y7
        = star (d z9) * d z1 + star (d z14) * d z6 + star (d z13) * d z5 + star (d z12) * d z4 + star (d z11) * d z3 + star (d z10) * d z2 := by
      linear_combination Doff
    have hz := SixQubit.Spinor.edge_zero D0a D1a Doffa hBu hBv
    linarith
  · have P1 : star (c y5) * d z0 + star (c y13) * d z8
        + (star (c y7) * d z2 + star (c y15) * d z10) = 0 := by
      linear_combination (1/2 : ℂ) * ho12 + (1/2 : ℂ) * ho13
    have P2 : star (c y0) * d z2 + star (c y8) * d z10
        + (star (c y5) * d z7 + star (c y13) * d z15) = 0 := by
      linear_combination (1/2 : ℂ) * ho14 + (-1/2 : ℂ) * ho15
    obtain ⟨hBu, hBv⟩ :=
      SixQubit.Spinor.cancel_perp K00 K01 K10 K11 P1 P2 hu hv
    have D0a : Complex.normSq (c y0) + Complex.normSq (c y7)
        = Complex.normSq (d z2) + Complex.normSq (d z6) + Complex.normSq (d z5) + Complex.normSq (d z4) + Complex.normSq (d z3) + Complex.normSq (d z1) := by linarith
    have D1a : Complex.normSq (c y8) + Complex.normSq (c y15)
        = Complex.normSq (d z10) + Complex.normSq (d z14) + Complex.normSq (d z13) + Complex.normSq (d z12) + Complex.normSq (d z11) + Complex.normSq (d z9) := by linarith
    have Doffa : star (c y8) * c y0 + star (c y15) * c y7
        = star (d z10) * d z2 + star (d z14) * d z6 + star (d z13) * d z5 + star (d z12) * d z4 + star (d z11) * d z3 + star (d z9) * d z1 := by
      linear_combination Doff
    have hz := SixQubit.Spinor.edge_zero D0a D1a Doffa hBu hBv
    linarith
  · have P1 : star (c y4) * d z0 + star (c y12) * d z8
        + (star (c y7) * d z3 + star (c y15) * d z11) = 0 := by
      linear_combination (1/2 : ℂ) * ho16 + (1/2 : ℂ) * ho17
    have P2 : star (c y0) * d z3 + star (c y8) * d z11
        + (star (c y4) * d z7 + star (c y12) * d z15) = 0 := by
      linear_combination (1/2 : ℂ) * ho18 + (-1/2 : ℂ) * ho19
    obtain ⟨hBu, hBv⟩ :=
      SixQubit.Spinor.cancel_perp K00 K01 K10 K11 P1 P2 hu hv
    have D0a : Complex.normSq (c y0) + Complex.normSq (c y7)
        = Complex.normSq (d z3) + Complex.normSq (d z6) + Complex.normSq (d z5) + Complex.normSq (d z4) + Complex.normSq (d z2) + Complex.normSq (d z1) := by linarith
    have D1a : Complex.normSq (c y8) + Complex.normSq (c y15)
        = Complex.normSq (d z11) + Complex.normSq (d z14) + Complex.normSq (d z13) + Complex.normSq (d z12) + Complex.normSq (d z10) + Complex.normSq (d z9) := by linarith
    have Doffa : star (c y8) * c y0 + star (c y15) * c y7
        = star (d z11) * d z3 + star (d z14) * d z6 + star (d z13) * d z5 + star (d z12) * d z4 + star (d z10) * d z2 + star (d z9) * d z1 := by
      linear_combination Doff
    have hz := SixQubit.Spinor.edge_zero D0a D1a Doffa hBu hBv
    linarith

end

end SixQubit.Orbit12
