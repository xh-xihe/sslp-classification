import Mathlib

import SS.FullKL
import SixQubit.Common
import SixQubit.Spinor

/-!
# Six-qubit no-go for moment orbit 6

Orbit 6 of `six_qubit_sslp.tex`: q = 3, angle vector
a = (0, 1, 1, 1, 1, 1), residues 0 and 1.

Qubit 1 has angle zero, so the amplitudes group into spinors in `ℂ²`:
an anchor `u`, ten bottom edges `a_ij`, and on the top fiber five
one-element spinors `b_k` and five four-element spinors `c_i`.

The five-dressing character system for the flip `X_k` (its matrix has
determinant -48) kills `u† b_k` for every `k`.  The equality of the two
reduced states on the zero-angle qubit, contracted on both sides with
`u`, then reads

```
‖u‖⁴ + Σ |a_ij† u|² = Σ |c_i† u|² ,
```

and Lagrange`s identity (`SixQubit.Spinor.lagrange`) turns the right
side into `‖u‖² Σ ‖c_i‖² - Σ |det(c_i,u)|²`.  The moment polytope pins
`‖u‖² = 1/3` and `Σ ‖c_i‖² = 1/3`, so the two `1/9`s cancel exactly and
what survives is a vanishing sum of nonnegative reals: every `a_ij` is
orthogonal to `u`.  The four two-by-two entries of the `X_k` row then
collapse to `‖u‖² b_k = 0`, so every `b_k` vanishes -- contradicting the
exact shell mass `Σ ‖b_k‖² = 2/3`.

This replaces the projector-alignment step of the paper: no spans, no
case analysis on which `t_i` are positive, and no division.

Everything computational is decided by the Lean kernel; `native_decide`
is not used.
-/

namespace SixQubit.Orbit6

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

/-! ## The two fibers -/

def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]

def y0 : SS.BitString 6 := bs false false false false false false  -- 000000
def y1 : SS.BitString 6 := bs false false false true  true  true   -- 000111
def y2 : SS.BitString 6 := bs false false true  false true  true   -- 001011
def y3 : SS.BitString 6 := bs false false true  true  false true   -- 001101
def y4 : SS.BitString 6 := bs false false true  true  true  false  -- 001110
def y5 : SS.BitString 6 := bs false true  false false true  true   -- 010011
def y6 : SS.BitString 6 := bs false true  false true  false true   -- 010101
def y7 : SS.BitString 6 := bs false true  false true  true  false  -- 010110
def y8 : SS.BitString 6 := bs false true  true  false false true   -- 011001
def y9 : SS.BitString 6 := bs false true  true  false true  false  -- 011010
def y10 : SS.BitString 6 := bs false true  true  true  false false  -- 011100
def y11 : SS.BitString 6 := bs true  false false false false false  -- 100000
def y12 : SS.BitString 6 := bs true  false false true  true  true   -- 100111
def y13 : SS.BitString 6 := bs true  false true  false true  true   -- 101011
def y14 : SS.BitString 6 := bs true  false true  true  false true   -- 101101
def y15 : SS.BitString 6 := bs true  false true  true  true  false  -- 101110
def y16 : SS.BitString 6 := bs true  true  false false true  true   -- 110011
def y17 : SS.BitString 6 := bs true  true  false true  false true   -- 110101
def y18 : SS.BitString 6 := bs true  true  false true  true  false  -- 110110
def y19 : SS.BitString 6 := bs true  true  true  false false true   -- 111001
def y20 : SS.BitString 6 := bs true  true  true  false true  false  -- 111010
def y21 : SS.BitString 6 := bs true  true  true  true  false false  -- 111100

def z0 : SS.BitString 6 := bs false false false false false true   -- 000001
def z1 : SS.BitString 6 := bs false false false false true  false  -- 000010
def z2 : SS.BitString 6 := bs false false false true  false false  -- 000100
def z3 : SS.BitString 6 := bs false false true  false false false  -- 001000
def z4 : SS.BitString 6 := bs false false true  true  true  true   -- 001111
def z5 : SS.BitString 6 := bs false true  false false false false  -- 010000
def z6 : SS.BitString 6 := bs false true  false true  true  true   -- 010111
def z7 : SS.BitString 6 := bs false true  true  false true  true   -- 011011
def z8 : SS.BitString 6 := bs false true  true  true  false true   -- 011101
def z9 : SS.BitString 6 := bs false true  true  true  true  false  -- 011110
def z10 : SS.BitString 6 := bs true  false false false false true   -- 100001
def z11 : SS.BitString 6 := bs true  false false false true  false  -- 100010
def z12 : SS.BitString 6 := bs true  false false true  false false  -- 100100
def z13 : SS.BitString 6 := bs true  false true  false false false  -- 101000
def z14 : SS.BitString 6 := bs true  false true  true  true  true   -- 101111
def z15 : SS.BitString 6 := bs true  true  false false false false  -- 110000
def z16 : SS.BitString 6 := bs true  true  false true  true  true   -- 110111
def z17 : SS.BitString 6 := bs true  true  true  false true  true   -- 111011
def z18 : SS.BitString 6 := bs true  true  true  true  false true   -- 111101
def z19 : SS.BitString 6 := bs true  true  true  true  true  false  -- 111110

def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21}
def S1 : Finset (SS.BitString 6) := {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19}

def av : Fin 6 -> ZMod 3 := ![0, 1, 1, 1, 1, 1]

theorem S0_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 0) = S0 := by
  decide

theorem S1_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 1) = S1 := by
  decide

/-! ## Masks and dressings -/

def ef0 : SS.BitString 6 := bs false true  false false false false  -- 010000
def ef1 : SS.BitString 6 := bs true  true  false false false false  -- 110000
def ef2 : SS.BitString 6 := bs false false true  false false false  -- 001000
def ef3 : SS.BitString 6 := bs true  false true  false false false  -- 101000
def ef4 : SS.BitString 6 := bs false false false true  false false  -- 000100
def ef5 : SS.BitString 6 := bs true  false false true  false false  -- 100100
def ef6 : SS.BitString 6 := bs false false false false true  false  -- 000010
def ef7 : SS.BitString 6 := bs true  false false false true  false  -- 100010
def ef8 : SS.BitString 6 := bs false false false false false true   -- 000001
def ef9 : SS.BitString 6 := bs true  false false false false true   -- 100001
def efA : SS.BitString 6 := bs true  false false false false false  -- 100000
def w0 : SS.BitString 6 := bs false false false false false false  -- 000000
def w1 : SS.BitString 6 := bs false false false false false true   -- 000001
def w2 : SS.BitString 6 := bs false false false false true  false  -- 000010
def w3 : SS.BitString 6 := bs false false false true  false false  -- 000100
def w4 : SS.BitString 6 := bs false false true  false false false  -- 001000
def w5 : SS.BitString 6 := bs false true  false false false false  -- 010000
def w6 : SS.BitString 6 := bs true  false false false false false  -- 100000

/-! ## The off-diagonal layer -/

def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),
      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

theorem incidence_ef0 :
    S1.filter (fun y => SS.bxor y ef0 ∈ S0) = {z5, z6, z7, z8, z9, z15, z16, z17, z18, z19} := by decide
theorem flip_ef0_5 : SS.bxor z5 ef0 = y0 := by decide
theorem flip_ef0_6 : SS.bxor z6 ef0 = y1 := by decide
theorem flip_ef0_7 : SS.bxor z7 ef0 = y2 := by decide
theorem flip_ef0_8 : SS.bxor z8 ef0 = y3 := by decide
theorem flip_ef0_9 : SS.bxor z9 ef0 = y4 := by decide
theorem flip_ef0_15 : SS.bxor z15 ef0 = y11 := by decide
theorem flip_ef0_16 : SS.bxor z16 ef0 = y12 := by decide
theorem flip_ef0_17 : SS.bxor z17 ef0 = y13 := by decide
theorem flip_ef0_18 : SS.bxor z18 ef0 = y14 := by decide
theorem flip_ef0_19 : SS.bxor z19 ef0 = y15 := by decide
theorem sg_ef0_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg_ef0_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg_ef0_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg_ef0_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_ef0_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg_ef0_w0_15 : SS.bdot w0 z15 = false := by decide
theorem sg_ef0_w0_16 : SS.bdot w0 z16 = false := by decide
theorem sg_ef0_w0_17 : SS.bdot w0 z17 = false := by decide
theorem sg_ef0_w0_18 : SS.bdot w0 z18 = false := by decide
theorem sg_ef0_w0_19 : SS.bdot w0 z19 = false := by decide
theorem ex_ef0_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w0 = star (c y0) * d z5 + star (c y1) * d z6 + star (c y2) * d z7 + star (c y3) * d z8 + star (c y4) * d z9 + star (c y11) * d z15 + star (c y12) * d z16 + star (c y13) * d z17 + star (c y14) * d z18 + star (c y15) * d z19 := by
  unfold offSum
  rw [incidence_ef0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef0_5, flip_ef0_6, flip_ef0_7, flip_ef0_8, flip_ef0_9, flip_ef0_15, flip_ef0_16, flip_ef0_17, flip_ef0_18, flip_ef0_19]
  simp only [sg_ef0_w0_5, sg_ef0_w0_6, sg_ef0_w0_7, sg_ef0_w0_8, sg_ef0_w0_9, sg_ef0_w0_15, sg_ef0_w0_16, sg_ef0_w0_17, sg_ef0_w0_18, sg_ef0_w0_19, SixQubit.signMul_false]
  try ring
theorem sg_ef0_w1_5 : SS.bdot w1 z5 = false := by decide
theorem sg_ef0_w1_6 : SS.bdot w1 z6 = true := by decide
theorem sg_ef0_w1_7 : SS.bdot w1 z7 = true := by decide
theorem sg_ef0_w1_8 : SS.bdot w1 z8 = true := by decide
theorem sg_ef0_w1_9 : SS.bdot w1 z9 = false := by decide
theorem sg_ef0_w1_15 : SS.bdot w1 z15 = false := by decide
theorem sg_ef0_w1_16 : SS.bdot w1 z16 = true := by decide
theorem sg_ef0_w1_17 : SS.bdot w1 z17 = true := by decide
theorem sg_ef0_w1_18 : SS.bdot w1 z18 = true := by decide
theorem sg_ef0_w1_19 : SS.bdot w1 z19 = false := by decide
theorem ex_ef0_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w1 = star (c y0) * d z5 - star (c y1) * d z6 - star (c y2) * d z7 - star (c y3) * d z8 + star (c y4) * d z9 + star (c y11) * d z15 - star (c y12) * d z16 - star (c y13) * d z17 - star (c y14) * d z18 + star (c y15) * d z19 := by
  unfold offSum
  rw [incidence_ef0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef0_5, flip_ef0_6, flip_ef0_7, flip_ef0_8, flip_ef0_9, flip_ef0_15, flip_ef0_16, flip_ef0_17, flip_ef0_18, flip_ef0_19]
  simp only [sg_ef0_w1_5, sg_ef0_w1_6, sg_ef0_w1_7, sg_ef0_w1_8, sg_ef0_w1_9, sg_ef0_w1_15, sg_ef0_w1_16, sg_ef0_w1_17, sg_ef0_w1_18, sg_ef0_w1_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef0_w2_5 : SS.bdot w2 z5 = false := by decide
theorem sg_ef0_w2_6 : SS.bdot w2 z6 = true := by decide
theorem sg_ef0_w2_7 : SS.bdot w2 z7 = true := by decide
theorem sg_ef0_w2_8 : SS.bdot w2 z8 = false := by decide
theorem sg_ef0_w2_9 : SS.bdot w2 z9 = true := by decide
theorem sg_ef0_w2_15 : SS.bdot w2 z15 = false := by decide
theorem sg_ef0_w2_16 : SS.bdot w2 z16 = true := by decide
theorem sg_ef0_w2_17 : SS.bdot w2 z17 = true := by decide
theorem sg_ef0_w2_18 : SS.bdot w2 z18 = false := by decide
theorem sg_ef0_w2_19 : SS.bdot w2 z19 = true := by decide
theorem ex_ef0_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w2 = star (c y0) * d z5 - star (c y1) * d z6 - star (c y2) * d z7 + star (c y3) * d z8 - star (c y4) * d z9 + star (c y11) * d z15 - star (c y12) * d z16 - star (c y13) * d z17 + star (c y14) * d z18 - star (c y15) * d z19 := by
  unfold offSum
  rw [incidence_ef0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef0_5, flip_ef0_6, flip_ef0_7, flip_ef0_8, flip_ef0_9, flip_ef0_15, flip_ef0_16, flip_ef0_17, flip_ef0_18, flip_ef0_19]
  simp only [sg_ef0_w2_5, sg_ef0_w2_6, sg_ef0_w2_7, sg_ef0_w2_8, sg_ef0_w2_9, sg_ef0_w2_15, sg_ef0_w2_16, sg_ef0_w2_17, sg_ef0_w2_18, sg_ef0_w2_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef0_w3_5 : SS.bdot w3 z5 = false := by decide
theorem sg_ef0_w3_6 : SS.bdot w3 z6 = true := by decide
theorem sg_ef0_w3_7 : SS.bdot w3 z7 = false := by decide
theorem sg_ef0_w3_8 : SS.bdot w3 z8 = true := by decide
theorem sg_ef0_w3_9 : SS.bdot w3 z9 = true := by decide
theorem sg_ef0_w3_15 : SS.bdot w3 z15 = false := by decide
theorem sg_ef0_w3_16 : SS.bdot w3 z16 = true := by decide
theorem sg_ef0_w3_17 : SS.bdot w3 z17 = false := by decide
theorem sg_ef0_w3_18 : SS.bdot w3 z18 = true := by decide
theorem sg_ef0_w3_19 : SS.bdot w3 z19 = true := by decide
theorem ex_ef0_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w3 = star (c y0) * d z5 - star (c y1) * d z6 + star (c y2) * d z7 - star (c y3) * d z8 - star (c y4) * d z9 + star (c y11) * d z15 - star (c y12) * d z16 + star (c y13) * d z17 - star (c y14) * d z18 - star (c y15) * d z19 := by
  unfold offSum
  rw [incidence_ef0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef0_5, flip_ef0_6, flip_ef0_7, flip_ef0_8, flip_ef0_9, flip_ef0_15, flip_ef0_16, flip_ef0_17, flip_ef0_18, flip_ef0_19]
  simp only [sg_ef0_w3_5, sg_ef0_w3_6, sg_ef0_w3_7, sg_ef0_w3_8, sg_ef0_w3_9, sg_ef0_w3_15, sg_ef0_w3_16, sg_ef0_w3_17, sg_ef0_w3_18, sg_ef0_w3_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef0_w4_5 : SS.bdot w4 z5 = false := by decide
theorem sg_ef0_w4_6 : SS.bdot w4 z6 = false := by decide
theorem sg_ef0_w4_7 : SS.bdot w4 z7 = true := by decide
theorem sg_ef0_w4_8 : SS.bdot w4 z8 = true := by decide
theorem sg_ef0_w4_9 : SS.bdot w4 z9 = true := by decide
theorem sg_ef0_w4_15 : SS.bdot w4 z15 = false := by decide
theorem sg_ef0_w4_16 : SS.bdot w4 z16 = false := by decide
theorem sg_ef0_w4_17 : SS.bdot w4 z17 = true := by decide
theorem sg_ef0_w4_18 : SS.bdot w4 z18 = true := by decide
theorem sg_ef0_w4_19 : SS.bdot w4 z19 = true := by decide
theorem ex_ef0_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w4 = star (c y0) * d z5 + star (c y1) * d z6 - star (c y2) * d z7 - star (c y3) * d z8 - star (c y4) * d z9 + star (c y11) * d z15 + star (c y12) * d z16 - star (c y13) * d z17 - star (c y14) * d z18 - star (c y15) * d z19 := by
  unfold offSum
  rw [incidence_ef0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef0_5, flip_ef0_6, flip_ef0_7, flip_ef0_8, flip_ef0_9, flip_ef0_15, flip_ef0_16, flip_ef0_17, flip_ef0_18, flip_ef0_19]
  simp only [sg_ef0_w4_5, sg_ef0_w4_6, sg_ef0_w4_7, sg_ef0_w4_8, sg_ef0_w4_9, sg_ef0_w4_15, sg_ef0_w4_16, sg_ef0_w4_17, sg_ef0_w4_18, sg_ef0_w4_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef0_w6_5 : SS.bdot w6 z5 = false := by decide
theorem sg_ef0_w6_6 : SS.bdot w6 z6 = false := by decide
theorem sg_ef0_w6_7 : SS.bdot w6 z7 = false := by decide
theorem sg_ef0_w6_8 : SS.bdot w6 z8 = false := by decide
theorem sg_ef0_w6_9 : SS.bdot w6 z9 = false := by decide
theorem sg_ef0_w6_15 : SS.bdot w6 z15 = true := by decide
theorem sg_ef0_w6_16 : SS.bdot w6 z16 = true := by decide
theorem sg_ef0_w6_17 : SS.bdot w6 z17 = true := by decide
theorem sg_ef0_w6_18 : SS.bdot w6 z18 = true := by decide
theorem sg_ef0_w6_19 : SS.bdot w6 z19 = true := by decide
theorem ex_ef0_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w6 = star (c y0) * d z5 + star (c y1) * d z6 + star (c y2) * d z7 + star (c y3) * d z8 + star (c y4) * d z9 - star (c y11) * d z15 - star (c y12) * d z16 - star (c y13) * d z17 - star (c y14) * d z18 - star (c y15) * d z19 := by
  unfold offSum
  rw [incidence_ef0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef0_5, flip_ef0_6, flip_ef0_7, flip_ef0_8, flip_ef0_9, flip_ef0_15, flip_ef0_16, flip_ef0_17, flip_ef0_18, flip_ef0_19]
  simp only [sg_ef0_w6_5, sg_ef0_w6_6, sg_ef0_w6_7, sg_ef0_w6_8, sg_ef0_w6_9, sg_ef0_w6_15, sg_ef0_w6_16, sg_ef0_w6_17, sg_ef0_w6_18, sg_ef0_w6_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem incidence_ef1 :
    S1.filter (fun y => SS.bxor y ef1 ∈ S0) = {z5, z6, z7, z8, z9, z15, z16, z17, z18, z19} := by decide
theorem flip_ef1_5 : SS.bxor z5 ef1 = y11 := by decide
theorem flip_ef1_6 : SS.bxor z6 ef1 = y12 := by decide
theorem flip_ef1_7 : SS.bxor z7 ef1 = y13 := by decide
theorem flip_ef1_8 : SS.bxor z8 ef1 = y14 := by decide
theorem flip_ef1_9 : SS.bxor z9 ef1 = y15 := by decide
theorem flip_ef1_15 : SS.bxor z15 ef1 = y0 := by decide
theorem flip_ef1_16 : SS.bxor z16 ef1 = y1 := by decide
theorem flip_ef1_17 : SS.bxor z17 ef1 = y2 := by decide
theorem flip_ef1_18 : SS.bxor z18 ef1 = y3 := by decide
theorem flip_ef1_19 : SS.bxor z19 ef1 = y4 := by decide
theorem sg_ef1_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg_ef1_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg_ef1_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg_ef1_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_ef1_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg_ef1_w0_15 : SS.bdot w0 z15 = false := by decide
theorem sg_ef1_w0_16 : SS.bdot w0 z16 = false := by decide
theorem sg_ef1_w0_17 : SS.bdot w0 z17 = false := by decide
theorem sg_ef1_w0_18 : SS.bdot w0 z18 = false := by decide
theorem sg_ef1_w0_19 : SS.bdot w0 z19 = false := by decide
theorem ex_ef1_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w0 = star (c y11) * d z5 + star (c y12) * d z6 + star (c y13) * d z7 + star (c y14) * d z8 + star (c y15) * d z9 + star (c y0) * d z15 + star (c y1) * d z16 + star (c y2) * d z17 + star (c y3) * d z18 + star (c y4) * d z19 := by
  unfold offSum
  rw [incidence_ef1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef1_5, flip_ef1_6, flip_ef1_7, flip_ef1_8, flip_ef1_9, flip_ef1_15, flip_ef1_16, flip_ef1_17, flip_ef1_18, flip_ef1_19]
  simp only [sg_ef1_w0_5, sg_ef1_w0_6, sg_ef1_w0_7, sg_ef1_w0_8, sg_ef1_w0_9, sg_ef1_w0_15, sg_ef1_w0_16, sg_ef1_w0_17, sg_ef1_w0_18, sg_ef1_w0_19, SixQubit.signMul_false]
  try ring
theorem sg_ef1_w6_5 : SS.bdot w6 z5 = false := by decide
theorem sg_ef1_w6_6 : SS.bdot w6 z6 = false := by decide
theorem sg_ef1_w6_7 : SS.bdot w6 z7 = false := by decide
theorem sg_ef1_w6_8 : SS.bdot w6 z8 = false := by decide
theorem sg_ef1_w6_9 : SS.bdot w6 z9 = false := by decide
theorem sg_ef1_w6_15 : SS.bdot w6 z15 = true := by decide
theorem sg_ef1_w6_16 : SS.bdot w6 z16 = true := by decide
theorem sg_ef1_w6_17 : SS.bdot w6 z17 = true := by decide
theorem sg_ef1_w6_18 : SS.bdot w6 z18 = true := by decide
theorem sg_ef1_w6_19 : SS.bdot w6 z19 = true := by decide
theorem ex_ef1_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w6 = star (c y11) * d z5 + star (c y12) * d z6 + star (c y13) * d z7 + star (c y14) * d z8 + star (c y15) * d z9 - star (c y0) * d z15 - star (c y1) * d z16 - star (c y2) * d z17 - star (c y3) * d z18 - star (c y4) * d z19 := by
  unfold offSum
  rw [incidence_ef1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef1_5, flip_ef1_6, flip_ef1_7, flip_ef1_8, flip_ef1_9, flip_ef1_15, flip_ef1_16, flip_ef1_17, flip_ef1_18, flip_ef1_19]
  simp only [sg_ef1_w6_5, sg_ef1_w6_6, sg_ef1_w6_7, sg_ef1_w6_8, sg_ef1_w6_9, sg_ef1_w6_15, sg_ef1_w6_16, sg_ef1_w6_17, sg_ef1_w6_18, sg_ef1_w6_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem incidence_ef2 :
    S1.filter (fun y => SS.bxor y ef2 ∈ S0) = {z3, z4, z7, z8, z9, z13, z14, z17, z18, z19} := by decide
theorem flip_ef2_3 : SS.bxor z3 ef2 = y0 := by decide
theorem flip_ef2_4 : SS.bxor z4 ef2 = y1 := by decide
theorem flip_ef2_7 : SS.bxor z7 ef2 = y5 := by decide
theorem flip_ef2_8 : SS.bxor z8 ef2 = y6 := by decide
theorem flip_ef2_9 : SS.bxor z9 ef2 = y7 := by decide
theorem flip_ef2_13 : SS.bxor z13 ef2 = y11 := by decide
theorem flip_ef2_14 : SS.bxor z14 ef2 = y12 := by decide
theorem flip_ef2_17 : SS.bxor z17 ef2 = y16 := by decide
theorem flip_ef2_18 : SS.bxor z18 ef2 = y17 := by decide
theorem flip_ef2_19 : SS.bxor z19 ef2 = y18 := by decide
theorem sg_ef2_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg_ef2_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg_ef2_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg_ef2_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_ef2_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg_ef2_w0_13 : SS.bdot w0 z13 = false := by decide
theorem sg_ef2_w0_14 : SS.bdot w0 z14 = false := by decide
theorem sg_ef2_w0_17 : SS.bdot w0 z17 = false := by decide
theorem sg_ef2_w0_18 : SS.bdot w0 z18 = false := by decide
theorem sg_ef2_w0_19 : SS.bdot w0 z19 = false := by decide
theorem ex_ef2_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w0 = star (c y0) * d z3 + star (c y1) * d z4 + star (c y5) * d z7 + star (c y6) * d z8 + star (c y7) * d z9 + star (c y11) * d z13 + star (c y12) * d z14 + star (c y16) * d z17 + star (c y17) * d z18 + star (c y18) * d z19 := by
  unfold offSum
  rw [incidence_ef2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef2_3, flip_ef2_4, flip_ef2_7, flip_ef2_8, flip_ef2_9, flip_ef2_13, flip_ef2_14, flip_ef2_17, flip_ef2_18, flip_ef2_19]
  simp only [sg_ef2_w0_3, sg_ef2_w0_4, sg_ef2_w0_7, sg_ef2_w0_8, sg_ef2_w0_9, sg_ef2_w0_13, sg_ef2_w0_14, sg_ef2_w0_17, sg_ef2_w0_18, sg_ef2_w0_19, SixQubit.signMul_false]
  try ring
theorem sg_ef2_w1_3 : SS.bdot w1 z3 = false := by decide
theorem sg_ef2_w1_4 : SS.bdot w1 z4 = true := by decide
theorem sg_ef2_w1_7 : SS.bdot w1 z7 = true := by decide
theorem sg_ef2_w1_8 : SS.bdot w1 z8 = true := by decide
theorem sg_ef2_w1_9 : SS.bdot w1 z9 = false := by decide
theorem sg_ef2_w1_13 : SS.bdot w1 z13 = false := by decide
theorem sg_ef2_w1_14 : SS.bdot w1 z14 = true := by decide
theorem sg_ef2_w1_17 : SS.bdot w1 z17 = true := by decide
theorem sg_ef2_w1_18 : SS.bdot w1 z18 = true := by decide
theorem sg_ef2_w1_19 : SS.bdot w1 z19 = false := by decide
theorem ex_ef2_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w1 = star (c y0) * d z3 - star (c y1) * d z4 - star (c y5) * d z7 - star (c y6) * d z8 + star (c y7) * d z9 + star (c y11) * d z13 - star (c y12) * d z14 - star (c y16) * d z17 - star (c y17) * d z18 + star (c y18) * d z19 := by
  unfold offSum
  rw [incidence_ef2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef2_3, flip_ef2_4, flip_ef2_7, flip_ef2_8, flip_ef2_9, flip_ef2_13, flip_ef2_14, flip_ef2_17, flip_ef2_18, flip_ef2_19]
  simp only [sg_ef2_w1_3, sg_ef2_w1_4, sg_ef2_w1_7, sg_ef2_w1_8, sg_ef2_w1_9, sg_ef2_w1_13, sg_ef2_w1_14, sg_ef2_w1_17, sg_ef2_w1_18, sg_ef2_w1_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef2_w2_3 : SS.bdot w2 z3 = false := by decide
theorem sg_ef2_w2_4 : SS.bdot w2 z4 = true := by decide
theorem sg_ef2_w2_7 : SS.bdot w2 z7 = true := by decide
theorem sg_ef2_w2_8 : SS.bdot w2 z8 = false := by decide
theorem sg_ef2_w2_9 : SS.bdot w2 z9 = true := by decide
theorem sg_ef2_w2_13 : SS.bdot w2 z13 = false := by decide
theorem sg_ef2_w2_14 : SS.bdot w2 z14 = true := by decide
theorem sg_ef2_w2_17 : SS.bdot w2 z17 = true := by decide
theorem sg_ef2_w2_18 : SS.bdot w2 z18 = false := by decide
theorem sg_ef2_w2_19 : SS.bdot w2 z19 = true := by decide
theorem ex_ef2_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w2 = star (c y0) * d z3 - star (c y1) * d z4 - star (c y5) * d z7 + star (c y6) * d z8 - star (c y7) * d z9 + star (c y11) * d z13 - star (c y12) * d z14 - star (c y16) * d z17 + star (c y17) * d z18 - star (c y18) * d z19 := by
  unfold offSum
  rw [incidence_ef2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef2_3, flip_ef2_4, flip_ef2_7, flip_ef2_8, flip_ef2_9, flip_ef2_13, flip_ef2_14, flip_ef2_17, flip_ef2_18, flip_ef2_19]
  simp only [sg_ef2_w2_3, sg_ef2_w2_4, sg_ef2_w2_7, sg_ef2_w2_8, sg_ef2_w2_9, sg_ef2_w2_13, sg_ef2_w2_14, sg_ef2_w2_17, sg_ef2_w2_18, sg_ef2_w2_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef2_w3_3 : SS.bdot w3 z3 = false := by decide
theorem sg_ef2_w3_4 : SS.bdot w3 z4 = true := by decide
theorem sg_ef2_w3_7 : SS.bdot w3 z7 = false := by decide
theorem sg_ef2_w3_8 : SS.bdot w3 z8 = true := by decide
theorem sg_ef2_w3_9 : SS.bdot w3 z9 = true := by decide
theorem sg_ef2_w3_13 : SS.bdot w3 z13 = false := by decide
theorem sg_ef2_w3_14 : SS.bdot w3 z14 = true := by decide
theorem sg_ef2_w3_17 : SS.bdot w3 z17 = false := by decide
theorem sg_ef2_w3_18 : SS.bdot w3 z18 = true := by decide
theorem sg_ef2_w3_19 : SS.bdot w3 z19 = true := by decide
theorem ex_ef2_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w3 = star (c y0) * d z3 - star (c y1) * d z4 + star (c y5) * d z7 - star (c y6) * d z8 - star (c y7) * d z9 + star (c y11) * d z13 - star (c y12) * d z14 + star (c y16) * d z17 - star (c y17) * d z18 - star (c y18) * d z19 := by
  unfold offSum
  rw [incidence_ef2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef2_3, flip_ef2_4, flip_ef2_7, flip_ef2_8, flip_ef2_9, flip_ef2_13, flip_ef2_14, flip_ef2_17, flip_ef2_18, flip_ef2_19]
  simp only [sg_ef2_w3_3, sg_ef2_w3_4, sg_ef2_w3_7, sg_ef2_w3_8, sg_ef2_w3_9, sg_ef2_w3_13, sg_ef2_w3_14, sg_ef2_w3_17, sg_ef2_w3_18, sg_ef2_w3_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef2_w5_3 : SS.bdot w5 z3 = false := by decide
theorem sg_ef2_w5_4 : SS.bdot w5 z4 = false := by decide
theorem sg_ef2_w5_7 : SS.bdot w5 z7 = true := by decide
theorem sg_ef2_w5_8 : SS.bdot w5 z8 = true := by decide
theorem sg_ef2_w5_9 : SS.bdot w5 z9 = true := by decide
theorem sg_ef2_w5_13 : SS.bdot w5 z13 = false := by decide
theorem sg_ef2_w5_14 : SS.bdot w5 z14 = false := by decide
theorem sg_ef2_w5_17 : SS.bdot w5 z17 = true := by decide
theorem sg_ef2_w5_18 : SS.bdot w5 z18 = true := by decide
theorem sg_ef2_w5_19 : SS.bdot w5 z19 = true := by decide
theorem ex_ef2_w5 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w5 = star (c y0) * d z3 + star (c y1) * d z4 - star (c y5) * d z7 - star (c y6) * d z8 - star (c y7) * d z9 + star (c y11) * d z13 + star (c y12) * d z14 - star (c y16) * d z17 - star (c y17) * d z18 - star (c y18) * d z19 := by
  unfold offSum
  rw [incidence_ef2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef2_3, flip_ef2_4, flip_ef2_7, flip_ef2_8, flip_ef2_9, flip_ef2_13, flip_ef2_14, flip_ef2_17, flip_ef2_18, flip_ef2_19]
  simp only [sg_ef2_w5_3, sg_ef2_w5_4, sg_ef2_w5_7, sg_ef2_w5_8, sg_ef2_w5_9, sg_ef2_w5_13, sg_ef2_w5_14, sg_ef2_w5_17, sg_ef2_w5_18, sg_ef2_w5_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef2_w6_3 : SS.bdot w6 z3 = false := by decide
theorem sg_ef2_w6_4 : SS.bdot w6 z4 = false := by decide
theorem sg_ef2_w6_7 : SS.bdot w6 z7 = false := by decide
theorem sg_ef2_w6_8 : SS.bdot w6 z8 = false := by decide
theorem sg_ef2_w6_9 : SS.bdot w6 z9 = false := by decide
theorem sg_ef2_w6_13 : SS.bdot w6 z13 = true := by decide
theorem sg_ef2_w6_14 : SS.bdot w6 z14 = true := by decide
theorem sg_ef2_w6_17 : SS.bdot w6 z17 = true := by decide
theorem sg_ef2_w6_18 : SS.bdot w6 z18 = true := by decide
theorem sg_ef2_w6_19 : SS.bdot w6 z19 = true := by decide
theorem ex_ef2_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w6 = star (c y0) * d z3 + star (c y1) * d z4 + star (c y5) * d z7 + star (c y6) * d z8 + star (c y7) * d z9 - star (c y11) * d z13 - star (c y12) * d z14 - star (c y16) * d z17 - star (c y17) * d z18 - star (c y18) * d z19 := by
  unfold offSum
  rw [incidence_ef2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef2_3, flip_ef2_4, flip_ef2_7, flip_ef2_8, flip_ef2_9, flip_ef2_13, flip_ef2_14, flip_ef2_17, flip_ef2_18, flip_ef2_19]
  simp only [sg_ef2_w6_3, sg_ef2_w6_4, sg_ef2_w6_7, sg_ef2_w6_8, sg_ef2_w6_9, sg_ef2_w6_13, sg_ef2_w6_14, sg_ef2_w6_17, sg_ef2_w6_18, sg_ef2_w6_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem incidence_ef3 :
    S1.filter (fun y => SS.bxor y ef3 ∈ S0) = {z3, z4, z7, z8, z9, z13, z14, z17, z18, z19} := by decide
theorem flip_ef3_3 : SS.bxor z3 ef3 = y11 := by decide
theorem flip_ef3_4 : SS.bxor z4 ef3 = y12 := by decide
theorem flip_ef3_7 : SS.bxor z7 ef3 = y16 := by decide
theorem flip_ef3_8 : SS.bxor z8 ef3 = y17 := by decide
theorem flip_ef3_9 : SS.bxor z9 ef3 = y18 := by decide
theorem flip_ef3_13 : SS.bxor z13 ef3 = y0 := by decide
theorem flip_ef3_14 : SS.bxor z14 ef3 = y1 := by decide
theorem flip_ef3_17 : SS.bxor z17 ef3 = y5 := by decide
theorem flip_ef3_18 : SS.bxor z18 ef3 = y6 := by decide
theorem flip_ef3_19 : SS.bxor z19 ef3 = y7 := by decide
theorem sg_ef3_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg_ef3_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg_ef3_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg_ef3_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_ef3_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg_ef3_w0_13 : SS.bdot w0 z13 = false := by decide
theorem sg_ef3_w0_14 : SS.bdot w0 z14 = false := by decide
theorem sg_ef3_w0_17 : SS.bdot w0 z17 = false := by decide
theorem sg_ef3_w0_18 : SS.bdot w0 z18 = false := by decide
theorem sg_ef3_w0_19 : SS.bdot w0 z19 = false := by decide
theorem ex_ef3_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w0 = star (c y11) * d z3 + star (c y12) * d z4 + star (c y16) * d z7 + star (c y17) * d z8 + star (c y18) * d z9 + star (c y0) * d z13 + star (c y1) * d z14 + star (c y5) * d z17 + star (c y6) * d z18 + star (c y7) * d z19 := by
  unfold offSum
  rw [incidence_ef3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef3_3, flip_ef3_4, flip_ef3_7, flip_ef3_8, flip_ef3_9, flip_ef3_13, flip_ef3_14, flip_ef3_17, flip_ef3_18, flip_ef3_19]
  simp only [sg_ef3_w0_3, sg_ef3_w0_4, sg_ef3_w0_7, sg_ef3_w0_8, sg_ef3_w0_9, sg_ef3_w0_13, sg_ef3_w0_14, sg_ef3_w0_17, sg_ef3_w0_18, sg_ef3_w0_19, SixQubit.signMul_false]
  try ring
theorem sg_ef3_w6_3 : SS.bdot w6 z3 = false := by decide
theorem sg_ef3_w6_4 : SS.bdot w6 z4 = false := by decide
theorem sg_ef3_w6_7 : SS.bdot w6 z7 = false := by decide
theorem sg_ef3_w6_8 : SS.bdot w6 z8 = false := by decide
theorem sg_ef3_w6_9 : SS.bdot w6 z9 = false := by decide
theorem sg_ef3_w6_13 : SS.bdot w6 z13 = true := by decide
theorem sg_ef3_w6_14 : SS.bdot w6 z14 = true := by decide
theorem sg_ef3_w6_17 : SS.bdot w6 z17 = true := by decide
theorem sg_ef3_w6_18 : SS.bdot w6 z18 = true := by decide
theorem sg_ef3_w6_19 : SS.bdot w6 z19 = true := by decide
theorem ex_ef3_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w6 = star (c y11) * d z3 + star (c y12) * d z4 + star (c y16) * d z7 + star (c y17) * d z8 + star (c y18) * d z9 - star (c y0) * d z13 - star (c y1) * d z14 - star (c y5) * d z17 - star (c y6) * d z18 - star (c y7) * d z19 := by
  unfold offSum
  rw [incidence_ef3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef3_3, flip_ef3_4, flip_ef3_7, flip_ef3_8, flip_ef3_9, flip_ef3_13, flip_ef3_14, flip_ef3_17, flip_ef3_18, flip_ef3_19]
  simp only [sg_ef3_w6_3, sg_ef3_w6_4, sg_ef3_w6_7, sg_ef3_w6_8, sg_ef3_w6_9, sg_ef3_w6_13, sg_ef3_w6_14, sg_ef3_w6_17, sg_ef3_w6_18, sg_ef3_w6_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem incidence_ef4 :
    S1.filter (fun y => SS.bxor y ef4 ∈ S0) = {z2, z4, z6, z8, z9, z12, z14, z16, z18, z19} := by decide
theorem flip_ef4_2 : SS.bxor z2 ef4 = y0 := by decide
theorem flip_ef4_4 : SS.bxor z4 ef4 = y2 := by decide
theorem flip_ef4_6 : SS.bxor z6 ef4 = y5 := by decide
theorem flip_ef4_8 : SS.bxor z8 ef4 = y8 := by decide
theorem flip_ef4_9 : SS.bxor z9 ef4 = y9 := by decide
theorem flip_ef4_12 : SS.bxor z12 ef4 = y11 := by decide
theorem flip_ef4_14 : SS.bxor z14 ef4 = y13 := by decide
theorem flip_ef4_16 : SS.bxor z16 ef4 = y16 := by decide
theorem flip_ef4_18 : SS.bxor z18 ef4 = y19 := by decide
theorem flip_ef4_19 : SS.bxor z19 ef4 = y20 := by decide
theorem sg_ef4_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg_ef4_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg_ef4_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg_ef4_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_ef4_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg_ef4_w0_12 : SS.bdot w0 z12 = false := by decide
theorem sg_ef4_w0_14 : SS.bdot w0 z14 = false := by decide
theorem sg_ef4_w0_16 : SS.bdot w0 z16 = false := by decide
theorem sg_ef4_w0_18 : SS.bdot w0 z18 = false := by decide
theorem sg_ef4_w0_19 : SS.bdot w0 z19 = false := by decide
theorem ex_ef4_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w0 = star (c y0) * d z2 + star (c y2) * d z4 + star (c y5) * d z6 + star (c y8) * d z8 + star (c y9) * d z9 + star (c y11) * d z12 + star (c y13) * d z14 + star (c y16) * d z16 + star (c y19) * d z18 + star (c y20) * d z19 := by
  unfold offSum
  rw [incidence_ef4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef4_2, flip_ef4_4, flip_ef4_6, flip_ef4_8, flip_ef4_9, flip_ef4_12, flip_ef4_14, flip_ef4_16, flip_ef4_18, flip_ef4_19]
  simp only [sg_ef4_w0_2, sg_ef4_w0_4, sg_ef4_w0_6, sg_ef4_w0_8, sg_ef4_w0_9, sg_ef4_w0_12, sg_ef4_w0_14, sg_ef4_w0_16, sg_ef4_w0_18, sg_ef4_w0_19, SixQubit.signMul_false]
  try ring
theorem sg_ef4_w1_2 : SS.bdot w1 z2 = false := by decide
theorem sg_ef4_w1_4 : SS.bdot w1 z4 = true := by decide
theorem sg_ef4_w1_6 : SS.bdot w1 z6 = true := by decide
theorem sg_ef4_w1_8 : SS.bdot w1 z8 = true := by decide
theorem sg_ef4_w1_9 : SS.bdot w1 z9 = false := by decide
theorem sg_ef4_w1_12 : SS.bdot w1 z12 = false := by decide
theorem sg_ef4_w1_14 : SS.bdot w1 z14 = true := by decide
theorem sg_ef4_w1_16 : SS.bdot w1 z16 = true := by decide
theorem sg_ef4_w1_18 : SS.bdot w1 z18 = true := by decide
theorem sg_ef4_w1_19 : SS.bdot w1 z19 = false := by decide
theorem ex_ef4_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w1 = star (c y0) * d z2 - star (c y2) * d z4 - star (c y5) * d z6 - star (c y8) * d z8 + star (c y9) * d z9 + star (c y11) * d z12 - star (c y13) * d z14 - star (c y16) * d z16 - star (c y19) * d z18 + star (c y20) * d z19 := by
  unfold offSum
  rw [incidence_ef4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef4_2, flip_ef4_4, flip_ef4_6, flip_ef4_8, flip_ef4_9, flip_ef4_12, flip_ef4_14, flip_ef4_16, flip_ef4_18, flip_ef4_19]
  simp only [sg_ef4_w1_2, sg_ef4_w1_4, sg_ef4_w1_6, sg_ef4_w1_8, sg_ef4_w1_9, sg_ef4_w1_12, sg_ef4_w1_14, sg_ef4_w1_16, sg_ef4_w1_18, sg_ef4_w1_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef4_w2_2 : SS.bdot w2 z2 = false := by decide
theorem sg_ef4_w2_4 : SS.bdot w2 z4 = true := by decide
theorem sg_ef4_w2_6 : SS.bdot w2 z6 = true := by decide
theorem sg_ef4_w2_8 : SS.bdot w2 z8 = false := by decide
theorem sg_ef4_w2_9 : SS.bdot w2 z9 = true := by decide
theorem sg_ef4_w2_12 : SS.bdot w2 z12 = false := by decide
theorem sg_ef4_w2_14 : SS.bdot w2 z14 = true := by decide
theorem sg_ef4_w2_16 : SS.bdot w2 z16 = true := by decide
theorem sg_ef4_w2_18 : SS.bdot w2 z18 = false := by decide
theorem sg_ef4_w2_19 : SS.bdot w2 z19 = true := by decide
theorem ex_ef4_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w2 = star (c y0) * d z2 - star (c y2) * d z4 - star (c y5) * d z6 + star (c y8) * d z8 - star (c y9) * d z9 + star (c y11) * d z12 - star (c y13) * d z14 - star (c y16) * d z16 + star (c y19) * d z18 - star (c y20) * d z19 := by
  unfold offSum
  rw [incidence_ef4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef4_2, flip_ef4_4, flip_ef4_6, flip_ef4_8, flip_ef4_9, flip_ef4_12, flip_ef4_14, flip_ef4_16, flip_ef4_18, flip_ef4_19]
  simp only [sg_ef4_w2_2, sg_ef4_w2_4, sg_ef4_w2_6, sg_ef4_w2_8, sg_ef4_w2_9, sg_ef4_w2_12, sg_ef4_w2_14, sg_ef4_w2_16, sg_ef4_w2_18, sg_ef4_w2_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef4_w4_2 : SS.bdot w4 z2 = false := by decide
theorem sg_ef4_w4_4 : SS.bdot w4 z4 = true := by decide
theorem sg_ef4_w4_6 : SS.bdot w4 z6 = false := by decide
theorem sg_ef4_w4_8 : SS.bdot w4 z8 = true := by decide
theorem sg_ef4_w4_9 : SS.bdot w4 z9 = true := by decide
theorem sg_ef4_w4_12 : SS.bdot w4 z12 = false := by decide
theorem sg_ef4_w4_14 : SS.bdot w4 z14 = true := by decide
theorem sg_ef4_w4_16 : SS.bdot w4 z16 = false := by decide
theorem sg_ef4_w4_18 : SS.bdot w4 z18 = true := by decide
theorem sg_ef4_w4_19 : SS.bdot w4 z19 = true := by decide
theorem ex_ef4_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w4 = star (c y0) * d z2 - star (c y2) * d z4 + star (c y5) * d z6 - star (c y8) * d z8 - star (c y9) * d z9 + star (c y11) * d z12 - star (c y13) * d z14 + star (c y16) * d z16 - star (c y19) * d z18 - star (c y20) * d z19 := by
  unfold offSum
  rw [incidence_ef4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef4_2, flip_ef4_4, flip_ef4_6, flip_ef4_8, flip_ef4_9, flip_ef4_12, flip_ef4_14, flip_ef4_16, flip_ef4_18, flip_ef4_19]
  simp only [sg_ef4_w4_2, sg_ef4_w4_4, sg_ef4_w4_6, sg_ef4_w4_8, sg_ef4_w4_9, sg_ef4_w4_12, sg_ef4_w4_14, sg_ef4_w4_16, sg_ef4_w4_18, sg_ef4_w4_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef4_w5_2 : SS.bdot w5 z2 = false := by decide
theorem sg_ef4_w5_4 : SS.bdot w5 z4 = false := by decide
theorem sg_ef4_w5_6 : SS.bdot w5 z6 = true := by decide
theorem sg_ef4_w5_8 : SS.bdot w5 z8 = true := by decide
theorem sg_ef4_w5_9 : SS.bdot w5 z9 = true := by decide
theorem sg_ef4_w5_12 : SS.bdot w5 z12 = false := by decide
theorem sg_ef4_w5_14 : SS.bdot w5 z14 = false := by decide
theorem sg_ef4_w5_16 : SS.bdot w5 z16 = true := by decide
theorem sg_ef4_w5_18 : SS.bdot w5 z18 = true := by decide
theorem sg_ef4_w5_19 : SS.bdot w5 z19 = true := by decide
theorem ex_ef4_w5 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w5 = star (c y0) * d z2 + star (c y2) * d z4 - star (c y5) * d z6 - star (c y8) * d z8 - star (c y9) * d z9 + star (c y11) * d z12 + star (c y13) * d z14 - star (c y16) * d z16 - star (c y19) * d z18 - star (c y20) * d z19 := by
  unfold offSum
  rw [incidence_ef4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef4_2, flip_ef4_4, flip_ef4_6, flip_ef4_8, flip_ef4_9, flip_ef4_12, flip_ef4_14, flip_ef4_16, flip_ef4_18, flip_ef4_19]
  simp only [sg_ef4_w5_2, sg_ef4_w5_4, sg_ef4_w5_6, sg_ef4_w5_8, sg_ef4_w5_9, sg_ef4_w5_12, sg_ef4_w5_14, sg_ef4_w5_16, sg_ef4_w5_18, sg_ef4_w5_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef4_w6_2 : SS.bdot w6 z2 = false := by decide
theorem sg_ef4_w6_4 : SS.bdot w6 z4 = false := by decide
theorem sg_ef4_w6_6 : SS.bdot w6 z6 = false := by decide
theorem sg_ef4_w6_8 : SS.bdot w6 z8 = false := by decide
theorem sg_ef4_w6_9 : SS.bdot w6 z9 = false := by decide
theorem sg_ef4_w6_12 : SS.bdot w6 z12 = true := by decide
theorem sg_ef4_w6_14 : SS.bdot w6 z14 = true := by decide
theorem sg_ef4_w6_16 : SS.bdot w6 z16 = true := by decide
theorem sg_ef4_w6_18 : SS.bdot w6 z18 = true := by decide
theorem sg_ef4_w6_19 : SS.bdot w6 z19 = true := by decide
theorem ex_ef4_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w6 = star (c y0) * d z2 + star (c y2) * d z4 + star (c y5) * d z6 + star (c y8) * d z8 + star (c y9) * d z9 - star (c y11) * d z12 - star (c y13) * d z14 - star (c y16) * d z16 - star (c y19) * d z18 - star (c y20) * d z19 := by
  unfold offSum
  rw [incidence_ef4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef4_2, flip_ef4_4, flip_ef4_6, flip_ef4_8, flip_ef4_9, flip_ef4_12, flip_ef4_14, flip_ef4_16, flip_ef4_18, flip_ef4_19]
  simp only [sg_ef4_w6_2, sg_ef4_w6_4, sg_ef4_w6_6, sg_ef4_w6_8, sg_ef4_w6_9, sg_ef4_w6_12, sg_ef4_w6_14, sg_ef4_w6_16, sg_ef4_w6_18, sg_ef4_w6_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem incidence_ef5 :
    S1.filter (fun y => SS.bxor y ef5 ∈ S0) = {z2, z4, z6, z8, z9, z12, z14, z16, z18, z19} := by decide
theorem flip_ef5_2 : SS.bxor z2 ef5 = y11 := by decide
theorem flip_ef5_4 : SS.bxor z4 ef5 = y13 := by decide
theorem flip_ef5_6 : SS.bxor z6 ef5 = y16 := by decide
theorem flip_ef5_8 : SS.bxor z8 ef5 = y19 := by decide
theorem flip_ef5_9 : SS.bxor z9 ef5 = y20 := by decide
theorem flip_ef5_12 : SS.bxor z12 ef5 = y0 := by decide
theorem flip_ef5_14 : SS.bxor z14 ef5 = y2 := by decide
theorem flip_ef5_16 : SS.bxor z16 ef5 = y5 := by decide
theorem flip_ef5_18 : SS.bxor z18 ef5 = y8 := by decide
theorem flip_ef5_19 : SS.bxor z19 ef5 = y9 := by decide
theorem sg_ef5_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg_ef5_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg_ef5_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg_ef5_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_ef5_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg_ef5_w0_12 : SS.bdot w0 z12 = false := by decide
theorem sg_ef5_w0_14 : SS.bdot w0 z14 = false := by decide
theorem sg_ef5_w0_16 : SS.bdot w0 z16 = false := by decide
theorem sg_ef5_w0_18 : SS.bdot w0 z18 = false := by decide
theorem sg_ef5_w0_19 : SS.bdot w0 z19 = false := by decide
theorem ex_ef5_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef5 w0 = star (c y11) * d z2 + star (c y13) * d z4 + star (c y16) * d z6 + star (c y19) * d z8 + star (c y20) * d z9 + star (c y0) * d z12 + star (c y2) * d z14 + star (c y5) * d z16 + star (c y8) * d z18 + star (c y9) * d z19 := by
  unfold offSum
  rw [incidence_ef5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef5_2, flip_ef5_4, flip_ef5_6, flip_ef5_8, flip_ef5_9, flip_ef5_12, flip_ef5_14, flip_ef5_16, flip_ef5_18, flip_ef5_19]
  simp only [sg_ef5_w0_2, sg_ef5_w0_4, sg_ef5_w0_6, sg_ef5_w0_8, sg_ef5_w0_9, sg_ef5_w0_12, sg_ef5_w0_14, sg_ef5_w0_16, sg_ef5_w0_18, sg_ef5_w0_19, SixQubit.signMul_false]
  try ring
theorem sg_ef5_w6_2 : SS.bdot w6 z2 = false := by decide
theorem sg_ef5_w6_4 : SS.bdot w6 z4 = false := by decide
theorem sg_ef5_w6_6 : SS.bdot w6 z6 = false := by decide
theorem sg_ef5_w6_8 : SS.bdot w6 z8 = false := by decide
theorem sg_ef5_w6_9 : SS.bdot w6 z9 = false := by decide
theorem sg_ef5_w6_12 : SS.bdot w6 z12 = true := by decide
theorem sg_ef5_w6_14 : SS.bdot w6 z14 = true := by decide
theorem sg_ef5_w6_16 : SS.bdot w6 z16 = true := by decide
theorem sg_ef5_w6_18 : SS.bdot w6 z18 = true := by decide
theorem sg_ef5_w6_19 : SS.bdot w6 z19 = true := by decide
theorem ex_ef5_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef5 w6 = star (c y11) * d z2 + star (c y13) * d z4 + star (c y16) * d z6 + star (c y19) * d z8 + star (c y20) * d z9 - star (c y0) * d z12 - star (c y2) * d z14 - star (c y5) * d z16 - star (c y8) * d z18 - star (c y9) * d z19 := by
  unfold offSum
  rw [incidence_ef5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef5_2, flip_ef5_4, flip_ef5_6, flip_ef5_8, flip_ef5_9, flip_ef5_12, flip_ef5_14, flip_ef5_16, flip_ef5_18, flip_ef5_19]
  simp only [sg_ef5_w6_2, sg_ef5_w6_4, sg_ef5_w6_6, sg_ef5_w6_8, sg_ef5_w6_9, sg_ef5_w6_12, sg_ef5_w6_14, sg_ef5_w6_16, sg_ef5_w6_18, sg_ef5_w6_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem incidence_ef6 :
    S1.filter (fun y => SS.bxor y ef6 ∈ S0) = {z1, z4, z6, z7, z9, z11, z14, z16, z17, z19} := by decide
theorem flip_ef6_1 : SS.bxor z1 ef6 = y0 := by decide
theorem flip_ef6_4 : SS.bxor z4 ef6 = y3 := by decide
theorem flip_ef6_6 : SS.bxor z6 ef6 = y6 := by decide
theorem flip_ef6_7 : SS.bxor z7 ef6 = y8 := by decide
theorem flip_ef6_9 : SS.bxor z9 ef6 = y10 := by decide
theorem flip_ef6_11 : SS.bxor z11 ef6 = y11 := by decide
theorem flip_ef6_14 : SS.bxor z14 ef6 = y14 := by decide
theorem flip_ef6_16 : SS.bxor z16 ef6 = y17 := by decide
theorem flip_ef6_17 : SS.bxor z17 ef6 = y19 := by decide
theorem flip_ef6_19 : SS.bxor z19 ef6 = y21 := by decide
theorem sg_ef6_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg_ef6_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg_ef6_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg_ef6_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg_ef6_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg_ef6_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg_ef6_w0_14 : SS.bdot w0 z14 = false := by decide
theorem sg_ef6_w0_16 : SS.bdot w0 z16 = false := by decide
theorem sg_ef6_w0_17 : SS.bdot w0 z17 = false := by decide
theorem sg_ef6_w0_19 : SS.bdot w0 z19 = false := by decide
theorem ex_ef6_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w0 = star (c y0) * d z1 + star (c y3) * d z4 + star (c y6) * d z6 + star (c y8) * d z7 + star (c y10) * d z9 + star (c y11) * d z11 + star (c y14) * d z14 + star (c y17) * d z16 + star (c y19) * d z17 + star (c y21) * d z19 := by
  unfold offSum
  rw [incidence_ef6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef6_1, flip_ef6_4, flip_ef6_6, flip_ef6_7, flip_ef6_9, flip_ef6_11, flip_ef6_14, flip_ef6_16, flip_ef6_17, flip_ef6_19]
  simp only [sg_ef6_w0_1, sg_ef6_w0_4, sg_ef6_w0_6, sg_ef6_w0_7, sg_ef6_w0_9, sg_ef6_w0_11, sg_ef6_w0_14, sg_ef6_w0_16, sg_ef6_w0_17, sg_ef6_w0_19, SixQubit.signMul_false]
  try ring
theorem sg_ef6_w1_1 : SS.bdot w1 z1 = false := by decide
theorem sg_ef6_w1_4 : SS.bdot w1 z4 = true := by decide
theorem sg_ef6_w1_6 : SS.bdot w1 z6 = true := by decide
theorem sg_ef6_w1_7 : SS.bdot w1 z7 = true := by decide
theorem sg_ef6_w1_9 : SS.bdot w1 z9 = false := by decide
theorem sg_ef6_w1_11 : SS.bdot w1 z11 = false := by decide
theorem sg_ef6_w1_14 : SS.bdot w1 z14 = true := by decide
theorem sg_ef6_w1_16 : SS.bdot w1 z16 = true := by decide
theorem sg_ef6_w1_17 : SS.bdot w1 z17 = true := by decide
theorem sg_ef6_w1_19 : SS.bdot w1 z19 = false := by decide
theorem ex_ef6_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w1 = star (c y0) * d z1 - star (c y3) * d z4 - star (c y6) * d z6 - star (c y8) * d z7 + star (c y10) * d z9 + star (c y11) * d z11 - star (c y14) * d z14 - star (c y17) * d z16 - star (c y19) * d z17 + star (c y21) * d z19 := by
  unfold offSum
  rw [incidence_ef6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef6_1, flip_ef6_4, flip_ef6_6, flip_ef6_7, flip_ef6_9, flip_ef6_11, flip_ef6_14, flip_ef6_16, flip_ef6_17, flip_ef6_19]
  simp only [sg_ef6_w1_1, sg_ef6_w1_4, sg_ef6_w1_6, sg_ef6_w1_7, sg_ef6_w1_9, sg_ef6_w1_11, sg_ef6_w1_14, sg_ef6_w1_16, sg_ef6_w1_17, sg_ef6_w1_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef6_w3_1 : SS.bdot w3 z1 = false := by decide
theorem sg_ef6_w3_4 : SS.bdot w3 z4 = true := by decide
theorem sg_ef6_w3_6 : SS.bdot w3 z6 = true := by decide
theorem sg_ef6_w3_7 : SS.bdot w3 z7 = false := by decide
theorem sg_ef6_w3_9 : SS.bdot w3 z9 = true := by decide
theorem sg_ef6_w3_11 : SS.bdot w3 z11 = false := by decide
theorem sg_ef6_w3_14 : SS.bdot w3 z14 = true := by decide
theorem sg_ef6_w3_16 : SS.bdot w3 z16 = true := by decide
theorem sg_ef6_w3_17 : SS.bdot w3 z17 = false := by decide
theorem sg_ef6_w3_19 : SS.bdot w3 z19 = true := by decide
theorem ex_ef6_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w3 = star (c y0) * d z1 - star (c y3) * d z4 - star (c y6) * d z6 + star (c y8) * d z7 - star (c y10) * d z9 + star (c y11) * d z11 - star (c y14) * d z14 - star (c y17) * d z16 + star (c y19) * d z17 - star (c y21) * d z19 := by
  unfold offSum
  rw [incidence_ef6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef6_1, flip_ef6_4, flip_ef6_6, flip_ef6_7, flip_ef6_9, flip_ef6_11, flip_ef6_14, flip_ef6_16, flip_ef6_17, flip_ef6_19]
  simp only [sg_ef6_w3_1, sg_ef6_w3_4, sg_ef6_w3_6, sg_ef6_w3_7, sg_ef6_w3_9, sg_ef6_w3_11, sg_ef6_w3_14, sg_ef6_w3_16, sg_ef6_w3_17, sg_ef6_w3_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef6_w4_1 : SS.bdot w4 z1 = false := by decide
theorem sg_ef6_w4_4 : SS.bdot w4 z4 = true := by decide
theorem sg_ef6_w4_6 : SS.bdot w4 z6 = false := by decide
theorem sg_ef6_w4_7 : SS.bdot w4 z7 = true := by decide
theorem sg_ef6_w4_9 : SS.bdot w4 z9 = true := by decide
theorem sg_ef6_w4_11 : SS.bdot w4 z11 = false := by decide
theorem sg_ef6_w4_14 : SS.bdot w4 z14 = true := by decide
theorem sg_ef6_w4_16 : SS.bdot w4 z16 = false := by decide
theorem sg_ef6_w4_17 : SS.bdot w4 z17 = true := by decide
theorem sg_ef6_w4_19 : SS.bdot w4 z19 = true := by decide
theorem ex_ef6_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w4 = star (c y0) * d z1 - star (c y3) * d z4 + star (c y6) * d z6 - star (c y8) * d z7 - star (c y10) * d z9 + star (c y11) * d z11 - star (c y14) * d z14 + star (c y17) * d z16 - star (c y19) * d z17 - star (c y21) * d z19 := by
  unfold offSum
  rw [incidence_ef6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef6_1, flip_ef6_4, flip_ef6_6, flip_ef6_7, flip_ef6_9, flip_ef6_11, flip_ef6_14, flip_ef6_16, flip_ef6_17, flip_ef6_19]
  simp only [sg_ef6_w4_1, sg_ef6_w4_4, sg_ef6_w4_6, sg_ef6_w4_7, sg_ef6_w4_9, sg_ef6_w4_11, sg_ef6_w4_14, sg_ef6_w4_16, sg_ef6_w4_17, sg_ef6_w4_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef6_w5_1 : SS.bdot w5 z1 = false := by decide
theorem sg_ef6_w5_4 : SS.bdot w5 z4 = false := by decide
theorem sg_ef6_w5_6 : SS.bdot w5 z6 = true := by decide
theorem sg_ef6_w5_7 : SS.bdot w5 z7 = true := by decide
theorem sg_ef6_w5_9 : SS.bdot w5 z9 = true := by decide
theorem sg_ef6_w5_11 : SS.bdot w5 z11 = false := by decide
theorem sg_ef6_w5_14 : SS.bdot w5 z14 = false := by decide
theorem sg_ef6_w5_16 : SS.bdot w5 z16 = true := by decide
theorem sg_ef6_w5_17 : SS.bdot w5 z17 = true := by decide
theorem sg_ef6_w5_19 : SS.bdot w5 z19 = true := by decide
theorem ex_ef6_w5 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w5 = star (c y0) * d z1 + star (c y3) * d z4 - star (c y6) * d z6 - star (c y8) * d z7 - star (c y10) * d z9 + star (c y11) * d z11 + star (c y14) * d z14 - star (c y17) * d z16 - star (c y19) * d z17 - star (c y21) * d z19 := by
  unfold offSum
  rw [incidence_ef6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef6_1, flip_ef6_4, flip_ef6_6, flip_ef6_7, flip_ef6_9, flip_ef6_11, flip_ef6_14, flip_ef6_16, flip_ef6_17, flip_ef6_19]
  simp only [sg_ef6_w5_1, sg_ef6_w5_4, sg_ef6_w5_6, sg_ef6_w5_7, sg_ef6_w5_9, sg_ef6_w5_11, sg_ef6_w5_14, sg_ef6_w5_16, sg_ef6_w5_17, sg_ef6_w5_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef6_w6_1 : SS.bdot w6 z1 = false := by decide
theorem sg_ef6_w6_4 : SS.bdot w6 z4 = false := by decide
theorem sg_ef6_w6_6 : SS.bdot w6 z6 = false := by decide
theorem sg_ef6_w6_7 : SS.bdot w6 z7 = false := by decide
theorem sg_ef6_w6_9 : SS.bdot w6 z9 = false := by decide
theorem sg_ef6_w6_11 : SS.bdot w6 z11 = true := by decide
theorem sg_ef6_w6_14 : SS.bdot w6 z14 = true := by decide
theorem sg_ef6_w6_16 : SS.bdot w6 z16 = true := by decide
theorem sg_ef6_w6_17 : SS.bdot w6 z17 = true := by decide
theorem sg_ef6_w6_19 : SS.bdot w6 z19 = true := by decide
theorem ex_ef6_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w6 = star (c y0) * d z1 + star (c y3) * d z4 + star (c y6) * d z6 + star (c y8) * d z7 + star (c y10) * d z9 - star (c y11) * d z11 - star (c y14) * d z14 - star (c y17) * d z16 - star (c y19) * d z17 - star (c y21) * d z19 := by
  unfold offSum
  rw [incidence_ef6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef6_1, flip_ef6_4, flip_ef6_6, flip_ef6_7, flip_ef6_9, flip_ef6_11, flip_ef6_14, flip_ef6_16, flip_ef6_17, flip_ef6_19]
  simp only [sg_ef6_w6_1, sg_ef6_w6_4, sg_ef6_w6_6, sg_ef6_w6_7, sg_ef6_w6_9, sg_ef6_w6_11, sg_ef6_w6_14, sg_ef6_w6_16, sg_ef6_w6_17, sg_ef6_w6_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem incidence_ef7 :
    S1.filter (fun y => SS.bxor y ef7 ∈ S0) = {z1, z4, z6, z7, z9, z11, z14, z16, z17, z19} := by decide
theorem flip_ef7_1 : SS.bxor z1 ef7 = y11 := by decide
theorem flip_ef7_4 : SS.bxor z4 ef7 = y14 := by decide
theorem flip_ef7_6 : SS.bxor z6 ef7 = y17 := by decide
theorem flip_ef7_7 : SS.bxor z7 ef7 = y19 := by decide
theorem flip_ef7_9 : SS.bxor z9 ef7 = y21 := by decide
theorem flip_ef7_11 : SS.bxor z11 ef7 = y0 := by decide
theorem flip_ef7_14 : SS.bxor z14 ef7 = y3 := by decide
theorem flip_ef7_16 : SS.bxor z16 ef7 = y6 := by decide
theorem flip_ef7_17 : SS.bxor z17 ef7 = y8 := by decide
theorem flip_ef7_19 : SS.bxor z19 ef7 = y10 := by decide
theorem sg_ef7_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg_ef7_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg_ef7_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg_ef7_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg_ef7_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg_ef7_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg_ef7_w0_14 : SS.bdot w0 z14 = false := by decide
theorem sg_ef7_w0_16 : SS.bdot w0 z16 = false := by decide
theorem sg_ef7_w0_17 : SS.bdot w0 z17 = false := by decide
theorem sg_ef7_w0_19 : SS.bdot w0 z19 = false := by decide
theorem ex_ef7_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef7 w0 = star (c y11) * d z1 + star (c y14) * d z4 + star (c y17) * d z6 + star (c y19) * d z7 + star (c y21) * d z9 + star (c y0) * d z11 + star (c y3) * d z14 + star (c y6) * d z16 + star (c y8) * d z17 + star (c y10) * d z19 := by
  unfold offSum
  rw [incidence_ef7]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef7_1, flip_ef7_4, flip_ef7_6, flip_ef7_7, flip_ef7_9, flip_ef7_11, flip_ef7_14, flip_ef7_16, flip_ef7_17, flip_ef7_19]
  simp only [sg_ef7_w0_1, sg_ef7_w0_4, sg_ef7_w0_6, sg_ef7_w0_7, sg_ef7_w0_9, sg_ef7_w0_11, sg_ef7_w0_14, sg_ef7_w0_16, sg_ef7_w0_17, sg_ef7_w0_19, SixQubit.signMul_false]
  try ring
theorem sg_ef7_w6_1 : SS.bdot w6 z1 = false := by decide
theorem sg_ef7_w6_4 : SS.bdot w6 z4 = false := by decide
theorem sg_ef7_w6_6 : SS.bdot w6 z6 = false := by decide
theorem sg_ef7_w6_7 : SS.bdot w6 z7 = false := by decide
theorem sg_ef7_w6_9 : SS.bdot w6 z9 = false := by decide
theorem sg_ef7_w6_11 : SS.bdot w6 z11 = true := by decide
theorem sg_ef7_w6_14 : SS.bdot w6 z14 = true := by decide
theorem sg_ef7_w6_16 : SS.bdot w6 z16 = true := by decide
theorem sg_ef7_w6_17 : SS.bdot w6 z17 = true := by decide
theorem sg_ef7_w6_19 : SS.bdot w6 z19 = true := by decide
theorem ex_ef7_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef7 w6 = star (c y11) * d z1 + star (c y14) * d z4 + star (c y17) * d z6 + star (c y19) * d z7 + star (c y21) * d z9 - star (c y0) * d z11 - star (c y3) * d z14 - star (c y6) * d z16 - star (c y8) * d z17 - star (c y10) * d z19 := by
  unfold offSum
  rw [incidence_ef7]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef7_1, flip_ef7_4, flip_ef7_6, flip_ef7_7, flip_ef7_9, flip_ef7_11, flip_ef7_14, flip_ef7_16, flip_ef7_17, flip_ef7_19]
  simp only [sg_ef7_w6_1, sg_ef7_w6_4, sg_ef7_w6_6, sg_ef7_w6_7, sg_ef7_w6_9, sg_ef7_w6_11, sg_ef7_w6_14, sg_ef7_w6_16, sg_ef7_w6_17, sg_ef7_w6_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem incidence_ef8 :
    S1.filter (fun y => SS.bxor y ef8 ∈ S0) = {z0, z4, z6, z7, z8, z10, z14, z16, z17, z18} := by decide
theorem flip_ef8_0 : SS.bxor z0 ef8 = y0 := by decide
theorem flip_ef8_4 : SS.bxor z4 ef8 = y4 := by decide
theorem flip_ef8_6 : SS.bxor z6 ef8 = y7 := by decide
theorem flip_ef8_7 : SS.bxor z7 ef8 = y9 := by decide
theorem flip_ef8_8 : SS.bxor z8 ef8 = y10 := by decide
theorem flip_ef8_10 : SS.bxor z10 ef8 = y11 := by decide
theorem flip_ef8_14 : SS.bxor z14 ef8 = y15 := by decide
theorem flip_ef8_16 : SS.bxor z16 ef8 = y18 := by decide
theorem flip_ef8_17 : SS.bxor z17 ef8 = y20 := by decide
theorem flip_ef8_18 : SS.bxor z18 ef8 = y21 := by decide
theorem sg_ef8_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg_ef8_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg_ef8_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg_ef8_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg_ef8_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_ef8_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg_ef8_w0_14 : SS.bdot w0 z14 = false := by decide
theorem sg_ef8_w0_16 : SS.bdot w0 z16 = false := by decide
theorem sg_ef8_w0_17 : SS.bdot w0 z17 = false := by decide
theorem sg_ef8_w0_18 : SS.bdot w0 z18 = false := by decide
theorem ex_ef8_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef8 w0 = star (c y0) * d z0 + star (c y4) * d z4 + star (c y7) * d z6 + star (c y9) * d z7 + star (c y10) * d z8 + star (c y11) * d z10 + star (c y15) * d z14 + star (c y18) * d z16 + star (c y20) * d z17 + star (c y21) * d z18 := by
  unfold offSum
  rw [incidence_ef8]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef8_0, flip_ef8_4, flip_ef8_6, flip_ef8_7, flip_ef8_8, flip_ef8_10, flip_ef8_14, flip_ef8_16, flip_ef8_17, flip_ef8_18]
  simp only [sg_ef8_w0_0, sg_ef8_w0_4, sg_ef8_w0_6, sg_ef8_w0_7, sg_ef8_w0_8, sg_ef8_w0_10, sg_ef8_w0_14, sg_ef8_w0_16, sg_ef8_w0_17, sg_ef8_w0_18, SixQubit.signMul_false]
  try ring
theorem sg_ef8_w2_0 : SS.bdot w2 z0 = false := by decide
theorem sg_ef8_w2_4 : SS.bdot w2 z4 = true := by decide
theorem sg_ef8_w2_6 : SS.bdot w2 z6 = true := by decide
theorem sg_ef8_w2_7 : SS.bdot w2 z7 = true := by decide
theorem sg_ef8_w2_8 : SS.bdot w2 z8 = false := by decide
theorem sg_ef8_w2_10 : SS.bdot w2 z10 = false := by decide
theorem sg_ef8_w2_14 : SS.bdot w2 z14 = true := by decide
theorem sg_ef8_w2_16 : SS.bdot w2 z16 = true := by decide
theorem sg_ef8_w2_17 : SS.bdot w2 z17 = true := by decide
theorem sg_ef8_w2_18 : SS.bdot w2 z18 = false := by decide
theorem ex_ef8_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef8 w2 = star (c y0) * d z0 - star (c y4) * d z4 - star (c y7) * d z6 - star (c y9) * d z7 + star (c y10) * d z8 + star (c y11) * d z10 - star (c y15) * d z14 - star (c y18) * d z16 - star (c y20) * d z17 + star (c y21) * d z18 := by
  unfold offSum
  rw [incidence_ef8]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef8_0, flip_ef8_4, flip_ef8_6, flip_ef8_7, flip_ef8_8, flip_ef8_10, flip_ef8_14, flip_ef8_16, flip_ef8_17, flip_ef8_18]
  simp only [sg_ef8_w2_0, sg_ef8_w2_4, sg_ef8_w2_6, sg_ef8_w2_7, sg_ef8_w2_8, sg_ef8_w2_10, sg_ef8_w2_14, sg_ef8_w2_16, sg_ef8_w2_17, sg_ef8_w2_18, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef8_w3_0 : SS.bdot w3 z0 = false := by decide
theorem sg_ef8_w3_4 : SS.bdot w3 z4 = true := by decide
theorem sg_ef8_w3_6 : SS.bdot w3 z6 = true := by decide
theorem sg_ef8_w3_7 : SS.bdot w3 z7 = false := by decide
theorem sg_ef8_w3_8 : SS.bdot w3 z8 = true := by decide
theorem sg_ef8_w3_10 : SS.bdot w3 z10 = false := by decide
theorem sg_ef8_w3_14 : SS.bdot w3 z14 = true := by decide
theorem sg_ef8_w3_16 : SS.bdot w3 z16 = true := by decide
theorem sg_ef8_w3_17 : SS.bdot w3 z17 = false := by decide
theorem sg_ef8_w3_18 : SS.bdot w3 z18 = true := by decide
theorem ex_ef8_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef8 w3 = star (c y0) * d z0 - star (c y4) * d z4 - star (c y7) * d z6 + star (c y9) * d z7 - star (c y10) * d z8 + star (c y11) * d z10 - star (c y15) * d z14 - star (c y18) * d z16 + star (c y20) * d z17 - star (c y21) * d z18 := by
  unfold offSum
  rw [incidence_ef8]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef8_0, flip_ef8_4, flip_ef8_6, flip_ef8_7, flip_ef8_8, flip_ef8_10, flip_ef8_14, flip_ef8_16, flip_ef8_17, flip_ef8_18]
  simp only [sg_ef8_w3_0, sg_ef8_w3_4, sg_ef8_w3_6, sg_ef8_w3_7, sg_ef8_w3_8, sg_ef8_w3_10, sg_ef8_w3_14, sg_ef8_w3_16, sg_ef8_w3_17, sg_ef8_w3_18, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef8_w4_0 : SS.bdot w4 z0 = false := by decide
theorem sg_ef8_w4_4 : SS.bdot w4 z4 = true := by decide
theorem sg_ef8_w4_6 : SS.bdot w4 z6 = false := by decide
theorem sg_ef8_w4_7 : SS.bdot w4 z7 = true := by decide
theorem sg_ef8_w4_8 : SS.bdot w4 z8 = true := by decide
theorem sg_ef8_w4_10 : SS.bdot w4 z10 = false := by decide
theorem sg_ef8_w4_14 : SS.bdot w4 z14 = true := by decide
theorem sg_ef8_w4_16 : SS.bdot w4 z16 = false := by decide
theorem sg_ef8_w4_17 : SS.bdot w4 z17 = true := by decide
theorem sg_ef8_w4_18 : SS.bdot w4 z18 = true := by decide
theorem ex_ef8_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef8 w4 = star (c y0) * d z0 - star (c y4) * d z4 + star (c y7) * d z6 - star (c y9) * d z7 - star (c y10) * d z8 + star (c y11) * d z10 - star (c y15) * d z14 + star (c y18) * d z16 - star (c y20) * d z17 - star (c y21) * d z18 := by
  unfold offSum
  rw [incidence_ef8]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef8_0, flip_ef8_4, flip_ef8_6, flip_ef8_7, flip_ef8_8, flip_ef8_10, flip_ef8_14, flip_ef8_16, flip_ef8_17, flip_ef8_18]
  simp only [sg_ef8_w4_0, sg_ef8_w4_4, sg_ef8_w4_6, sg_ef8_w4_7, sg_ef8_w4_8, sg_ef8_w4_10, sg_ef8_w4_14, sg_ef8_w4_16, sg_ef8_w4_17, sg_ef8_w4_18, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef8_w5_0 : SS.bdot w5 z0 = false := by decide
theorem sg_ef8_w5_4 : SS.bdot w5 z4 = false := by decide
theorem sg_ef8_w5_6 : SS.bdot w5 z6 = true := by decide
theorem sg_ef8_w5_7 : SS.bdot w5 z7 = true := by decide
theorem sg_ef8_w5_8 : SS.bdot w5 z8 = true := by decide
theorem sg_ef8_w5_10 : SS.bdot w5 z10 = false := by decide
theorem sg_ef8_w5_14 : SS.bdot w5 z14 = false := by decide
theorem sg_ef8_w5_16 : SS.bdot w5 z16 = true := by decide
theorem sg_ef8_w5_17 : SS.bdot w5 z17 = true := by decide
theorem sg_ef8_w5_18 : SS.bdot w5 z18 = true := by decide
theorem ex_ef8_w5 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef8 w5 = star (c y0) * d z0 + star (c y4) * d z4 - star (c y7) * d z6 - star (c y9) * d z7 - star (c y10) * d z8 + star (c y11) * d z10 + star (c y15) * d z14 - star (c y18) * d z16 - star (c y20) * d z17 - star (c y21) * d z18 := by
  unfold offSum
  rw [incidence_ef8]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef8_0, flip_ef8_4, flip_ef8_6, flip_ef8_7, flip_ef8_8, flip_ef8_10, flip_ef8_14, flip_ef8_16, flip_ef8_17, flip_ef8_18]
  simp only [sg_ef8_w5_0, sg_ef8_w5_4, sg_ef8_w5_6, sg_ef8_w5_7, sg_ef8_w5_8, sg_ef8_w5_10, sg_ef8_w5_14, sg_ef8_w5_16, sg_ef8_w5_17, sg_ef8_w5_18, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_ef8_w6_0 : SS.bdot w6 z0 = false := by decide
theorem sg_ef8_w6_4 : SS.bdot w6 z4 = false := by decide
theorem sg_ef8_w6_6 : SS.bdot w6 z6 = false := by decide
theorem sg_ef8_w6_7 : SS.bdot w6 z7 = false := by decide
theorem sg_ef8_w6_8 : SS.bdot w6 z8 = false := by decide
theorem sg_ef8_w6_10 : SS.bdot w6 z10 = true := by decide
theorem sg_ef8_w6_14 : SS.bdot w6 z14 = true := by decide
theorem sg_ef8_w6_16 : SS.bdot w6 z16 = true := by decide
theorem sg_ef8_w6_17 : SS.bdot w6 z17 = true := by decide
theorem sg_ef8_w6_18 : SS.bdot w6 z18 = true := by decide
theorem ex_ef8_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef8 w6 = star (c y0) * d z0 + star (c y4) * d z4 + star (c y7) * d z6 + star (c y9) * d z7 + star (c y10) * d z8 - star (c y11) * d z10 - star (c y15) * d z14 - star (c y18) * d z16 - star (c y20) * d z17 - star (c y21) * d z18 := by
  unfold offSum
  rw [incidence_ef8]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef8_0, flip_ef8_4, flip_ef8_6, flip_ef8_7, flip_ef8_8, flip_ef8_10, flip_ef8_14, flip_ef8_16, flip_ef8_17, flip_ef8_18]
  simp only [sg_ef8_w6_0, sg_ef8_w6_4, sg_ef8_w6_6, sg_ef8_w6_7, sg_ef8_w6_8, sg_ef8_w6_10, sg_ef8_w6_14, sg_ef8_w6_16, sg_ef8_w6_17, sg_ef8_w6_18, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem incidence_ef9 :
    S1.filter (fun y => SS.bxor y ef9 ∈ S0) = {z0, z4, z6, z7, z8, z10, z14, z16, z17, z18} := by decide
theorem flip_ef9_0 : SS.bxor z0 ef9 = y11 := by decide
theorem flip_ef9_4 : SS.bxor z4 ef9 = y15 := by decide
theorem flip_ef9_6 : SS.bxor z6 ef9 = y18 := by decide
theorem flip_ef9_7 : SS.bxor z7 ef9 = y20 := by decide
theorem flip_ef9_8 : SS.bxor z8 ef9 = y21 := by decide
theorem flip_ef9_10 : SS.bxor z10 ef9 = y0 := by decide
theorem flip_ef9_14 : SS.bxor z14 ef9 = y4 := by decide
theorem flip_ef9_16 : SS.bxor z16 ef9 = y7 := by decide
theorem flip_ef9_17 : SS.bxor z17 ef9 = y9 := by decide
theorem flip_ef9_18 : SS.bxor z18 ef9 = y10 := by decide
theorem sg_ef9_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg_ef9_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg_ef9_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg_ef9_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg_ef9_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_ef9_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg_ef9_w0_14 : SS.bdot w0 z14 = false := by decide
theorem sg_ef9_w0_16 : SS.bdot w0 z16 = false := by decide
theorem sg_ef9_w0_17 : SS.bdot w0 z17 = false := by decide
theorem sg_ef9_w0_18 : SS.bdot w0 z18 = false := by decide
theorem ex_ef9_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef9 w0 = star (c y11) * d z0 + star (c y15) * d z4 + star (c y18) * d z6 + star (c y20) * d z7 + star (c y21) * d z8 + star (c y0) * d z10 + star (c y4) * d z14 + star (c y7) * d z16 + star (c y9) * d z17 + star (c y10) * d z18 := by
  unfold offSum
  rw [incidence_ef9]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef9_0, flip_ef9_4, flip_ef9_6, flip_ef9_7, flip_ef9_8, flip_ef9_10, flip_ef9_14, flip_ef9_16, flip_ef9_17, flip_ef9_18]
  simp only [sg_ef9_w0_0, sg_ef9_w0_4, sg_ef9_w0_6, sg_ef9_w0_7, sg_ef9_w0_8, sg_ef9_w0_10, sg_ef9_w0_14, sg_ef9_w0_16, sg_ef9_w0_17, sg_ef9_w0_18, SixQubit.signMul_false]
  try ring
theorem sg_ef9_w6_0 : SS.bdot w6 z0 = false := by decide
theorem sg_ef9_w6_4 : SS.bdot w6 z4 = false := by decide
theorem sg_ef9_w6_6 : SS.bdot w6 z6 = false := by decide
theorem sg_ef9_w6_7 : SS.bdot w6 z7 = false := by decide
theorem sg_ef9_w6_8 : SS.bdot w6 z8 = false := by decide
theorem sg_ef9_w6_10 : SS.bdot w6 z10 = true := by decide
theorem sg_ef9_w6_14 : SS.bdot w6 z14 = true := by decide
theorem sg_ef9_w6_16 : SS.bdot w6 z16 = true := by decide
theorem sg_ef9_w6_17 : SS.bdot w6 z17 = true := by decide
theorem sg_ef9_w6_18 : SS.bdot w6 z18 = true := by decide
theorem ex_ef9_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef9 w6 = star (c y11) * d z0 + star (c y15) * d z4 + star (c y18) * d z6 + star (c y20) * d z7 + star (c y21) * d z8 - star (c y0) * d z10 - star (c y4) * d z14 - star (c y7) * d z16 - star (c y9) * d z17 - star (c y10) * d z18 := by
  unfold offSum
  rw [incidence_ef9]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef9_0, flip_ef9_4, flip_ef9_6, flip_ef9_7, flip_ef9_8, flip_ef9_10, flip_ef9_14, flip_ef9_16, flip_ef9_17, flip_ef9_18]
  simp only [sg_ef9_w6_0, sg_ef9_w6_4, sg_ef9_w6_6, sg_ef9_w6_7, sg_ef9_w6_8, sg_ef9_w6_10, sg_ef9_w6_14, sg_ef9_w6_16, sg_ef9_w6_17, sg_ef9_w6_18, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

/-! ## The diagonal layer on the zero-angle qubit -/

def diagBot (c : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ x ∈ S0.filter (fun x => SS.bxor x e ∈ S0),
      SixQubit.signMul (SS.bdot z x) (star (c (SS.bxor x e)) * c x)

def diagTop (dd : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S1),
      SixQubit.signMul (SS.bdot z y) (star (dd (SS.bxor y e)) * dd y)

theorem dincB : S0.filter (fun x => SS.bxor x efA ∈ S0) = {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21} := by decide
theorem dincT : S1.filter (fun y => SS.bxor y efA ∈ S1) = {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19} := by decide
theorem dflipB_0 : SS.bxor y0 efA = y11 := by decide
theorem dflipB_1 : SS.bxor y1 efA = y12 := by decide
theorem dflipB_2 : SS.bxor y2 efA = y13 := by decide
theorem dflipB_3 : SS.bxor y3 efA = y14 := by decide
theorem dflipB_4 : SS.bxor y4 efA = y15 := by decide
theorem dflipB_5 : SS.bxor y5 efA = y16 := by decide
theorem dflipB_6 : SS.bxor y6 efA = y17 := by decide
theorem dflipB_7 : SS.bxor y7 efA = y18 := by decide
theorem dflipB_8 : SS.bxor y8 efA = y19 := by decide
theorem dflipB_9 : SS.bxor y9 efA = y20 := by decide
theorem dflipB_10 : SS.bxor y10 efA = y21 := by decide
theorem dflipB_11 : SS.bxor y11 efA = y0 := by decide
theorem dflipB_12 : SS.bxor y12 efA = y1 := by decide
theorem dflipB_13 : SS.bxor y13 efA = y2 := by decide
theorem dflipB_14 : SS.bxor y14 efA = y3 := by decide
theorem dflipB_15 : SS.bxor y15 efA = y4 := by decide
theorem dflipB_16 : SS.bxor y16 efA = y5 := by decide
theorem dflipB_17 : SS.bxor y17 efA = y6 := by decide
theorem dflipB_18 : SS.bxor y18 efA = y7 := by decide
theorem dflipB_19 : SS.bxor y19 efA = y8 := by decide
theorem dflipB_20 : SS.bxor y20 efA = y9 := by decide
theorem dflipB_21 : SS.bxor y21 efA = y10 := by decide
theorem dflipT_0 : SS.bxor z0 efA = z10 := by decide
theorem dflipT_1 : SS.bxor z1 efA = z11 := by decide
theorem dflipT_2 : SS.bxor z2 efA = z12 := by decide
theorem dflipT_3 : SS.bxor z3 efA = z13 := by decide
theorem dflipT_4 : SS.bxor z4 efA = z14 := by decide
theorem dflipT_5 : SS.bxor z5 efA = z15 := by decide
theorem dflipT_6 : SS.bxor z6 efA = z16 := by decide
theorem dflipT_7 : SS.bxor z7 efA = z17 := by decide
theorem dflipT_8 : SS.bxor z8 efA = z18 := by decide
theorem dflipT_9 : SS.bxor z9 efA = z19 := by decide
theorem dflipT_10 : SS.bxor z10 efA = z0 := by decide
theorem dflipT_11 : SS.bxor z11 efA = z1 := by decide
theorem dflipT_12 : SS.bxor z12 efA = z2 := by decide
theorem dflipT_13 : SS.bxor z13 efA = z3 := by decide
theorem dflipT_14 : SS.bxor z14 efA = z4 := by decide
theorem dflipT_15 : SS.bxor z15 efA = z5 := by decide
theorem dflipT_16 : SS.bxor z16 efA = z6 := by decide
theorem dflipT_17 : SS.bxor z17 efA = z7 := by decide
theorem dflipT_18 : SS.bxor z18 efA = z8 := by decide
theorem dflipT_19 : SS.bxor z19 efA = z9 := by decide

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
theorem dsB_w0_16 : SS.bdot w0 y16 = false := by decide
theorem dsB_w0_17 : SS.bdot w0 y17 = false := by decide
theorem dsB_w0_18 : SS.bdot w0 y18 = false := by decide
theorem dsB_w0_19 : SS.bdot w0 y19 = false := by decide
theorem dsB_w0_20 : SS.bdot w0 y20 = false := by decide
theorem dsB_w0_21 : SS.bdot w0 y21 = false := by decide
theorem dexB_w0 (c : SS.BitString 6 -> ℂ) :
    diagBot c efA w0 = star (c y11) * c y0 + star (c y12) * c y1 + star (c y13) * c y2 + star (c y14) * c y3 + star (c y15) * c y4 + star (c y16) * c y5 + star (c y17) * c y6 + star (c y18) * c y7 + star (c y19) * c y8 + star (c y20) * c y9 + star (c y21) * c y10 + star (c y0) * c y11 + star (c y1) * c y12 + star (c y2) * c y13 + star (c y3) * c y14 + star (c y4) * c y15 + star (c y5) * c y16 + star (c y6) * c y17 + star (c y7) * c y18 + star (c y8) * c y19 + star (c y9) * c y20 + star (c y10) * c y21 := by
  unfold diagBot
  rw [dincB]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipB_0, dflipB_1, dflipB_2, dflipB_3, dflipB_4, dflipB_5, dflipB_6, dflipB_7, dflipB_8, dflipB_9, dflipB_10, dflipB_11, dflipB_12, dflipB_13, dflipB_14, dflipB_15, dflipB_16, dflipB_17, dflipB_18, dflipB_19, dflipB_20, dflipB_21]
  simp only [dsB_w0_0, dsB_w0_1, dsB_w0_2, dsB_w0_3, dsB_w0_4, dsB_w0_5, dsB_w0_6, dsB_w0_7, dsB_w0_8, dsB_w0_9, dsB_w0_10, dsB_w0_11, dsB_w0_12, dsB_w0_13, dsB_w0_14, dsB_w0_15, dsB_w0_16, dsB_w0_17, dsB_w0_18, dsB_w0_19, dsB_w0_20, dsB_w0_21, SixQubit.signMul_false]
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
theorem dsT_w0_16 : SS.bdot w0 z16 = false := by decide
theorem dsT_w0_17 : SS.bdot w0 z17 = false := by decide
theorem dsT_w0_18 : SS.bdot w0 z18 = false := by decide
theorem dsT_w0_19 : SS.bdot w0 z19 = false := by decide
theorem dexT_w0 (dd : SS.BitString 6 -> ℂ) :
    diagTop dd efA w0 = star (dd z10) * dd z0 + star (dd z11) * dd z1 + star (dd z12) * dd z2 + star (dd z13) * dd z3 + star (dd z14) * dd z4 + star (dd z15) * dd z5 + star (dd z16) * dd z6 + star (dd z17) * dd z7 + star (dd z18) * dd z8 + star (dd z19) * dd z9 + star (dd z0) * dd z10 + star (dd z1) * dd z11 + star (dd z2) * dd z12 + star (dd z3) * dd z13 + star (dd z4) * dd z14 + star (dd z5) * dd z15 + star (dd z6) * dd z16 + star (dd z7) * dd z17 + star (dd z8) * dd z18 + star (dd z9) * dd z19 := by
  unfold diagTop
  rw [dincT]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipT_0, dflipT_1, dflipT_2, dflipT_3, dflipT_4, dflipT_5, dflipT_6, dflipT_7, dflipT_8, dflipT_9, dflipT_10, dflipT_11, dflipT_12, dflipT_13, dflipT_14, dflipT_15, dflipT_16, dflipT_17, dflipT_18, dflipT_19]
  simp only [dsT_w0_0, dsT_w0_1, dsT_w0_2, dsT_w0_3, dsT_w0_4, dsT_w0_5, dsT_w0_6, dsT_w0_7, dsT_w0_8, dsT_w0_9, dsT_w0_10, dsT_w0_11, dsT_w0_12, dsT_w0_13, dsT_w0_14, dsT_w0_15, dsT_w0_16, dsT_w0_17, dsT_w0_18, dsT_w0_19, SixQubit.signMul_false]
  try ring

theorem dsB_w6_0 : SS.bdot w6 y0 = false := by decide
theorem dsB_w6_1 : SS.bdot w6 y1 = false := by decide
theorem dsB_w6_2 : SS.bdot w6 y2 = false := by decide
theorem dsB_w6_3 : SS.bdot w6 y3 = false := by decide
theorem dsB_w6_4 : SS.bdot w6 y4 = false := by decide
theorem dsB_w6_5 : SS.bdot w6 y5 = false := by decide
theorem dsB_w6_6 : SS.bdot w6 y6 = false := by decide
theorem dsB_w6_7 : SS.bdot w6 y7 = false := by decide
theorem dsB_w6_8 : SS.bdot w6 y8 = false := by decide
theorem dsB_w6_9 : SS.bdot w6 y9 = false := by decide
theorem dsB_w6_10 : SS.bdot w6 y10 = false := by decide
theorem dsB_w6_11 : SS.bdot w6 y11 = true := by decide
theorem dsB_w6_12 : SS.bdot w6 y12 = true := by decide
theorem dsB_w6_13 : SS.bdot w6 y13 = true := by decide
theorem dsB_w6_14 : SS.bdot w6 y14 = true := by decide
theorem dsB_w6_15 : SS.bdot w6 y15 = true := by decide
theorem dsB_w6_16 : SS.bdot w6 y16 = true := by decide
theorem dsB_w6_17 : SS.bdot w6 y17 = true := by decide
theorem dsB_w6_18 : SS.bdot w6 y18 = true := by decide
theorem dsB_w6_19 : SS.bdot w6 y19 = true := by decide
theorem dsB_w6_20 : SS.bdot w6 y20 = true := by decide
theorem dsB_w6_21 : SS.bdot w6 y21 = true := by decide
theorem dexB_w6 (c : SS.BitString 6 -> ℂ) :
    diagBot c efA w6 = star (c y11) * c y0 + star (c y12) * c y1 + star (c y13) * c y2 + star (c y14) * c y3 + star (c y15) * c y4 + star (c y16) * c y5 + star (c y17) * c y6 + star (c y18) * c y7 + star (c y19) * c y8 + star (c y20) * c y9 + star (c y21) * c y10 - star (c y0) * c y11 - star (c y1) * c y12 - star (c y2) * c y13 - star (c y3) * c y14 - star (c y4) * c y15 - star (c y5) * c y16 - star (c y6) * c y17 - star (c y7) * c y18 - star (c y8) * c y19 - star (c y9) * c y20 - star (c y10) * c y21 := by
  unfold diagBot
  rw [dincB]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipB_0, dflipB_1, dflipB_2, dflipB_3, dflipB_4, dflipB_5, dflipB_6, dflipB_7, dflipB_8, dflipB_9, dflipB_10, dflipB_11, dflipB_12, dflipB_13, dflipB_14, dflipB_15, dflipB_16, dflipB_17, dflipB_18, dflipB_19, dflipB_20, dflipB_21]
  simp only [dsB_w6_0, dsB_w6_1, dsB_w6_2, dsB_w6_3, dsB_w6_4, dsB_w6_5, dsB_w6_6, dsB_w6_7, dsB_w6_8, dsB_w6_9, dsB_w6_10, dsB_w6_11, dsB_w6_12, dsB_w6_13, dsB_w6_14, dsB_w6_15, dsB_w6_16, dsB_w6_17, dsB_w6_18, dsB_w6_19, dsB_w6_20, dsB_w6_21, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem dsT_w6_0 : SS.bdot w6 z0 = false := by decide
theorem dsT_w6_1 : SS.bdot w6 z1 = false := by decide
theorem dsT_w6_2 : SS.bdot w6 z2 = false := by decide
theorem dsT_w6_3 : SS.bdot w6 z3 = false := by decide
theorem dsT_w6_4 : SS.bdot w6 z4 = false := by decide
theorem dsT_w6_5 : SS.bdot w6 z5 = false := by decide
theorem dsT_w6_6 : SS.bdot w6 z6 = false := by decide
theorem dsT_w6_7 : SS.bdot w6 z7 = false := by decide
theorem dsT_w6_8 : SS.bdot w6 z8 = false := by decide
theorem dsT_w6_9 : SS.bdot w6 z9 = false := by decide
theorem dsT_w6_10 : SS.bdot w6 z10 = true := by decide
theorem dsT_w6_11 : SS.bdot w6 z11 = true := by decide
theorem dsT_w6_12 : SS.bdot w6 z12 = true := by decide
theorem dsT_w6_13 : SS.bdot w6 z13 = true := by decide
theorem dsT_w6_14 : SS.bdot w6 z14 = true := by decide
theorem dsT_w6_15 : SS.bdot w6 z15 = true := by decide
theorem dsT_w6_16 : SS.bdot w6 z16 = true := by decide
theorem dsT_w6_17 : SS.bdot w6 z17 = true := by decide
theorem dsT_w6_18 : SS.bdot w6 z18 = true := by decide
theorem dsT_w6_19 : SS.bdot w6 z19 = true := by decide
theorem dexT_w6 (dd : SS.BitString 6 -> ℂ) :
    diagTop dd efA w6 = star (dd z10) * dd z0 + star (dd z11) * dd z1 + star (dd z12) * dd z2 + star (dd z13) * dd z3 + star (dd z14) * dd z4 + star (dd z15) * dd z5 + star (dd z16) * dd z6 + star (dd z17) * dd z7 + star (dd z18) * dd z8 + star (dd z19) * dd z9 - star (dd z0) * dd z10 - star (dd z1) * dd z11 - star (dd z2) * dd z12 - star (dd z3) * dd z13 - star (dd z4) * dd z14 - star (dd z5) * dd z15 - star (dd z6) * dd z16 - star (dd z7) * dd z17 - star (dd z8) * dd z18 - star (dd z9) * dd z19 := by
  unfold diagTop
  rw [dincT]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dflipT_0, dflipT_1, dflipT_2, dflipT_3, dflipT_4, dflipT_5, dflipT_6, dflipT_7, dflipT_8, dflipT_9, dflipT_10, dflipT_11, dflipT_12, dflipT_13, dflipT_14, dflipT_15, dflipT_16, dflipT_17, dflipT_18, dflipT_19]
  simp only [dsT_w6_0, dsT_w6_1, dsT_w6_2, dsT_w6_3, dsT_w6_4, dsT_w6_5, dsT_w6_6, dsT_w6_7, dsT_w6_8, dsT_w6_9, dsT_w6_10, dsT_w6_11, dsT_w6_12, dsT_w6_13, dsT_w6_14, dsT_w6_15, dsT_w6_16, dsT_w6_17, dsT_w6_18, dsT_w6_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

/-! ## The moment system -/

/-- The two normalizations, the twenty-one moment equalities, and the
nonnegativity of every probability. -/
structure MomentSystem (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 : Real) : Prop where
  n0 : q0 + q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 + q9 + q10 + q11 + q12 + q13 + q14 + q15 + q16 + q17 + q18 + q19 + q20 + q21 = 1
  n1 : r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15 + r16 + r17 + r18 + r19 = 1
  m1 : q11 + q12 + q13 + q14 + q15 + q16 + q17 + q18 + q19 + q20 + q21 = r10 + r11 + r12 + r13 + r14 + r15 + r16 + r17 + r18 + r19
  m2 : q5 + q6 + q7 + q8 + q9 + q10 + q16 + q17 + q18 + q19 + q20 + q21 = r5 + r6 + r7 + r8 + r9 + r15 + r16 + r17 + r18 + r19
  m3 : q2 + q3 + q4 + q8 + q9 + q10 + q13 + q14 + q15 + q19 + q20 + q21 = r3 + r4 + r7 + r8 + r9 + r13 + r14 + r17 + r18 + r19
  m4 : q1 + q3 + q4 + q6 + q7 + q10 + q12 + q14 + q15 + q17 + q18 + q21 = r2 + r4 + r6 + r8 + r9 + r12 + r14 + r16 + r18 + r19
  m5 : q1 + q2 + q4 + q5 + q7 + q9 + q12 + q13 + q15 + q16 + q18 + q20 = r1 + r4 + r6 + r7 + r9 + r11 + r14 + r16 + r17 + r19
  m6 : q1 + q2 + q3 + q5 + q6 + q8 + q12 + q13 + q14 + q16 + q17 + q19 = r0 + r4 + r6 + r7 + r8 + r10 + r14 + r16 + r17 + r18
  m12 : q16 + q17 + q18 + q19 + q20 + q21 = r15 + r16 + r17 + r18 + r19
  m13 : q13 + q14 + q15 + q19 + q20 + q21 = r13 + r14 + r17 + r18 + r19
  m14 : q12 + q14 + q15 + q17 + q18 + q21 = r12 + r14 + r16 + r18 + r19
  m15 : q12 + q13 + q15 + q16 + q18 + q20 = r11 + r14 + r16 + r17 + r19
  m16 : q12 + q13 + q14 + q16 + q17 + q19 = r10 + r14 + r16 + r17 + r18
  m23 : q8 + q9 + q10 + q19 + q20 + q21 = r7 + r8 + r9 + r17 + r18 + r19
  m24 : q6 + q7 + q10 + q17 + q18 + q21 = r6 + r8 + r9 + r16 + r18 + r19
  m25 : q5 + q7 + q9 + q16 + q18 + q20 = r6 + r7 + r9 + r16 + r17 + r19
  m26 : q5 + q6 + q8 + q16 + q17 + q19 = r6 + r7 + r8 + r16 + r17 + r18
  m34 : q3 + q4 + q10 + q14 + q15 + q21 = r4 + r8 + r9 + r14 + r18 + r19
  m35 : q2 + q4 + q9 + q13 + q15 + q20 = r4 + r7 + r9 + r14 + r17 + r19
  m36 : q2 + q3 + q8 + q13 + q14 + q19 = r4 + r7 + r8 + r14 + r17 + r18
  m45 : q1 + q4 + q7 + q12 + q15 + q18 = r4 + r6 + r9 + r14 + r16 + r19
  m46 : q1 + q3 + q6 + q12 + q14 + q17 = r4 + r6 + r8 + r14 + r16 + r18
  m56 : q1 + q2 + q5 + q12 + q13 + q16 = r4 + r6 + r7 + r14 + r16 + r17

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
  nq16 : 0 ≤ q16
  nq17 : 0 ≤ q17
  nq18 : 0 ≤ q18
  nq19 : 0 ≤ q19
  nq20 : 0 ≤ q20
  nq21 : 0 ≤ q21
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
  nr16 : 0 ≤ r16
  nr17 : 0 ≤ r17
  nr18 : 0 ≤ r18
  nr19 : 0 ≤ r19

/-- The anchor mass, the two shell masses, and the two diagonal entries
of the reduced state on the zero-angle qubit. -/
theorem MomentSystem.facts {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19) :
    q0 + q11 = 1/3
    ∧ r4 + r14 + r6 + r16 + r7 + r17 + r8 + r18 + r9 + r19 = 1/3
    ∧ r5 + r15 + r3 + r13 + r2 + r12 + r1 + r11 + r0 + r10 = 2/3
    ∧ q0 + q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 + q9 + q10 = r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9
    ∧ q11 + q12 + q13 + q14 + q15 + q16 + q17 + q18 + q19 + q20 + q21 = r10 + r11 + r12 + r13 + r14 + r15 + r16 + r17 + r18 + r19
    := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, m12, m13, m14, m15, m16, m23, m24, m25, m26, m34, m35, m36, m45, m46, m56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nq16, nq17, nq18, nq19, nq20, nq21, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15, nr16, nr17, nr18, nr19⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-! ## The no-go -/

/-- **Orbit 6 is impossible.** -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11)) (Complex.normSq (c y12)) (Complex.normSq (c y13)) (Complex.normSq (c y14)) (Complex.normSq (c y15)) (Complex.normSq (c y16)) (Complex.normSq (c y17)) (Complex.normSq (c y18)) (Complex.normSq (c y19)) (Complex.normSq (c y20)) (Complex.normSq (c y21))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)) (Complex.normSq (d z12)) (Complex.normSq (d z13)) (Complex.normSq (d z14)) (Complex.normSq (d z15)) (Complex.normSq (d z16)) (Complex.normSq (d z17)) (Complex.normSq (d z18)) (Complex.normSq (d z19)))
    (ho0 : offSum c d ef0 w0 = 0)
    (ho1 : offSum c d ef0 w6 = 0)
    (ho2 : offSum c d ef1 w0 = 0)
    (ho3 : offSum c d ef1 w6 = 0)
    (ho4 : offSum c d ef0 w1 = 0)
    (ho5 : offSum c d ef0 w2 = 0)
    (ho6 : offSum c d ef0 w3 = 0)
    (ho7 : offSum c d ef0 w4 = 0)
    (ho8 : offSum c d ef2 w0 = 0)
    (ho9 : offSum c d ef2 w6 = 0)
    (ho10 : offSum c d ef3 w0 = 0)
    (ho11 : offSum c d ef3 w6 = 0)
    (ho12 : offSum c d ef2 w1 = 0)
    (ho13 : offSum c d ef2 w2 = 0)
    (ho14 : offSum c d ef2 w3 = 0)
    (ho15 : offSum c d ef2 w5 = 0)
    (ho16 : offSum c d ef4 w0 = 0)
    (ho17 : offSum c d ef4 w6 = 0)
    (ho18 : offSum c d ef5 w0 = 0)
    (ho19 : offSum c d ef5 w6 = 0)
    (ho20 : offSum c d ef4 w1 = 0)
    (ho21 : offSum c d ef4 w2 = 0)
    (ho22 : offSum c d ef4 w4 = 0)
    (ho23 : offSum c d ef4 w5 = 0)
    (ho24 : offSum c d ef6 w0 = 0)
    (ho25 : offSum c d ef6 w6 = 0)
    (ho26 : offSum c d ef7 w0 = 0)
    (ho27 : offSum c d ef7 w6 = 0)
    (ho28 : offSum c d ef6 w1 = 0)
    (ho29 : offSum c d ef6 w3 = 0)
    (ho30 : offSum c d ef6 w4 = 0)
    (ho31 : offSum c d ef6 w5 = 0)
    (ho32 : offSum c d ef8 w0 = 0)
    (ho33 : offSum c d ef8 w6 = 0)
    (ho34 : offSum c d ef9 w0 = 0)
    (ho35 : offSum c d ef9 w6 = 0)
    (ho36 : offSum c d ef8 w2 = 0)
    (ho37 : offSum c d ef8 w3 = 0)
    (ho38 : offSum c d ef8 w4 = 0)
    (ho39 : offSum c d ef8 w5 = 0)
    (hd0 : diagBot c efA w0 = diagTop d efA w0)
    (hd1 : diagBot c efA w6 = diagTop d efA w6)
    : False := by
  rw [ex_ef0_w0] at ho0
  rw [ex_ef0_w6] at ho1
  rw [ex_ef1_w0] at ho2
  rw [ex_ef1_w6] at ho3
  rw [ex_ef0_w1] at ho4
  rw [ex_ef0_w2] at ho5
  rw [ex_ef0_w3] at ho6
  rw [ex_ef0_w4] at ho7
  rw [ex_ef2_w0] at ho8
  rw [ex_ef2_w6] at ho9
  rw [ex_ef3_w0] at ho10
  rw [ex_ef3_w6] at ho11
  rw [ex_ef2_w1] at ho12
  rw [ex_ef2_w2] at ho13
  rw [ex_ef2_w3] at ho14
  rw [ex_ef2_w5] at ho15
  rw [ex_ef4_w0] at ho16
  rw [ex_ef4_w6] at ho17
  rw [ex_ef5_w0] at ho18
  rw [ex_ef5_w6] at ho19
  rw [ex_ef4_w1] at ho20
  rw [ex_ef4_w2] at ho21
  rw [ex_ef4_w4] at ho22
  rw [ex_ef4_w5] at ho23
  rw [ex_ef6_w0] at ho24
  rw [ex_ef6_w6] at ho25
  rw [ex_ef7_w0] at ho26
  rw [ex_ef7_w6] at ho27
  rw [ex_ef6_w1] at ho28
  rw [ex_ef6_w3] at ho29
  rw [ex_ef6_w4] at ho30
  rw [ex_ef6_w5] at ho31
  rw [ex_ef8_w0] at ho32
  rw [ex_ef8_w6] at ho33
  rw [ex_ef9_w0] at ho34
  rw [ex_ef9_w6] at ho35
  rw [ex_ef8_w2] at ho36
  rw [ex_ef8_w3] at ho37
  rw [ex_ef8_w4] at ho38
  rw [ex_ef8_w5] at ho39
  rw [dexB_w0, dexT_w0] at hd0
  rw [dexB_w6, dexT_w6] at hd1
  obtain ⟨hR, hC, hB, hA0, hA1⟩ := hm.facts
  have hP1 : star (c y0) * d z5 + star (c y11) * d z15 = 0 := by
    linear_combination (1/3 : ℂ) * ho0 + (1/6 : ℂ) * ho4 + (1/6 : ℂ) * ho5 + (1/6 : ℂ) * ho6 + (1/6 : ℂ) * ho7
  have nP1 : Complex.normSq (star (c y0) * d z5 + star (c y11) * d z15) = 0 := by
    rw [hP1]; simp
  have hP2 : star (c y0) * d z3 + star (c y11) * d z13 = 0 := by
    linear_combination (1/3 : ℂ) * ho8 + (1/6 : ℂ) * ho12 + (1/6 : ℂ) * ho13 + (1/6 : ℂ) * ho14 + (1/6 : ℂ) * ho15
  have nP2 : Complex.normSq (star (c y0) * d z3 + star (c y11) * d z13) = 0 := by
    rw [hP2]; simp
  have hP3 : star (c y0) * d z2 + star (c y11) * d z12 = 0 := by
    linear_combination (1/3 : ℂ) * ho16 + (1/6 : ℂ) * ho20 + (1/6 : ℂ) * ho21 + (1/6 : ℂ) * ho22 + (1/6 : ℂ) * ho23
  have nP3 : Complex.normSq (star (c y0) * d z2 + star (c y11) * d z12) = 0 := by
    rw [hP3]; simp
  have hP4 : star (c y0) * d z1 + star (c y11) * d z11 = 0 := by
    linear_combination (1/3 : ℂ) * ho24 + (1/6 : ℂ) * ho28 + (1/6 : ℂ) * ho29 + (1/6 : ℂ) * ho30 + (1/6 : ℂ) * ho31
  have nP4 : Complex.normSq (star (c y0) * d z1 + star (c y11) * d z11) = 0 := by
    rw [hP4]; simp
  have hP5 : star (c y0) * d z0 + star (c y11) * d z10 = 0 := by
    linear_combination (1/3 : ℂ) * ho32 + (1/6 : ℂ) * ho36 + (1/6 : ℂ) * ho37 + (1/6 : ℂ) * ho38 + (1/6 : ℂ) * ho39
  have nP5 : Complex.normSq (star (c y0) * d z0 + star (c y11) * d z10) = 0 := by
    rw [hP5]; simp
  have Roff : star (c y11) * c y0 + star (c y12) * c y1 + star (c y13) * c y2 + star (c y14) * c y3 + star (c y15) * c y4 + star (c y16) * c y5 + star (c y17) * c y6 + star (c y18) * c y7 + star (c y19) * c y8 + star (c y20) * c y9 + star (c y21) * c y10
      = star (d z15) * d z5 + star (d z13) * d z3 + star (d z12) * d z2 + star (d z11) * d z1 + star (d z10) * d z0 + star (d z14) * d z4 + star (d z16) * d z6 + star (d z17) * d z7 + star (d z18) * d z8 + star (d z19) * d z9 := by
    linear_combination (1/2 : ℂ) * hd0 + (1/2 : ℂ) * hd1
  have Rofs : star (c y0) * c y11 + star (c y1) * c y12 + star (c y2) * c y13 + star (c y3) * c y14 + star (c y4) * c y15 + star (c y5) * c y16 + star (c y6) * c y17 + star (c y7) * c y18 + star (c y8) * c y19 + star (c y9) * c y20 + star (c y10) * c y21
      = star (d z5) * d z15 + star (d z3) * d z13 + star (d z2) * d z12 + star (d z1) * d z11 + star (d z0) * d z10 + star (d z4) * d z14 + star (d z6) * d z16 + star (d z7) * d z17 + star (d z8) * d z18 + star (d z9) * d z19 := by
    linear_combination (1/2 : ℂ) * hd0 + (-1/2 : ℂ) * hd1
  have Rc00 : star (c y0) * c y0 + star (c y1) * c y1 + star (c y2) * c y2 + star (c y3) * c y3 + star (c y4) * c y4 + star (c y5) * c y5 + star (c y6) * c y6 + star (c y7) * c y7 + star (c y8) * c y8 + star (c y9) * c y9 + star (c y10) * c y10
      = star (d z5) * d z5 + star (d z3) * d z3 + star (d z2) * d z2 + star (d z1) * d z1 + star (d z0) * d z0 + star (d z4) * d z4 + star (d z6) * d z6 + star (d z7) * d z7 + star (d z8) * d z8 + star (d z9) * d z9 := by
    have hc := congrArg (fun x : ℝ => (x : ℂ)) hA0
    push_cast at hc
    simp only [← SixQubit.star_mul_self] at hc
    linear_combination hc
  have Rc11 : star (c y11) * c y11 + star (c y12) * c y12 + star (c y13) * c y13 + star (c y14) * c y14 + star (c y15) * c y15 + star (c y16) * c y16 + star (c y17) * c y17 + star (c y18) * c y18 + star (c y19) * c y19 + star (c y20) * c y20 + star (c y21) * c y21
      = star (d z15) * d z15 + star (d z13) * d z13 + star (d z12) * d z12 + star (d z11) * d z11 + star (d z10) * d z10 + star (d z14) * d z14 + star (d z16) * d z16 + star (d z17) * d z17 + star (d z18) * d z18 + star (d z19) * d z19 := by
    have hc := congrArg (fun x : ℝ => (x : ℂ)) hA1
    push_cast at hc
    simp only [← SixQubit.star_mul_self] at hc
    linear_combination hc
  have main :
      (c y0 * star (c y0) + c y11 * star (c y11)) * (star (c y0) * c y0 + star (c y11) * c y11)
        + (c y1 * star (c y0) + c y12 * star (c y11)) * (star (c y1) * c y0 + star (c y12) * c y11)
        + (c y2 * star (c y0) + c y13 * star (c y11)) * (star (c y2) * c y0 + star (c y13) * c y11)
        + (c y3 * star (c y0) + c y14 * star (c y11)) * (star (c y3) * c y0 + star (c y14) * c y11)
        + (c y4 * star (c y0) + c y15 * star (c y11)) * (star (c y4) * c y0 + star (c y15) * c y11)
        + (c y5 * star (c y0) + c y16 * star (c y11)) * (star (c y5) * c y0 + star (c y16) * c y11)
        + (c y6 * star (c y0) + c y17 * star (c y11)) * (star (c y6) * c y0 + star (c y17) * c y11)
        + (c y7 * star (c y0) + c y18 * star (c y11)) * (star (c y7) * c y0 + star (c y18) * c y11)
        + (c y8 * star (c y0) + c y19 * star (c y11)) * (star (c y8) * c y0 + star (c y19) * c y11)
        + (c y9 * star (c y0) + c y20 * star (c y11)) * (star (c y9) * c y0 + star (c y20) * c y11)
        + (c y10 * star (c y0) + c y21 * star (c y11)) * (star (c y10) * c y0 + star (c y21) * c y11)
      = (c y0 * star (d z5) + c y11 * star (d z15)) * (star (c y0) * d z5 + star (c y11) * d z15)
        + (c y0 * star (d z3) + c y11 * star (d z13)) * (star (c y0) * d z3 + star (c y11) * d z13)
        + (c y0 * star (d z2) + c y11 * star (d z12)) * (star (c y0) * d z2 + star (c y11) * d z12)
        + (c y0 * star (d z1) + c y11 * star (d z11)) * (star (c y0) * d z1 + star (c y11) * d z11)
        + (c y0 * star (d z0) + c y11 * star (d z10)) * (star (c y0) * d z0 + star (c y11) * d z10)
        + (c y0 * star (d z4) + c y11 * star (d z14)) * (star (c y0) * d z4 + star (c y11) * d z14)
        + (c y0 * star (d z6) + c y11 * star (d z16)) * (star (c y0) * d z6 + star (c y11) * d z16)
        + (c y0 * star (d z7) + c y11 * star (d z17)) * (star (c y0) * d z7 + star (c y11) * d z17)
        + (c y0 * star (d z8) + c y11 * star (d z18)) * (star (c y0) * d z8 + star (c y11) * d z18)
        + (c y0 * star (d z9) + c y11 * star (d z19)) * (star (c y0) * d z9 + star (c y11) * d z19) := by
    linear_combination (star (c y0) * c y0) * Rc00 + (star (c y11) * c y11) * Rc11
      + (star (c y0) * c y11) * Roff + (star (c y11) * c y0) * Rofs
  have hreal :
      (Complex.normSq (c y0) + Complex.normSq (c y11)) * (Complex.normSq (c y0) + Complex.normSq (c y11))
        + Complex.normSq (star (c y1) * c y0 + star (c y12) * c y11)
        + Complex.normSq (star (c y2) * c y0 + star (c y13) * c y11)
        + Complex.normSq (star (c y3) * c y0 + star (c y14) * c y11)
        + Complex.normSq (star (c y4) * c y0 + star (c y15) * c y11)
        + Complex.normSq (star (c y5) * c y0 + star (c y16) * c y11)
        + Complex.normSq (star (c y6) * c y0 + star (c y17) * c y11)
        + Complex.normSq (star (c y7) * c y0 + star (c y18) * c y11)
        + Complex.normSq (star (c y8) * c y0 + star (c y19) * c y11)
        + Complex.normSq (star (c y9) * c y0 + star (c y20) * c y11)
        + Complex.normSq (star (c y10) * c y0 + star (c y21) * c y11)
      = Complex.normSq (star (c y0) * d z5 + star (c y11) * d z15)
        + Complex.normSq (star (c y0) * d z3 + star (c y11) * d z13)
        + Complex.normSq (star (c y0) * d z2 + star (c y11) * d z12)
        + Complex.normSq (star (c y0) * d z1 + star (c y11) * d z11)
        + Complex.normSq (star (c y0) * d z0 + star (c y11) * d z10)
        + Complex.normSq (star (c y0) * d z4 + star (c y11) * d z14)
        + Complex.normSq (star (c y0) * d z6 + star (c y11) * d z16)
        + Complex.normSq (star (c y0) * d z7 + star (c y11) * d z17)
        + Complex.normSq (star (c y0) * d z8 + star (c y11) * d z18)
        + Complex.normSq (star (c y0) * d z9 + star (c y11) * d z19) := by
    have hc : (((Complex.normSq (c y0) + Complex.normSq (c y11)) * (Complex.normSq (c y0) + Complex.normSq (c y11)) + Complex.normSq (star (c y1) * c y0 + star (c y12) * c y11) + Complex.normSq (star (c y2) * c y0 + star (c y13) * c y11) + Complex.normSq (star (c y3) * c y0 + star (c y14) * c y11) + Complex.normSq (star (c y4) * c y0 + star (c y15) * c y11) + Complex.normSq (star (c y5) * c y0 + star (c y16) * c y11) + Complex.normSq (star (c y6) * c y0 + star (c y17) * c y11) + Complex.normSq (star (c y7) * c y0 + star (c y18) * c y11) + Complex.normSq (star (c y8) * c y0 + star (c y19) * c y11) + Complex.normSq (star (c y9) * c y0 + star (c y20) * c y11) + Complex.normSq (star (c y10) * c y0 + star (c y21) * c y11) : ℝ) : ℂ)
        = ((Complex.normSq (star (c y0) * d z5 + star (c y11) * d z15) + Complex.normSq (star (c y0) * d z3 + star (c y11) * d z13) + Complex.normSq (star (c y0) * d z2 + star (c y11) * d z12) + Complex.normSq (star (c y0) * d z1 + star (c y11) * d z11) + Complex.normSq (star (c y0) * d z0 + star (c y11) * d z10) + Complex.normSq (star (c y0) * d z4 + star (c y11) * d z14) + Complex.normSq (star (c y0) * d z6 + star (c y11) * d z16) + Complex.normSq (star (c y0) * d z7 + star (c y11) * d z17) + Complex.normSq (star (c y0) * d z8 + star (c y11) * d z18) + Complex.normSq (star (c y0) * d z9 + star (c y11) * d z19) : ℝ) : ℂ) := by
      push_cast
      simp only [← SixQubit.star_mul_self, star_add, star_mul', star_star]
      linear_combination main
    exact_mod_cast hc
  rw [hR] at hreal
  have hL1 := SixQubit.Spinor.lagrange (c y0) (c y11) (d z4) (d z14)
  rw [hR] at hL1
  have hL2 := SixQubit.Spinor.lagrange (c y0) (c y11) (d z6) (d z16)
  rw [hR] at hL2
  have hL3 := SixQubit.Spinor.lagrange (c y0) (c y11) (d z7) (d z17)
  rw [hR] at hL3
  have hL4 := SixQubit.Spinor.lagrange (c y0) (c y11) (d z8) (d z18)
  rw [hR] at hL4
  have hL5 := SixQubit.Spinor.lagrange (c y0) (c y11) (d z9) (d z19)
  rw [hR] at hL5
  have hz :
      Complex.normSq (star (c y1) * c y0 + star (c y12) * c y11)
        + Complex.normSq (star (c y2) * c y0 + star (c y13) * c y11)
        + Complex.normSq (star (c y3) * c y0 + star (c y14) * c y11)
        + Complex.normSq (star (c y4) * c y0 + star (c y15) * c y11)
        + Complex.normSq (star (c y5) * c y0 + star (c y16) * c y11)
        + Complex.normSq (star (c y6) * c y0 + star (c y17) * c y11)
        + Complex.normSq (star (c y7) * c y0 + star (c y18) * c y11)
        + Complex.normSq (star (c y8) * c y0 + star (c y19) * c y11)
        + Complex.normSq (star (c y9) * c y0 + star (c y20) * c y11)
        + Complex.normSq (star (c y10) * c y0 + star (c y21) * c y11)
        + Complex.normSq (c y0 * d z14 - c y11 * d z4)
        + Complex.normSq (c y0 * d z16 - c y11 * d z6)
        + Complex.normSq (c y0 * d z17 - c y11 * d z7)
        + Complex.normSq (c y0 * d z18 - c y11 * d z8)
        + Complex.normSq (c y0 * d z19 - c y11 * d z9)
      = 0 := by
    linarith only [hreal, hC, hL1, hL2, hL3, hL4, hL5, nP1, nP2, nP3, nP4, nP5]
  have ha0 : star (c y1) * c y0 + star (c y12) * c y11 = 0 :=
    Complex.normSq_eq_zero.mp (by linarith only [hz, Complex.normSq_nonneg (star (c y1) * c y0 + star (c y12) * c y11), Complex.normSq_nonneg (star (c y2) * c y0 + star (c y13) * c y11), Complex.normSq_nonneg (star (c y3) * c y0 + star (c y14) * c y11), Complex.normSq_nonneg (star (c y4) * c y0 + star (c y15) * c y11), Complex.normSq_nonneg (star (c y5) * c y0 + star (c y16) * c y11), Complex.normSq_nonneg (star (c y6) * c y0 + star (c y17) * c y11), Complex.normSq_nonneg (star (c y7) * c y0 + star (c y18) * c y11), Complex.normSq_nonneg (star (c y8) * c y0 + star (c y19) * c y11), Complex.normSq_nonneg (star (c y9) * c y0 + star (c y20) * c y11), Complex.normSq_nonneg (star (c y10) * c y0 + star (c y21) * c y11), Complex.normSq_nonneg (c y0 * d z14 - c y11 * d z4), Complex.normSq_nonneg (c y0 * d z16 - c y11 * d z6), Complex.normSq_nonneg (c y0 * d z17 - c y11 * d z7), Complex.normSq_nonneg (c y0 * d z18 - c y11 * d z8), Complex.normSq_nonneg (c y0 * d z19 - c y11 * d z9)])
  have ha1 : star (c y2) * c y0 + star (c y13) * c y11 = 0 :=
    Complex.normSq_eq_zero.mp (by linarith only [hz, Complex.normSq_nonneg (star (c y1) * c y0 + star (c y12) * c y11), Complex.normSq_nonneg (star (c y2) * c y0 + star (c y13) * c y11), Complex.normSq_nonneg (star (c y3) * c y0 + star (c y14) * c y11), Complex.normSq_nonneg (star (c y4) * c y0 + star (c y15) * c y11), Complex.normSq_nonneg (star (c y5) * c y0 + star (c y16) * c y11), Complex.normSq_nonneg (star (c y6) * c y0 + star (c y17) * c y11), Complex.normSq_nonneg (star (c y7) * c y0 + star (c y18) * c y11), Complex.normSq_nonneg (star (c y8) * c y0 + star (c y19) * c y11), Complex.normSq_nonneg (star (c y9) * c y0 + star (c y20) * c y11), Complex.normSq_nonneg (star (c y10) * c y0 + star (c y21) * c y11), Complex.normSq_nonneg (c y0 * d z14 - c y11 * d z4), Complex.normSq_nonneg (c y0 * d z16 - c y11 * d z6), Complex.normSq_nonneg (c y0 * d z17 - c y11 * d z7), Complex.normSq_nonneg (c y0 * d z18 - c y11 * d z8), Complex.normSq_nonneg (c y0 * d z19 - c y11 * d z9)])
  have ha2 : star (c y3) * c y0 + star (c y14) * c y11 = 0 :=
    Complex.normSq_eq_zero.mp (by linarith only [hz, Complex.normSq_nonneg (star (c y1) * c y0 + star (c y12) * c y11), Complex.normSq_nonneg (star (c y2) * c y0 + star (c y13) * c y11), Complex.normSq_nonneg (star (c y3) * c y0 + star (c y14) * c y11), Complex.normSq_nonneg (star (c y4) * c y0 + star (c y15) * c y11), Complex.normSq_nonneg (star (c y5) * c y0 + star (c y16) * c y11), Complex.normSq_nonneg (star (c y6) * c y0 + star (c y17) * c y11), Complex.normSq_nonneg (star (c y7) * c y0 + star (c y18) * c y11), Complex.normSq_nonneg (star (c y8) * c y0 + star (c y19) * c y11), Complex.normSq_nonneg (star (c y9) * c y0 + star (c y20) * c y11), Complex.normSq_nonneg (star (c y10) * c y0 + star (c y21) * c y11), Complex.normSq_nonneg (c y0 * d z14 - c y11 * d z4), Complex.normSq_nonneg (c y0 * d z16 - c y11 * d z6), Complex.normSq_nonneg (c y0 * d z17 - c y11 * d z7), Complex.normSq_nonneg (c y0 * d z18 - c y11 * d z8), Complex.normSq_nonneg (c y0 * d z19 - c y11 * d z9)])
  have ha3 : star (c y4) * c y0 + star (c y15) * c y11 = 0 :=
    Complex.normSq_eq_zero.mp (by linarith only [hz, Complex.normSq_nonneg (star (c y1) * c y0 + star (c y12) * c y11), Complex.normSq_nonneg (star (c y2) * c y0 + star (c y13) * c y11), Complex.normSq_nonneg (star (c y3) * c y0 + star (c y14) * c y11), Complex.normSq_nonneg (star (c y4) * c y0 + star (c y15) * c y11), Complex.normSq_nonneg (star (c y5) * c y0 + star (c y16) * c y11), Complex.normSq_nonneg (star (c y6) * c y0 + star (c y17) * c y11), Complex.normSq_nonneg (star (c y7) * c y0 + star (c y18) * c y11), Complex.normSq_nonneg (star (c y8) * c y0 + star (c y19) * c y11), Complex.normSq_nonneg (star (c y9) * c y0 + star (c y20) * c y11), Complex.normSq_nonneg (star (c y10) * c y0 + star (c y21) * c y11), Complex.normSq_nonneg (c y0 * d z14 - c y11 * d z4), Complex.normSq_nonneg (c y0 * d z16 - c y11 * d z6), Complex.normSq_nonneg (c y0 * d z17 - c y11 * d z7), Complex.normSq_nonneg (c y0 * d z18 - c y11 * d z8), Complex.normSq_nonneg (c y0 * d z19 - c y11 * d z9)])
  have ha4 : star (c y5) * c y0 + star (c y16) * c y11 = 0 :=
    Complex.normSq_eq_zero.mp (by linarith only [hz, Complex.normSq_nonneg (star (c y1) * c y0 + star (c y12) * c y11), Complex.normSq_nonneg (star (c y2) * c y0 + star (c y13) * c y11), Complex.normSq_nonneg (star (c y3) * c y0 + star (c y14) * c y11), Complex.normSq_nonneg (star (c y4) * c y0 + star (c y15) * c y11), Complex.normSq_nonneg (star (c y5) * c y0 + star (c y16) * c y11), Complex.normSq_nonneg (star (c y6) * c y0 + star (c y17) * c y11), Complex.normSq_nonneg (star (c y7) * c y0 + star (c y18) * c y11), Complex.normSq_nonneg (star (c y8) * c y0 + star (c y19) * c y11), Complex.normSq_nonneg (star (c y9) * c y0 + star (c y20) * c y11), Complex.normSq_nonneg (star (c y10) * c y0 + star (c y21) * c y11), Complex.normSq_nonneg (c y0 * d z14 - c y11 * d z4), Complex.normSq_nonneg (c y0 * d z16 - c y11 * d z6), Complex.normSq_nonneg (c y0 * d z17 - c y11 * d z7), Complex.normSq_nonneg (c y0 * d z18 - c y11 * d z8), Complex.normSq_nonneg (c y0 * d z19 - c y11 * d z9)])
  have ha5 : star (c y6) * c y0 + star (c y17) * c y11 = 0 :=
    Complex.normSq_eq_zero.mp (by linarith only [hz, Complex.normSq_nonneg (star (c y1) * c y0 + star (c y12) * c y11), Complex.normSq_nonneg (star (c y2) * c y0 + star (c y13) * c y11), Complex.normSq_nonneg (star (c y3) * c y0 + star (c y14) * c y11), Complex.normSq_nonneg (star (c y4) * c y0 + star (c y15) * c y11), Complex.normSq_nonneg (star (c y5) * c y0 + star (c y16) * c y11), Complex.normSq_nonneg (star (c y6) * c y0 + star (c y17) * c y11), Complex.normSq_nonneg (star (c y7) * c y0 + star (c y18) * c y11), Complex.normSq_nonneg (star (c y8) * c y0 + star (c y19) * c y11), Complex.normSq_nonneg (star (c y9) * c y0 + star (c y20) * c y11), Complex.normSq_nonneg (star (c y10) * c y0 + star (c y21) * c y11), Complex.normSq_nonneg (c y0 * d z14 - c y11 * d z4), Complex.normSq_nonneg (c y0 * d z16 - c y11 * d z6), Complex.normSq_nonneg (c y0 * d z17 - c y11 * d z7), Complex.normSq_nonneg (c y0 * d z18 - c y11 * d z8), Complex.normSq_nonneg (c y0 * d z19 - c y11 * d z9)])
  have ha6 : star (c y7) * c y0 + star (c y18) * c y11 = 0 :=
    Complex.normSq_eq_zero.mp (by linarith only [hz, Complex.normSq_nonneg (star (c y1) * c y0 + star (c y12) * c y11), Complex.normSq_nonneg (star (c y2) * c y0 + star (c y13) * c y11), Complex.normSq_nonneg (star (c y3) * c y0 + star (c y14) * c y11), Complex.normSq_nonneg (star (c y4) * c y0 + star (c y15) * c y11), Complex.normSq_nonneg (star (c y5) * c y0 + star (c y16) * c y11), Complex.normSq_nonneg (star (c y6) * c y0 + star (c y17) * c y11), Complex.normSq_nonneg (star (c y7) * c y0 + star (c y18) * c y11), Complex.normSq_nonneg (star (c y8) * c y0 + star (c y19) * c y11), Complex.normSq_nonneg (star (c y9) * c y0 + star (c y20) * c y11), Complex.normSq_nonneg (star (c y10) * c y0 + star (c y21) * c y11), Complex.normSq_nonneg (c y0 * d z14 - c y11 * d z4), Complex.normSq_nonneg (c y0 * d z16 - c y11 * d z6), Complex.normSq_nonneg (c y0 * d z17 - c y11 * d z7), Complex.normSq_nonneg (c y0 * d z18 - c y11 * d z8), Complex.normSq_nonneg (c y0 * d z19 - c y11 * d z9)])
  have ha7 : star (c y8) * c y0 + star (c y19) * c y11 = 0 :=
    Complex.normSq_eq_zero.mp (by linarith only [hz, Complex.normSq_nonneg (star (c y1) * c y0 + star (c y12) * c y11), Complex.normSq_nonneg (star (c y2) * c y0 + star (c y13) * c y11), Complex.normSq_nonneg (star (c y3) * c y0 + star (c y14) * c y11), Complex.normSq_nonneg (star (c y4) * c y0 + star (c y15) * c y11), Complex.normSq_nonneg (star (c y5) * c y0 + star (c y16) * c y11), Complex.normSq_nonneg (star (c y6) * c y0 + star (c y17) * c y11), Complex.normSq_nonneg (star (c y7) * c y0 + star (c y18) * c y11), Complex.normSq_nonneg (star (c y8) * c y0 + star (c y19) * c y11), Complex.normSq_nonneg (star (c y9) * c y0 + star (c y20) * c y11), Complex.normSq_nonneg (star (c y10) * c y0 + star (c y21) * c y11), Complex.normSq_nonneg (c y0 * d z14 - c y11 * d z4), Complex.normSq_nonneg (c y0 * d z16 - c y11 * d z6), Complex.normSq_nonneg (c y0 * d z17 - c y11 * d z7), Complex.normSq_nonneg (c y0 * d z18 - c y11 * d z8), Complex.normSq_nonneg (c y0 * d z19 - c y11 * d z9)])
  have ha8 : star (c y9) * c y0 + star (c y20) * c y11 = 0 :=
    Complex.normSq_eq_zero.mp (by linarith only [hz, Complex.normSq_nonneg (star (c y1) * c y0 + star (c y12) * c y11), Complex.normSq_nonneg (star (c y2) * c y0 + star (c y13) * c y11), Complex.normSq_nonneg (star (c y3) * c y0 + star (c y14) * c y11), Complex.normSq_nonneg (star (c y4) * c y0 + star (c y15) * c y11), Complex.normSq_nonneg (star (c y5) * c y0 + star (c y16) * c y11), Complex.normSq_nonneg (star (c y6) * c y0 + star (c y17) * c y11), Complex.normSq_nonneg (star (c y7) * c y0 + star (c y18) * c y11), Complex.normSq_nonneg (star (c y8) * c y0 + star (c y19) * c y11), Complex.normSq_nonneg (star (c y9) * c y0 + star (c y20) * c y11), Complex.normSq_nonneg (star (c y10) * c y0 + star (c y21) * c y11), Complex.normSq_nonneg (c y0 * d z14 - c y11 * d z4), Complex.normSq_nonneg (c y0 * d z16 - c y11 * d z6), Complex.normSq_nonneg (c y0 * d z17 - c y11 * d z7), Complex.normSq_nonneg (c y0 * d z18 - c y11 * d z8), Complex.normSq_nonneg (c y0 * d z19 - c y11 * d z9)])
  have ha9 : star (c y10) * c y0 + star (c y21) * c y11 = 0 :=
    Complex.normSq_eq_zero.mp (by linarith only [hz, Complex.normSq_nonneg (star (c y1) * c y0 + star (c y12) * c y11), Complex.normSq_nonneg (star (c y2) * c y0 + star (c y13) * c y11), Complex.normSq_nonneg (star (c y3) * c y0 + star (c y14) * c y11), Complex.normSq_nonneg (star (c y4) * c y0 + star (c y15) * c y11), Complex.normSq_nonneg (star (c y5) * c y0 + star (c y16) * c y11), Complex.normSq_nonneg (star (c y6) * c y0 + star (c y17) * c y11), Complex.normSq_nonneg (star (c y7) * c y0 + star (c y18) * c y11), Complex.normSq_nonneg (star (c y8) * c y0 + star (c y19) * c y11), Complex.normSq_nonneg (star (c y9) * c y0 + star (c y20) * c y11), Complex.normSq_nonneg (star (c y10) * c y0 + star (c y21) * c y11), Complex.normSq_nonneg (c y0 * d z14 - c y11 * d z4), Complex.normSq_nonneg (c y0 * d z16 - c y11 * d z6), Complex.normSq_nonneg (c y0 * d z17 - c y11 * d z7), Complex.normSq_nonneg (c y0 * d z18 - c y11 * d z8), Complex.normSq_nonneg (c y0 * d z19 - c y11 * d z9)])
  have hS : star (c y0) * c y0 + star (c y11) * c y11 = (1/3 : ℂ) := by
    have hc := congrArg (fun x : ℝ => (x : ℂ)) hR
    push_cast at hc
    simp only [← SixQubit.star_mul_self] at hc
    linear_combination hc
  have E1_00 : star (c y0) * d z5
      + star (c y1) * d z6
      + star (c y2) * d z7
      + star (c y3) * d z8
      + star (c y4) * d z9
      = 0 := by
    linear_combination (1/2 : ℂ) * ho0 + (1/2 : ℂ) * ho1
  have E1_10 : star (c y11) * d z5
      + star (c y12) * d z6
      + star (c y13) * d z7
      + star (c y14) * d z8
      + star (c y15) * d z9
      = 0 := by
    linear_combination (1/2 : ℂ) * ho2 + (1/2 : ℂ) * ho3
  have hb1_0 : d z5 = 0 := by
    linear_combination (3 * c y0) * E1_00 + (3 * c y11) * E1_10 - (3 * d z6) * ha0 - (3 * d z7) * ha1 - (3 * d z8) * ha2 - (3 * d z9) * ha3 - (3 * d z5) * hS
  have E1_01 : star (c y0) * d z15
      + star (c y1) * d z16
      + star (c y2) * d z17
      + star (c y3) * d z18
      + star (c y4) * d z19
      = 0 := by
    linear_combination (1/2 : ℂ) * ho2 + (-1/2 : ℂ) * ho3
  have E1_11 : star (c y11) * d z15
      + star (c y12) * d z16
      + star (c y13) * d z17
      + star (c y14) * d z18
      + star (c y15) * d z19
      = 0 := by
    linear_combination (1/2 : ℂ) * ho0 + (-1/2 : ℂ) * ho1
  have hb1_1 : d z15 = 0 := by
    linear_combination (3 * c y0) * E1_01 + (3 * c y11) * E1_11 - (3 * d z16) * ha0 - (3 * d z17) * ha1 - (3 * d z18) * ha2 - (3 * d z19) * ha3 - (3 * d z15) * hS
  have E2_00 : star (c y0) * d z3
      + star (c y1) * d z4
      + star (c y5) * d z7
      + star (c y6) * d z8
      + star (c y7) * d z9
      = 0 := by
    linear_combination (1/2 : ℂ) * ho8 + (1/2 : ℂ) * ho9
  have E2_10 : star (c y11) * d z3
      + star (c y12) * d z4
      + star (c y16) * d z7
      + star (c y17) * d z8
      + star (c y18) * d z9
      = 0 := by
    linear_combination (1/2 : ℂ) * ho10 + (1/2 : ℂ) * ho11
  have hb2_0 : d z3 = 0 := by
    linear_combination (3 * c y0) * E2_00 + (3 * c y11) * E2_10 - (3 * d z4) * ha0 - (3 * d z7) * ha4 - (3 * d z8) * ha5 - (3 * d z9) * ha6 - (3 * d z3) * hS
  have E2_01 : star (c y0) * d z13
      + star (c y1) * d z14
      + star (c y5) * d z17
      + star (c y6) * d z18
      + star (c y7) * d z19
      = 0 := by
    linear_combination (1/2 : ℂ) * ho10 + (-1/2 : ℂ) * ho11
  have E2_11 : star (c y11) * d z13
      + star (c y12) * d z14
      + star (c y16) * d z17
      + star (c y17) * d z18
      + star (c y18) * d z19
      = 0 := by
    linear_combination (1/2 : ℂ) * ho8 + (-1/2 : ℂ) * ho9
  have hb2_1 : d z13 = 0 := by
    linear_combination (3 * c y0) * E2_01 + (3 * c y11) * E2_11 - (3 * d z14) * ha0 - (3 * d z17) * ha4 - (3 * d z18) * ha5 - (3 * d z19) * ha6 - (3 * d z13) * hS
  have E3_00 : star (c y0) * d z2
      + star (c y2) * d z4
      + star (c y5) * d z6
      + star (c y8) * d z8
      + star (c y9) * d z9
      = 0 := by
    linear_combination (1/2 : ℂ) * ho16 + (1/2 : ℂ) * ho17
  have E3_10 : star (c y11) * d z2
      + star (c y13) * d z4
      + star (c y16) * d z6
      + star (c y19) * d z8
      + star (c y20) * d z9
      = 0 := by
    linear_combination (1/2 : ℂ) * ho18 + (1/2 : ℂ) * ho19
  have hb3_0 : d z2 = 0 := by
    linear_combination (3 * c y0) * E3_00 + (3 * c y11) * E3_10 - (3 * d z4) * ha1 - (3 * d z6) * ha4 - (3 * d z8) * ha7 - (3 * d z9) * ha8 - (3 * d z2) * hS
  have E3_01 : star (c y0) * d z12
      + star (c y2) * d z14
      + star (c y5) * d z16
      + star (c y8) * d z18
      + star (c y9) * d z19
      = 0 := by
    linear_combination (1/2 : ℂ) * ho18 + (-1/2 : ℂ) * ho19
  have E3_11 : star (c y11) * d z12
      + star (c y13) * d z14
      + star (c y16) * d z16
      + star (c y19) * d z18
      + star (c y20) * d z19
      = 0 := by
    linear_combination (1/2 : ℂ) * ho16 + (-1/2 : ℂ) * ho17
  have hb3_1 : d z12 = 0 := by
    linear_combination (3 * c y0) * E3_01 + (3 * c y11) * E3_11 - (3 * d z14) * ha1 - (3 * d z16) * ha4 - (3 * d z18) * ha7 - (3 * d z19) * ha8 - (3 * d z12) * hS
  have E4_00 : star (c y0) * d z1
      + star (c y3) * d z4
      + star (c y6) * d z6
      + star (c y8) * d z7
      + star (c y10) * d z9
      = 0 := by
    linear_combination (1/2 : ℂ) * ho24 + (1/2 : ℂ) * ho25
  have E4_10 : star (c y11) * d z1
      + star (c y14) * d z4
      + star (c y17) * d z6
      + star (c y19) * d z7
      + star (c y21) * d z9
      = 0 := by
    linear_combination (1/2 : ℂ) * ho26 + (1/2 : ℂ) * ho27
  have hb4_0 : d z1 = 0 := by
    linear_combination (3 * c y0) * E4_00 + (3 * c y11) * E4_10 - (3 * d z4) * ha2 - (3 * d z6) * ha5 - (3 * d z7) * ha7 - (3 * d z9) * ha9 - (3 * d z1) * hS
  have E4_01 : star (c y0) * d z11
      + star (c y3) * d z14
      + star (c y6) * d z16
      + star (c y8) * d z17
      + star (c y10) * d z19
      = 0 := by
    linear_combination (1/2 : ℂ) * ho26 + (-1/2 : ℂ) * ho27
  have E4_11 : star (c y11) * d z11
      + star (c y14) * d z14
      + star (c y17) * d z16
      + star (c y19) * d z17
      + star (c y21) * d z19
      = 0 := by
    linear_combination (1/2 : ℂ) * ho24 + (-1/2 : ℂ) * ho25
  have hb4_1 : d z11 = 0 := by
    linear_combination (3 * c y0) * E4_01 + (3 * c y11) * E4_11 - (3 * d z14) * ha2 - (3 * d z16) * ha5 - (3 * d z17) * ha7 - (3 * d z19) * ha9 - (3 * d z11) * hS
  have E5_00 : star (c y0) * d z0
      + star (c y4) * d z4
      + star (c y7) * d z6
      + star (c y9) * d z7
      + star (c y10) * d z8
      = 0 := by
    linear_combination (1/2 : ℂ) * ho32 + (1/2 : ℂ) * ho33
  have E5_10 : star (c y11) * d z0
      + star (c y15) * d z4
      + star (c y18) * d z6
      + star (c y20) * d z7
      + star (c y21) * d z8
      = 0 := by
    linear_combination (1/2 : ℂ) * ho34 + (1/2 : ℂ) * ho35
  have hb5_0 : d z0 = 0 := by
    linear_combination (3 * c y0) * E5_00 + (3 * c y11) * E5_10 - (3 * d z4) * ha3 - (3 * d z6) * ha6 - (3 * d z7) * ha8 - (3 * d z8) * ha9 - (3 * d z0) * hS
  have E5_01 : star (c y0) * d z10
      + star (c y4) * d z14
      + star (c y7) * d z16
      + star (c y9) * d z17
      + star (c y10) * d z18
      = 0 := by
    linear_combination (1/2 : ℂ) * ho34 + (-1/2 : ℂ) * ho35
  have E5_11 : star (c y11) * d z10
      + star (c y15) * d z14
      + star (c y18) * d z16
      + star (c y20) * d z17
      + star (c y21) * d z18
      = 0 := by
    linear_combination (1/2 : ℂ) * ho32 + (-1/2 : ℂ) * ho33
  have hb5_1 : d z10 = 0 := by
    linear_combination (3 * c y0) * E5_01 + (3 * c y11) * E5_11 - (3 * d z14) * ha3 - (3 * d z16) * ha6 - (3 * d z17) * ha8 - (3 * d z18) * ha9 - (3 * d z10) * hS
  have nb1_0 : Complex.normSq (d z5) = 0 := by rw [hb1_0]; simp
  have nb1_1 : Complex.normSq (d z15) = 0 := by rw [hb1_1]; simp
  have nb2_0 : Complex.normSq (d z3) = 0 := by rw [hb2_0]; simp
  have nb2_1 : Complex.normSq (d z13) = 0 := by rw [hb2_1]; simp
  have nb3_0 : Complex.normSq (d z2) = 0 := by rw [hb3_0]; simp
  have nb3_1 : Complex.normSq (d z12) = 0 := by rw [hb3_1]; simp
  have nb4_0 : Complex.normSq (d z1) = 0 := by rw [hb4_0]; simp
  have nb4_1 : Complex.normSq (d z11) = 0 := by rw [hb4_1]; simp
  have nb5_0 : Complex.normSq (d z0) = 0 := by rw [hb5_0]; simp
  have nb5_1 : Complex.normSq (d z10) = 0 := by rw [hb5_1]; simp
  linarith only [hB, nb1_0, nb1_1, nb2_0, nb2_1, nb3_0, nb3_1, nb4_0, nb4_1, nb5_0, nb5_1]

end

end SixQubit.Orbit6
