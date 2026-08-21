import Mathlib

import SS.FullKL
import SixQubit.Common
import SixQubit.Trace5
import SixQubit.Flip5

set_option maxHeartbeats 2000000

/-!
# Six-qubit moment orbit 5: the free-pair frame reduction

Orbit 5 of `six_qubit_sslp.tex`: q = 3, angle vector a = (0, 0, 1, 1, 1, 1),
residues 0 and 1.  Qubits 0 and 1 carry angle zero, so the amplitudes group
into vectors of `ℂ⁴`.  Writing `V = {1,2,3,4}` for the four active
coordinates, the active tails of the two fibers are

```
T0 = {0000, 0111, 1011, 1101, 1110},   T1 = {1000, 0100, 0010, 0001, 1111},
```

so a candidate pair is

```
|0_L> = u (x) 0000 + Σᵢ aᵢ (x) ê_i ,   |1_L> = Σᵢ bᵢ (x) e_i + v (x) 1111 .
```

This module certifies, from the moment polytope and from the weight-at-most-two
Knill--Laflamme rows only:

* the ten squared norms `‖u‖² = ‖v‖² = 1/3`, `‖aᵢ‖² = ‖bᵢ‖² = 1/6`;
* the anchor orthogonalities `u† bᵢ = 0` and `aᵢ† v = 0`;
* the two-flip relations `aᵢ† bⱼ + aⱼ† bᵢ = 0` for `i ≠ j`;
* equality of the two reduced density matrices on the free pair;

and then, via `SixQubit.Trace5.cs_tight`, the *frame reduction*

```
u† aᵢ = 0   (1 ≤ i ≤ 4)   and   Σᵢ aᵢ aᵢ† = Σᵢ bᵢ bᵢ† .
```

Finally the *dressed* one-flip rows -- the weight-two errors `Z_A Xᵢ`, `X_A Xᵢ`
and `Y_A Xᵢ` for either zero-angle qubit `A` -- feed the two-qubit flip-kernel
dichotomy `SixQubit.Flip5.core`, which closes the orbit: either the Bell branch,
where the twelve cross orthogonalities `aᵢ† bⱼ = 0` reach
`SixQubit.Trace5.bell_contradiction`, or the line branch, where all ten vectors
collapse onto one line of `u^⊥` and the two-flip relations become the odd
triangle of `SixQubit.Triangle`.  The headline is `no_go_of_moments`.

Everything combinatorial is decided by the Lean kernel; `native_decide` is not
used.
-/

namespace SixQubit.Orbit5

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

/-! ## The two fibers -/

def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]

def y0 : SS.BitString 6 := bs false false false false false false  -- 000000
def y1 : SS.BitString 6 := bs false true  false false false false  -- 010000
def y2 : SS.BitString 6 := bs true  false false false false false  -- 100000
def y3 : SS.BitString 6 := bs true  true  false false false false  -- 110000
def y4 : SS.BitString 6 := bs false false false true  true  true  -- 000111
def y5 : SS.BitString 6 := bs false true  false true  true  true  -- 010111
def y6 : SS.BitString 6 := bs true  false false true  true  true  -- 100111
def y7 : SS.BitString 6 := bs true  true  false true  true  true  -- 110111
def y8 : SS.BitString 6 := bs false false true  false true  true  -- 001011
def y9 : SS.BitString 6 := bs false true  true  false true  true  -- 011011
def y10 : SS.BitString 6 := bs true  false true  false true  true  -- 101011
def y11 : SS.BitString 6 := bs true  true  true  false true  true  -- 111011
def y12 : SS.BitString 6 := bs false false true  true  false true  -- 001101
def y13 : SS.BitString 6 := bs false true  true  true  false true  -- 011101
def y14 : SS.BitString 6 := bs true  false true  true  false true  -- 101101
def y15 : SS.BitString 6 := bs true  true  true  true  false true  -- 111101
def y16 : SS.BitString 6 := bs false false true  true  true  false  -- 001110
def y17 : SS.BitString 6 := bs false true  true  true  true  false  -- 011110
def y18 : SS.BitString 6 := bs true  false true  true  true  false  -- 101110
def y19 : SS.BitString 6 := bs true  true  true  true  true  false  -- 111110

def z0 : SS.BitString 6 := bs false false true  false false false  -- 001000
def z1 : SS.BitString 6 := bs false true  true  false false false  -- 011000
def z2 : SS.BitString 6 := bs true  false true  false false false  -- 101000
def z3 : SS.BitString 6 := bs true  true  true  false false false  -- 111000
def z4 : SS.BitString 6 := bs false false false true  false false  -- 000100
def z5 : SS.BitString 6 := bs false true  false true  false false  -- 010100
def z6 : SS.BitString 6 := bs true  false false true  false false  -- 100100
def z7 : SS.BitString 6 := bs true  true  false true  false false  -- 110100
def z8 : SS.BitString 6 := bs false false false false true  false  -- 000010
def z9 : SS.BitString 6 := bs false true  false false true  false  -- 010010
def z10 : SS.BitString 6 := bs true  false false false true  false  -- 100010
def z11 : SS.BitString 6 := bs true  true  false false true  false  -- 110010
def z12 : SS.BitString 6 := bs false false false false false true  -- 000001
def z13 : SS.BitString 6 := bs false true  false false false true  -- 010001
def z14 : SS.BitString 6 := bs true  false false false false true  -- 100001
def z15 : SS.BitString 6 := bs true  true  false false false true  -- 110001
def z16 : SS.BitString 6 := bs false false true  true  true  true  -- 001111
def z17 : SS.BitString 6 := bs false true  true  true  true  true  -- 011111
def z18 : SS.BitString 6 := bs true  false true  true  true  true  -- 101111
def z19 : SS.BitString 6 := bs true  true  true  true  true  true  -- 111111

def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19}
def S1 : Finset (SS.BitString 6) := {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19}

def av : Fin 6 -> ZMod 3 := ![0, 0, 1, 1, 1, 1]

theorem S0_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 0) = S0 := by
  decide

theorem S1_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 1) = S1 := by
  decide

/-! ## Flip masks and dressings -/

def f1 : SS.BitString 6 := bs false false true  false false false  -- 001000
def f2 : SS.BitString 6 := bs false false false true  false false  -- 000100
def f3 : SS.BitString 6 := bs false false false false true  false  -- 000010
def f4 : SS.BitString 6 := bs false false false false false true  -- 000001
def g12 : SS.BitString 6 := bs false false false false true  true  -- 000011
def g13 : SS.BitString 6 := bs false false false true  false true  -- 000101
def g14 : SS.BitString 6 := bs false false false true  true  false  -- 000110
def g23 : SS.BitString 6 := bs false false true  false false true  -- 001001
def g24 : SS.BitString 6 := bs false false true  false true  false  -- 001010
def g34 : SS.BitString 6 := bs false false true  true  false false  -- 001100
def p1 : SS.BitString 6 := bs true  false false false false false  -- 100000
def p2 : SS.BitString 6 := bs false true  false false false false  -- 010000
def p3 : SS.BitString 6 := bs true  true  false false false false  -- 110000
def w0 : SS.BitString 6 := bs false false false false false false  -- 000000
def w1 : SS.BitString 6 := bs true  false false false false false  -- 100000
def w2 : SS.BitString 6 := bs false true  false false false false  -- 010000
def w3 : SS.BitString 6 := bs true  true  false false false false  -- 110000

/-! ## The off-diagonal layer -/

def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),
      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

theorem inc_f1 :
    S1.filter (fun y => SS.bxor y f1 ∈ S0) = {z0, z1, z2, z3, z16, z17, z18, z19} := by decide
theorem flip_f1_0 : SS.bxor z0 f1 = y0 := by decide
theorem flip_f1_1 : SS.bxor z1 f1 = y1 := by decide
theorem flip_f1_2 : SS.bxor z2 f1 = y2 := by decide
theorem flip_f1_3 : SS.bxor z3 f1 = y3 := by decide
theorem flip_f1_16 : SS.bxor z16 f1 = y4 := by decide
theorem flip_f1_17 : SS.bxor z17 f1 = y5 := by decide
theorem flip_f1_18 : SS.bxor z18 f1 = y6 := by decide
theorem flip_f1_19 : SS.bxor z19 f1 = y7 := by decide
theorem inc_f2 :
    S1.filter (fun y => SS.bxor y f2 ∈ S0) = {z4, z5, z6, z7, z16, z17, z18, z19} := by decide
theorem flip_f2_4 : SS.bxor z4 f2 = y0 := by decide
theorem flip_f2_5 : SS.bxor z5 f2 = y1 := by decide
theorem flip_f2_6 : SS.bxor z6 f2 = y2 := by decide
theorem flip_f2_7 : SS.bxor z7 f2 = y3 := by decide
theorem flip_f2_16 : SS.bxor z16 f2 = y8 := by decide
theorem flip_f2_17 : SS.bxor z17 f2 = y9 := by decide
theorem flip_f2_18 : SS.bxor z18 f2 = y10 := by decide
theorem flip_f2_19 : SS.bxor z19 f2 = y11 := by decide
theorem inc_f3 :
    S1.filter (fun y => SS.bxor y f3 ∈ S0) = {z8, z9, z10, z11, z16, z17, z18, z19} := by decide
theorem flip_f3_8 : SS.bxor z8 f3 = y0 := by decide
theorem flip_f3_9 : SS.bxor z9 f3 = y1 := by decide
theorem flip_f3_10 : SS.bxor z10 f3 = y2 := by decide
theorem flip_f3_11 : SS.bxor z11 f3 = y3 := by decide
theorem flip_f3_16 : SS.bxor z16 f3 = y12 := by decide
theorem flip_f3_17 : SS.bxor z17 f3 = y13 := by decide
theorem flip_f3_18 : SS.bxor z18 f3 = y14 := by decide
theorem flip_f3_19 : SS.bxor z19 f3 = y15 := by decide
theorem inc_f4 :
    S1.filter (fun y => SS.bxor y f4 ∈ S0) = {z12, z13, z14, z15, z16, z17, z18, z19} := by decide
theorem flip_f4_12 : SS.bxor z12 f4 = y0 := by decide
theorem flip_f4_13 : SS.bxor z13 f4 = y1 := by decide
theorem flip_f4_14 : SS.bxor z14 f4 = y2 := by decide
theorem flip_f4_15 : SS.bxor z15 f4 = y3 := by decide
theorem flip_f4_16 : SS.bxor z16 f4 = y16 := by decide
theorem flip_f4_17 : SS.bxor z17 f4 = y17 := by decide
theorem flip_f4_18 : SS.bxor z18 f4 = y18 := by decide
theorem flip_f4_19 : SS.bxor z19 f4 = y19 := by decide
theorem inc_g12 :
    S1.filter (fun y => SS.bxor y g12 ∈ S0) = {z0, z1, z2, z3, z4, z5, z6, z7} := by decide
theorem flip_g12_0 : SS.bxor z0 g12 = y8 := by decide
theorem flip_g12_1 : SS.bxor z1 g12 = y9 := by decide
theorem flip_g12_2 : SS.bxor z2 g12 = y10 := by decide
theorem flip_g12_3 : SS.bxor z3 g12 = y11 := by decide
theorem flip_g12_4 : SS.bxor z4 g12 = y4 := by decide
theorem flip_g12_5 : SS.bxor z5 g12 = y5 := by decide
theorem flip_g12_6 : SS.bxor z6 g12 = y6 := by decide
theorem flip_g12_7 : SS.bxor z7 g12 = y7 := by decide
theorem inc_g13 :
    S1.filter (fun y => SS.bxor y g13 ∈ S0) = {z0, z1, z2, z3, z8, z9, z10, z11} := by decide
theorem flip_g13_0 : SS.bxor z0 g13 = y12 := by decide
theorem flip_g13_1 : SS.bxor z1 g13 = y13 := by decide
theorem flip_g13_2 : SS.bxor z2 g13 = y14 := by decide
theorem flip_g13_3 : SS.bxor z3 g13 = y15 := by decide
theorem flip_g13_8 : SS.bxor z8 g13 = y4 := by decide
theorem flip_g13_9 : SS.bxor z9 g13 = y5 := by decide
theorem flip_g13_10 : SS.bxor z10 g13 = y6 := by decide
theorem flip_g13_11 : SS.bxor z11 g13 = y7 := by decide
theorem inc_g14 :
    S1.filter (fun y => SS.bxor y g14 ∈ S0) = {z0, z1, z2, z3, z12, z13, z14, z15} := by decide
theorem flip_g14_0 : SS.bxor z0 g14 = y16 := by decide
theorem flip_g14_1 : SS.bxor z1 g14 = y17 := by decide
theorem flip_g14_2 : SS.bxor z2 g14 = y18 := by decide
theorem flip_g14_3 : SS.bxor z3 g14 = y19 := by decide
theorem flip_g14_12 : SS.bxor z12 g14 = y4 := by decide
theorem flip_g14_13 : SS.bxor z13 g14 = y5 := by decide
theorem flip_g14_14 : SS.bxor z14 g14 = y6 := by decide
theorem flip_g14_15 : SS.bxor z15 g14 = y7 := by decide
theorem inc_g23 :
    S1.filter (fun y => SS.bxor y g23 ∈ S0) = {z4, z5, z6, z7, z8, z9, z10, z11} := by decide
theorem flip_g23_4 : SS.bxor z4 g23 = y12 := by decide
theorem flip_g23_5 : SS.bxor z5 g23 = y13 := by decide
theorem flip_g23_6 : SS.bxor z6 g23 = y14 := by decide
theorem flip_g23_7 : SS.bxor z7 g23 = y15 := by decide
theorem flip_g23_8 : SS.bxor z8 g23 = y8 := by decide
theorem flip_g23_9 : SS.bxor z9 g23 = y9 := by decide
theorem flip_g23_10 : SS.bxor z10 g23 = y10 := by decide
theorem flip_g23_11 : SS.bxor z11 g23 = y11 := by decide
theorem inc_g24 :
    S1.filter (fun y => SS.bxor y g24 ∈ S0) = {z4, z5, z6, z7, z12, z13, z14, z15} := by decide
theorem flip_g24_4 : SS.bxor z4 g24 = y16 := by decide
theorem flip_g24_5 : SS.bxor z5 g24 = y17 := by decide
theorem flip_g24_6 : SS.bxor z6 g24 = y18 := by decide
theorem flip_g24_7 : SS.bxor z7 g24 = y19 := by decide
theorem flip_g24_12 : SS.bxor z12 g24 = y8 := by decide
theorem flip_g24_13 : SS.bxor z13 g24 = y9 := by decide
theorem flip_g24_14 : SS.bxor z14 g24 = y10 := by decide
theorem flip_g24_15 : SS.bxor z15 g24 = y11 := by decide
theorem inc_g34 :
    S1.filter (fun y => SS.bxor y g34 ∈ S0) = {z8, z9, z10, z11, z12, z13, z14, z15} := by decide
theorem flip_g34_8 : SS.bxor z8 g34 = y16 := by decide
theorem flip_g34_9 : SS.bxor z9 g34 = y17 := by decide
theorem flip_g34_10 : SS.bxor z10 g34 = y18 := by decide
theorem flip_g34_11 : SS.bxor z11 g34 = y19 := by decide
theorem flip_g34_12 : SS.bxor z12 g34 = y12 := by decide
theorem flip_g34_13 : SS.bxor z13 g34 = y13 := by decide
theorem flip_g34_14 : SS.bxor z14 g34 = y14 := by decide
theorem flip_g34_15 : SS.bxor z15 g34 = y15 := by decide

theorem sg_f1_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg_f1_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg_f1_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg_f1_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg_f1_w0_16 : SS.bdot w0 z16 = false := by decide
theorem sg_f1_w0_17 : SS.bdot w0 z17 = false := by decide
theorem sg_f1_w0_18 : SS.bdot w0 z18 = false := by decide
theorem sg_f1_w0_19 : SS.bdot w0 z19 = false := by decide
theorem ex_f1_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d f1 w0 = star (c y0) * d z0 + star (c y1) * d z1 + star (c y2) * d z2 + star (c y3) * d z3
      + star (c y4) * d z16 + star (c y5) * d z17 + star (c y6) * d z18 + star (c y7) * d z19 := by
  unfold offSum
  rw [inc_f1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_f1_0, flip_f1_1, flip_f1_2, flip_f1_3, flip_f1_16, flip_f1_17, flip_f1_18, flip_f1_19]
  simp only [sg_f1_w0_0, sg_f1_w0_1, sg_f1_w0_2, sg_f1_w0_3, sg_f1_w0_16, sg_f1_w0_17, sg_f1_w0_18, sg_f1_w0_19, SixQubit.signMul_false]
  try ring
theorem sg_f1_f2_0 : SS.bdot f2 z0 = false := by decide
theorem sg_f1_f2_1 : SS.bdot f2 z1 = false := by decide
theorem sg_f1_f2_2 : SS.bdot f2 z2 = false := by decide
theorem sg_f1_f2_3 : SS.bdot f2 z3 = false := by decide
theorem sg_f1_f2_16 : SS.bdot f2 z16 = true := by decide
theorem sg_f1_f2_17 : SS.bdot f2 z17 = true := by decide
theorem sg_f1_f2_18 : SS.bdot f2 z18 = true := by decide
theorem sg_f1_f2_19 : SS.bdot f2 z19 = true := by decide
theorem ex_f1_f2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d f1 f2 = star (c y0) * d z0 + star (c y1) * d z1 + star (c y2) * d z2
      + star (c y3) * d z3 - star (c y4) * d z16 - star (c y5) * d z17 - star (c y6) * d z18 - star (c y7) * d z19 := by
  unfold offSum
  rw [inc_f1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_f1_0, flip_f1_1, flip_f1_2, flip_f1_3, flip_f1_16, flip_f1_17, flip_f1_18, flip_f1_19]
  simp only [sg_f1_f2_0, sg_f1_f2_1, sg_f1_f2_2, sg_f1_f2_3, sg_f1_f2_16, sg_f1_f2_17, sg_f1_f2_18, sg_f1_f2_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_f2_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg_f2_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg_f2_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg_f2_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg_f2_w0_16 : SS.bdot w0 z16 = false := by decide
theorem sg_f2_w0_17 : SS.bdot w0 z17 = false := by decide
theorem sg_f2_w0_18 : SS.bdot w0 z18 = false := by decide
theorem sg_f2_w0_19 : SS.bdot w0 z19 = false := by decide
theorem ex_f2_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d f2 w0 = star (c y0) * d z4 + star (c y1) * d z5 + star (c y2) * d z6 + star (c y3) * d z7
      + star (c y8) * d z16 + star (c y9) * d z17 + star (c y10) * d z18 + star (c y11) * d z19 := by
  unfold offSum
  rw [inc_f2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_f2_4, flip_f2_5, flip_f2_6, flip_f2_7, flip_f2_16, flip_f2_17, flip_f2_18, flip_f2_19]
  simp only [sg_f2_w0_4, sg_f2_w0_5, sg_f2_w0_6, sg_f2_w0_7, sg_f2_w0_16, sg_f2_w0_17, sg_f2_w0_18, sg_f2_w0_19, SixQubit.signMul_false]
  try ring
theorem sg_f2_f3_4 : SS.bdot f3 z4 = false := by decide
theorem sg_f2_f3_5 : SS.bdot f3 z5 = false := by decide
theorem sg_f2_f3_6 : SS.bdot f3 z6 = false := by decide
theorem sg_f2_f3_7 : SS.bdot f3 z7 = false := by decide
theorem sg_f2_f3_16 : SS.bdot f3 z16 = true := by decide
theorem sg_f2_f3_17 : SS.bdot f3 z17 = true := by decide
theorem sg_f2_f3_18 : SS.bdot f3 z18 = true := by decide
theorem sg_f2_f3_19 : SS.bdot f3 z19 = true := by decide
theorem ex_f2_f3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d f2 f3 = star (c y0) * d z4 + star (c y1) * d z5 + star (c y2) * d z6
      + star (c y3) * d z7 - star (c y8) * d z16 - star (c y9) * d z17 - star (c y10) * d z18 - star (c y11) * d z19 := by
  unfold offSum
  rw [inc_f2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_f2_4, flip_f2_5, flip_f2_6, flip_f2_7, flip_f2_16, flip_f2_17, flip_f2_18, flip_f2_19]
  simp only [sg_f2_f3_4, sg_f2_f3_5, sg_f2_f3_6, sg_f2_f3_7, sg_f2_f3_16, sg_f2_f3_17, sg_f2_f3_18, sg_f2_f3_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_f3_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_f3_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg_f3_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg_f3_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg_f3_w0_16 : SS.bdot w0 z16 = false := by decide
theorem sg_f3_w0_17 : SS.bdot w0 z17 = false := by decide
theorem sg_f3_w0_18 : SS.bdot w0 z18 = false := by decide
theorem sg_f3_w0_19 : SS.bdot w0 z19 = false := by decide
theorem ex_f3_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d f3 w0 = star (c y0) * d z8 + star (c y1) * d z9 + star (c y2) * d z10
      + star (c y3) * d z11 + star (c y12) * d z16 + star (c y13) * d z17 + star (c y14) * d z18
      + star (c y15) * d z19 := by
  unfold offSum
  rw [inc_f3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_f3_8, flip_f3_9, flip_f3_10, flip_f3_11, flip_f3_16, flip_f3_17, flip_f3_18, flip_f3_19]
  simp only [sg_f3_w0_8, sg_f3_w0_9, sg_f3_w0_10, sg_f3_w0_11, sg_f3_w0_16, sg_f3_w0_17, sg_f3_w0_18, sg_f3_w0_19, SixQubit.signMul_false]
  try ring
theorem sg_f3_f4_8 : SS.bdot f4 z8 = false := by decide
theorem sg_f3_f4_9 : SS.bdot f4 z9 = false := by decide
theorem sg_f3_f4_10 : SS.bdot f4 z10 = false := by decide
theorem sg_f3_f4_11 : SS.bdot f4 z11 = false := by decide
theorem sg_f3_f4_16 : SS.bdot f4 z16 = true := by decide
theorem sg_f3_f4_17 : SS.bdot f4 z17 = true := by decide
theorem sg_f3_f4_18 : SS.bdot f4 z18 = true := by decide
theorem sg_f3_f4_19 : SS.bdot f4 z19 = true := by decide
theorem ex_f3_f4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d f3 f4 = star (c y0) * d z8 + star (c y1) * d z9 + star (c y2) * d z10
      + star (c y3) * d z11 - star (c y12) * d z16 - star (c y13) * d z17 - star (c y14) * d z18 - star (c y15) * d z19 := by
  unfold offSum
  rw [inc_f3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_f3_8, flip_f3_9, flip_f3_10, flip_f3_11, flip_f3_16, flip_f3_17, flip_f3_18, flip_f3_19]
  simp only [sg_f3_f4_8, sg_f3_f4_9, sg_f3_f4_10, sg_f3_f4_11, sg_f3_f4_16, sg_f3_f4_17, sg_f3_f4_18, sg_f3_f4_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_f4_w0_12 : SS.bdot w0 z12 = false := by decide
theorem sg_f4_w0_13 : SS.bdot w0 z13 = false := by decide
theorem sg_f4_w0_14 : SS.bdot w0 z14 = false := by decide
theorem sg_f4_w0_15 : SS.bdot w0 z15 = false := by decide
theorem sg_f4_w0_16 : SS.bdot w0 z16 = false := by decide
theorem sg_f4_w0_17 : SS.bdot w0 z17 = false := by decide
theorem sg_f4_w0_18 : SS.bdot w0 z18 = false := by decide
theorem sg_f4_w0_19 : SS.bdot w0 z19 = false := by decide
theorem ex_f4_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d f4 w0 = star (c y0) * d z12 + star (c y1) * d z13 + star (c y2) * d z14
      + star (c y3) * d z15 + star (c y16) * d z16 + star (c y17) * d z17 + star (c y18) * d z18
      + star (c y19) * d z19 := by
  unfold offSum
  rw [inc_f4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_f4_12, flip_f4_13, flip_f4_14, flip_f4_15, flip_f4_16, flip_f4_17, flip_f4_18, flip_f4_19]
  simp only [sg_f4_w0_12, sg_f4_w0_13, sg_f4_w0_14, sg_f4_w0_15, sg_f4_w0_16, sg_f4_w0_17, sg_f4_w0_18, sg_f4_w0_19, SixQubit.signMul_false]
  try ring
theorem sg_f4_f1_12 : SS.bdot f1 z12 = false := by decide
theorem sg_f4_f1_13 : SS.bdot f1 z13 = false := by decide
theorem sg_f4_f1_14 : SS.bdot f1 z14 = false := by decide
theorem sg_f4_f1_15 : SS.bdot f1 z15 = false := by decide
theorem sg_f4_f1_16 : SS.bdot f1 z16 = true := by decide
theorem sg_f4_f1_17 : SS.bdot f1 z17 = true := by decide
theorem sg_f4_f1_18 : SS.bdot f1 z18 = true := by decide
theorem sg_f4_f1_19 : SS.bdot f1 z19 = true := by decide
theorem ex_f4_f1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d f4 f1 = star (c y0) * d z12 + star (c y1) * d z13 + star (c y2) * d z14
      + star (c y3) * d z15 - star (c y16) * d z16 - star (c y17) * d z17 - star (c y18) * d z18 - star (c y19) * d z19 := by
  unfold offSum
  rw [inc_f4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_f4_12, flip_f4_13, flip_f4_14, flip_f4_15, flip_f4_16, flip_f4_17, flip_f4_18, flip_f4_19]
  simp only [sg_f4_f1_12, sg_f4_f1_13, sg_f4_f1_14, sg_f4_f1_15, sg_f4_f1_16, sg_f4_f1_17, sg_f4_f1_18, sg_f4_f1_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_g12_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg_g12_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg_g12_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg_g12_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg_g12_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg_g12_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg_g12_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg_g12_w0_7 : SS.bdot w0 z7 = false := by decide
theorem ex_g12_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d g12 w0 = star (c y8) * d z0 + star (c y9) * d z1 + star (c y10) * d z2
      + star (c y11) * d z3 + star (c y4) * d z4 + star (c y5) * d z5 + star (c y6) * d z6
      + star (c y7) * d z7 := by
  unfold offSum
  rw [inc_g12]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_g12_0, flip_g12_1, flip_g12_2, flip_g12_3, flip_g12_4, flip_g12_5, flip_g12_6, flip_g12_7]
  simp only [sg_g12_w0_0, sg_g12_w0_1, sg_g12_w0_2, sg_g12_w0_3, sg_g12_w0_4, sg_g12_w0_5, sg_g12_w0_6, sg_g12_w0_7, SixQubit.signMul_false]
  try ring
theorem sg_g13_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg_g13_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg_g13_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg_g13_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg_g13_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_g13_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg_g13_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg_g13_w0_11 : SS.bdot w0 z11 = false := by decide
theorem ex_g13_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d g13 w0 = star (c y12) * d z0 + star (c y13) * d z1 + star (c y14) * d z2
      + star (c y15) * d z3 + star (c y4) * d z8 + star (c y5) * d z9 + star (c y6) * d z10
      + star (c y7) * d z11 := by
  unfold offSum
  rw [inc_g13]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_g13_0, flip_g13_1, flip_g13_2, flip_g13_3, flip_g13_8, flip_g13_9, flip_g13_10, flip_g13_11]
  simp only [sg_g13_w0_0, sg_g13_w0_1, sg_g13_w0_2, sg_g13_w0_3, sg_g13_w0_8, sg_g13_w0_9, sg_g13_w0_10, sg_g13_w0_11, SixQubit.signMul_false]
  try ring
theorem sg_g14_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg_g14_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg_g14_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg_g14_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg_g14_w0_12 : SS.bdot w0 z12 = false := by decide
theorem sg_g14_w0_13 : SS.bdot w0 z13 = false := by decide
theorem sg_g14_w0_14 : SS.bdot w0 z14 = false := by decide
theorem sg_g14_w0_15 : SS.bdot w0 z15 = false := by decide
theorem ex_g14_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d g14 w0 = star (c y16) * d z0 + star (c y17) * d z1 + star (c y18) * d z2
      + star (c y19) * d z3 + star (c y4) * d z12 + star (c y5) * d z13 + star (c y6) * d z14
      + star (c y7) * d z15 := by
  unfold offSum
  rw [inc_g14]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_g14_0, flip_g14_1, flip_g14_2, flip_g14_3, flip_g14_12, flip_g14_13, flip_g14_14, flip_g14_15]
  simp only [sg_g14_w0_0, sg_g14_w0_1, sg_g14_w0_2, sg_g14_w0_3, sg_g14_w0_12, sg_g14_w0_13, sg_g14_w0_14, sg_g14_w0_15, SixQubit.signMul_false]
  try ring
theorem sg_g23_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg_g23_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg_g23_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg_g23_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg_g23_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_g23_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg_g23_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg_g23_w0_11 : SS.bdot w0 z11 = false := by decide
theorem ex_g23_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d g23 w0 = star (c y12) * d z4 + star (c y13) * d z5 + star (c y14) * d z6
      + star (c y15) * d z7 + star (c y8) * d z8 + star (c y9) * d z9 + star (c y10) * d z10
      + star (c y11) * d z11 := by
  unfold offSum
  rw [inc_g23]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_g23_4, flip_g23_5, flip_g23_6, flip_g23_7, flip_g23_8, flip_g23_9, flip_g23_10, flip_g23_11]
  simp only [sg_g23_w0_4, sg_g23_w0_5, sg_g23_w0_6, sg_g23_w0_7, sg_g23_w0_8, sg_g23_w0_9, sg_g23_w0_10, sg_g23_w0_11, SixQubit.signMul_false]
  try ring
theorem sg_g24_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg_g24_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg_g24_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg_g24_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg_g24_w0_12 : SS.bdot w0 z12 = false := by decide
theorem sg_g24_w0_13 : SS.bdot w0 z13 = false := by decide
theorem sg_g24_w0_14 : SS.bdot w0 z14 = false := by decide
theorem sg_g24_w0_15 : SS.bdot w0 z15 = false := by decide
theorem ex_g24_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d g24 w0 = star (c y16) * d z4 + star (c y17) * d z5 + star (c y18) * d z6
      + star (c y19) * d z7 + star (c y8) * d z12 + star (c y9) * d z13 + star (c y10) * d z14
      + star (c y11) * d z15 := by
  unfold offSum
  rw [inc_g24]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_g24_4, flip_g24_5, flip_g24_6, flip_g24_7, flip_g24_12, flip_g24_13, flip_g24_14, flip_g24_15]
  simp only [sg_g24_w0_4, sg_g24_w0_5, sg_g24_w0_6, sg_g24_w0_7, sg_g24_w0_12, sg_g24_w0_13, sg_g24_w0_14, sg_g24_w0_15, SixQubit.signMul_false]
  try ring
theorem sg_g34_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_g34_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg_g34_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg_g34_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg_g34_w0_12 : SS.bdot w0 z12 = false := by decide
theorem sg_g34_w0_13 : SS.bdot w0 z13 = false := by decide
theorem sg_g34_w0_14 : SS.bdot w0 z14 = false := by decide
theorem sg_g34_w0_15 : SS.bdot w0 z15 = false := by decide
theorem ex_g34_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d g34 w0 = star (c y16) * d z8 + star (c y17) * d z9 + star (c y18) * d z10
      + star (c y19) * d z11 + star (c y12) * d z12 + star (c y13) * d z13 + star (c y14) * d z14
      + star (c y15) * d z15 := by
  unfold offSum
  rw [inc_g34]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_g34_8, flip_g34_9, flip_g34_10, flip_g34_11, flip_g34_12, flip_g34_13, flip_g34_14, flip_g34_15]
  simp only [sg_g34_w0_8, sg_g34_w0_9, sg_g34_w0_10, sg_g34_w0_11, sg_g34_w0_12, sg_g34_w0_13, sg_g34_w0_14, sg_g34_w0_15, SixQubit.signMul_false]
  try ring

/-! ## The diagonal layer on the free pair -/

def diagBot (c : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ x ∈ S0.filter (fun x => SS.bxor x e ∈ S0),
      SixQubit.signMul (SS.bdot z x) (star (c (SS.bxor x e)) * c x)

def diagTop (dd : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S1),
      SixQubit.signMul (SS.bdot z y) (star (dd (SS.bxor y e)) * dd y)

theorem dincB_p1 : S0.filter (fun x => SS.bxor x p1 ∈ S0) = {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19} := by decide
theorem dincT_p1 : S1.filter (fun y => SS.bxor y p1 ∈ S1) = {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19} := by decide
theorem dfB_p1_0 : SS.bxor y0 p1 = y2 := by decide
theorem dfB_p1_1 : SS.bxor y1 p1 = y3 := by decide
theorem dfB_p1_2 : SS.bxor y2 p1 = y0 := by decide
theorem dfB_p1_3 : SS.bxor y3 p1 = y1 := by decide
theorem dfB_p1_4 : SS.bxor y4 p1 = y6 := by decide
theorem dfB_p1_5 : SS.bxor y5 p1 = y7 := by decide
theorem dfB_p1_6 : SS.bxor y6 p1 = y4 := by decide
theorem dfB_p1_7 : SS.bxor y7 p1 = y5 := by decide
theorem dfB_p1_8 : SS.bxor y8 p1 = y10 := by decide
theorem dfB_p1_9 : SS.bxor y9 p1 = y11 := by decide
theorem dfB_p1_10 : SS.bxor y10 p1 = y8 := by decide
theorem dfB_p1_11 : SS.bxor y11 p1 = y9 := by decide
theorem dfB_p1_12 : SS.bxor y12 p1 = y14 := by decide
theorem dfB_p1_13 : SS.bxor y13 p1 = y15 := by decide
theorem dfB_p1_14 : SS.bxor y14 p1 = y12 := by decide
theorem dfB_p1_15 : SS.bxor y15 p1 = y13 := by decide
theorem dfB_p1_16 : SS.bxor y16 p1 = y18 := by decide
theorem dfB_p1_17 : SS.bxor y17 p1 = y19 := by decide
theorem dfB_p1_18 : SS.bxor y18 p1 = y16 := by decide
theorem dfB_p1_19 : SS.bxor y19 p1 = y17 := by decide
theorem dfT_p1_0 : SS.bxor z0 p1 = z2 := by decide
theorem dfT_p1_1 : SS.bxor z1 p1 = z3 := by decide
theorem dfT_p1_2 : SS.bxor z2 p1 = z0 := by decide
theorem dfT_p1_3 : SS.bxor z3 p1 = z1 := by decide
theorem dfT_p1_4 : SS.bxor z4 p1 = z6 := by decide
theorem dfT_p1_5 : SS.bxor z5 p1 = z7 := by decide
theorem dfT_p1_6 : SS.bxor z6 p1 = z4 := by decide
theorem dfT_p1_7 : SS.bxor z7 p1 = z5 := by decide
theorem dfT_p1_8 : SS.bxor z8 p1 = z10 := by decide
theorem dfT_p1_9 : SS.bxor z9 p1 = z11 := by decide
theorem dfT_p1_10 : SS.bxor z10 p1 = z8 := by decide
theorem dfT_p1_11 : SS.bxor z11 p1 = z9 := by decide
theorem dfT_p1_12 : SS.bxor z12 p1 = z14 := by decide
theorem dfT_p1_13 : SS.bxor z13 p1 = z15 := by decide
theorem dfT_p1_14 : SS.bxor z14 p1 = z12 := by decide
theorem dfT_p1_15 : SS.bxor z15 p1 = z13 := by decide
theorem dfT_p1_16 : SS.bxor z16 p1 = z18 := by decide
theorem dfT_p1_17 : SS.bxor z17 p1 = z19 := by decide
theorem dfT_p1_18 : SS.bxor z18 p1 = z16 := by decide
theorem dfT_p1_19 : SS.bxor z19 p1 = z17 := by decide
theorem dincB_p2 : S0.filter (fun x => SS.bxor x p2 ∈ S0) = {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19} := by decide
theorem dincT_p2 : S1.filter (fun y => SS.bxor y p2 ∈ S1) = {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19} := by decide
theorem dfB_p2_0 : SS.bxor y0 p2 = y1 := by decide
theorem dfB_p2_1 : SS.bxor y1 p2 = y0 := by decide
theorem dfB_p2_2 : SS.bxor y2 p2 = y3 := by decide
theorem dfB_p2_3 : SS.bxor y3 p2 = y2 := by decide
theorem dfB_p2_4 : SS.bxor y4 p2 = y5 := by decide
theorem dfB_p2_5 : SS.bxor y5 p2 = y4 := by decide
theorem dfB_p2_6 : SS.bxor y6 p2 = y7 := by decide
theorem dfB_p2_7 : SS.bxor y7 p2 = y6 := by decide
theorem dfB_p2_8 : SS.bxor y8 p2 = y9 := by decide
theorem dfB_p2_9 : SS.bxor y9 p2 = y8 := by decide
theorem dfB_p2_10 : SS.bxor y10 p2 = y11 := by decide
theorem dfB_p2_11 : SS.bxor y11 p2 = y10 := by decide
theorem dfB_p2_12 : SS.bxor y12 p2 = y13 := by decide
theorem dfB_p2_13 : SS.bxor y13 p2 = y12 := by decide
theorem dfB_p2_14 : SS.bxor y14 p2 = y15 := by decide
theorem dfB_p2_15 : SS.bxor y15 p2 = y14 := by decide
theorem dfB_p2_16 : SS.bxor y16 p2 = y17 := by decide
theorem dfB_p2_17 : SS.bxor y17 p2 = y16 := by decide
theorem dfB_p2_18 : SS.bxor y18 p2 = y19 := by decide
theorem dfB_p2_19 : SS.bxor y19 p2 = y18 := by decide
theorem dfT_p2_0 : SS.bxor z0 p2 = z1 := by decide
theorem dfT_p2_1 : SS.bxor z1 p2 = z0 := by decide
theorem dfT_p2_2 : SS.bxor z2 p2 = z3 := by decide
theorem dfT_p2_3 : SS.bxor z3 p2 = z2 := by decide
theorem dfT_p2_4 : SS.bxor z4 p2 = z5 := by decide
theorem dfT_p2_5 : SS.bxor z5 p2 = z4 := by decide
theorem dfT_p2_6 : SS.bxor z6 p2 = z7 := by decide
theorem dfT_p2_7 : SS.bxor z7 p2 = z6 := by decide
theorem dfT_p2_8 : SS.bxor z8 p2 = z9 := by decide
theorem dfT_p2_9 : SS.bxor z9 p2 = z8 := by decide
theorem dfT_p2_10 : SS.bxor z10 p2 = z11 := by decide
theorem dfT_p2_11 : SS.bxor z11 p2 = z10 := by decide
theorem dfT_p2_12 : SS.bxor z12 p2 = z13 := by decide
theorem dfT_p2_13 : SS.bxor z13 p2 = z12 := by decide
theorem dfT_p2_14 : SS.bxor z14 p2 = z15 := by decide
theorem dfT_p2_15 : SS.bxor z15 p2 = z14 := by decide
theorem dfT_p2_16 : SS.bxor z16 p2 = z17 := by decide
theorem dfT_p2_17 : SS.bxor z17 p2 = z16 := by decide
theorem dfT_p2_18 : SS.bxor z18 p2 = z19 := by decide
theorem dfT_p2_19 : SS.bxor z19 p2 = z18 := by decide
theorem dincB_p3 : S0.filter (fun x => SS.bxor x p3 ∈ S0) = {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19} := by decide
theorem dincT_p3 : S1.filter (fun y => SS.bxor y p3 ∈ S1) = {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19} := by decide
theorem dfB_p3_0 : SS.bxor y0 p3 = y3 := by decide
theorem dfB_p3_1 : SS.bxor y1 p3 = y2 := by decide
theorem dfB_p3_2 : SS.bxor y2 p3 = y1 := by decide
theorem dfB_p3_3 : SS.bxor y3 p3 = y0 := by decide
theorem dfB_p3_4 : SS.bxor y4 p3 = y7 := by decide
theorem dfB_p3_5 : SS.bxor y5 p3 = y6 := by decide
theorem dfB_p3_6 : SS.bxor y6 p3 = y5 := by decide
theorem dfB_p3_7 : SS.bxor y7 p3 = y4 := by decide
theorem dfB_p3_8 : SS.bxor y8 p3 = y11 := by decide
theorem dfB_p3_9 : SS.bxor y9 p3 = y10 := by decide
theorem dfB_p3_10 : SS.bxor y10 p3 = y9 := by decide
theorem dfB_p3_11 : SS.bxor y11 p3 = y8 := by decide
theorem dfB_p3_12 : SS.bxor y12 p3 = y15 := by decide
theorem dfB_p3_13 : SS.bxor y13 p3 = y14 := by decide
theorem dfB_p3_14 : SS.bxor y14 p3 = y13 := by decide
theorem dfB_p3_15 : SS.bxor y15 p3 = y12 := by decide
theorem dfB_p3_16 : SS.bxor y16 p3 = y19 := by decide
theorem dfB_p3_17 : SS.bxor y17 p3 = y18 := by decide
theorem dfB_p3_18 : SS.bxor y18 p3 = y17 := by decide
theorem dfB_p3_19 : SS.bxor y19 p3 = y16 := by decide
theorem dfT_p3_0 : SS.bxor z0 p3 = z3 := by decide
theorem dfT_p3_1 : SS.bxor z1 p3 = z2 := by decide
theorem dfT_p3_2 : SS.bxor z2 p3 = z1 := by decide
theorem dfT_p3_3 : SS.bxor z3 p3 = z0 := by decide
theorem dfT_p3_4 : SS.bxor z4 p3 = z7 := by decide
theorem dfT_p3_5 : SS.bxor z5 p3 = z6 := by decide
theorem dfT_p3_6 : SS.bxor z6 p3 = z5 := by decide
theorem dfT_p3_7 : SS.bxor z7 p3 = z4 := by decide
theorem dfT_p3_8 : SS.bxor z8 p3 = z11 := by decide
theorem dfT_p3_9 : SS.bxor z9 p3 = z10 := by decide
theorem dfT_p3_10 : SS.bxor z10 p3 = z9 := by decide
theorem dfT_p3_11 : SS.bxor z11 p3 = z8 := by decide
theorem dfT_p3_12 : SS.bxor z12 p3 = z15 := by decide
theorem dfT_p3_13 : SS.bxor z13 p3 = z14 := by decide
theorem dfT_p3_14 : SS.bxor z14 p3 = z13 := by decide
theorem dfT_p3_15 : SS.bxor z15 p3 = z12 := by decide
theorem dfT_p3_16 : SS.bxor z16 p3 = z19 := by decide
theorem dfT_p3_17 : SS.bxor z17 p3 = z18 := by decide
theorem dfT_p3_18 : SS.bxor z18 p3 = z17 := by decide
theorem dfT_p3_19 : SS.bxor z19 p3 = z16 := by decide

theorem dsB_p1_w0_0 : SS.bdot w0 y0 = false := by decide
theorem dsB_p1_w0_1 : SS.bdot w0 y1 = false := by decide
theorem dsB_p1_w0_2 : SS.bdot w0 y2 = false := by decide
theorem dsB_p1_w0_3 : SS.bdot w0 y3 = false := by decide
theorem dsB_p1_w0_4 : SS.bdot w0 y4 = false := by decide
theorem dsB_p1_w0_5 : SS.bdot w0 y5 = false := by decide
theorem dsB_p1_w0_6 : SS.bdot w0 y6 = false := by decide
theorem dsB_p1_w0_7 : SS.bdot w0 y7 = false := by decide
theorem dsB_p1_w0_8 : SS.bdot w0 y8 = false := by decide
theorem dsB_p1_w0_9 : SS.bdot w0 y9 = false := by decide
theorem dsB_p1_w0_10 : SS.bdot w0 y10 = false := by decide
theorem dsB_p1_w0_11 : SS.bdot w0 y11 = false := by decide
theorem dsB_p1_w0_12 : SS.bdot w0 y12 = false := by decide
theorem dsB_p1_w0_13 : SS.bdot w0 y13 = false := by decide
theorem dsB_p1_w0_14 : SS.bdot w0 y14 = false := by decide
theorem dsB_p1_w0_15 : SS.bdot w0 y15 = false := by decide
theorem dsB_p1_w0_16 : SS.bdot w0 y16 = false := by decide
theorem dsB_p1_w0_17 : SS.bdot w0 y17 = false := by decide
theorem dsB_p1_w0_18 : SS.bdot w0 y18 = false := by decide
theorem dsB_p1_w0_19 : SS.bdot w0 y19 = false := by decide
theorem dexB_p1_w0 (c : SS.BitString 6 -> ℂ) :
    diagBot c p1 w0 = star (c y2) * c y0 + star (c y3) * c y1 + star (c y0) * c y2 + star (c y1) * c y3
      + star (c y6) * c y4 + star (c y7) * c y5 + star (c y4) * c y6 + star (c y5) * c y7
      + star (c y10) * c y8 + star (c y11) * c y9 + star (c y8) * c y10 + star (c y9) * c y11
      + star (c y14) * c y12 + star (c y15) * c y13 + star (c y12) * c y14 + star (c y13) * c y15
      + star (c y18) * c y16 + star (c y19) * c y17 + star (c y16) * c y18 + star (c y17) * c y19 := by
  unfold diagBot
  rw [dincB_p1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfB_p1_0, dfB_p1_1, dfB_p1_2, dfB_p1_3, dfB_p1_4, dfB_p1_5, dfB_p1_6, dfB_p1_7, dfB_p1_8, dfB_p1_9, dfB_p1_10, dfB_p1_11, dfB_p1_12, dfB_p1_13, dfB_p1_14, dfB_p1_15, dfB_p1_16, dfB_p1_17, dfB_p1_18, dfB_p1_19]
  simp only [dsB_p1_w0_0, dsB_p1_w0_1, dsB_p1_w0_2, dsB_p1_w0_3, dsB_p1_w0_4, dsB_p1_w0_5, dsB_p1_w0_6, dsB_p1_w0_7, dsB_p1_w0_8, dsB_p1_w0_9, dsB_p1_w0_10, dsB_p1_w0_11, dsB_p1_w0_12, dsB_p1_w0_13, dsB_p1_w0_14, dsB_p1_w0_15, dsB_p1_w0_16, dsB_p1_w0_17, dsB_p1_w0_18, dsB_p1_w0_19, SixQubit.signMul_false]
  try ring
theorem dsT_p1_w0_0 : SS.bdot w0 z0 = false := by decide
theorem dsT_p1_w0_1 : SS.bdot w0 z1 = false := by decide
theorem dsT_p1_w0_2 : SS.bdot w0 z2 = false := by decide
theorem dsT_p1_w0_3 : SS.bdot w0 z3 = false := by decide
theorem dsT_p1_w0_4 : SS.bdot w0 z4 = false := by decide
theorem dsT_p1_w0_5 : SS.bdot w0 z5 = false := by decide
theorem dsT_p1_w0_6 : SS.bdot w0 z6 = false := by decide
theorem dsT_p1_w0_7 : SS.bdot w0 z7 = false := by decide
theorem dsT_p1_w0_8 : SS.bdot w0 z8 = false := by decide
theorem dsT_p1_w0_9 : SS.bdot w0 z9 = false := by decide
theorem dsT_p1_w0_10 : SS.bdot w0 z10 = false := by decide
theorem dsT_p1_w0_11 : SS.bdot w0 z11 = false := by decide
theorem dsT_p1_w0_12 : SS.bdot w0 z12 = false := by decide
theorem dsT_p1_w0_13 : SS.bdot w0 z13 = false := by decide
theorem dsT_p1_w0_14 : SS.bdot w0 z14 = false := by decide
theorem dsT_p1_w0_15 : SS.bdot w0 z15 = false := by decide
theorem dsT_p1_w0_16 : SS.bdot w0 z16 = false := by decide
theorem dsT_p1_w0_17 : SS.bdot w0 z17 = false := by decide
theorem dsT_p1_w0_18 : SS.bdot w0 z18 = false := by decide
theorem dsT_p1_w0_19 : SS.bdot w0 z19 = false := by decide
theorem dexT_p1_w0 (dd : SS.BitString 6 -> ℂ) :
    diagTop dd p1 w0 = star (dd z2) * dd z0 + star (dd z3) * dd z1 + star (dd z0) * dd z2
      + star (dd z1) * dd z3 + star (dd z6) * dd z4 + star (dd z7) * dd z5 + star (dd z4) * dd z6
      + star (dd z5) * dd z7 + star (dd z10) * dd z8 + star (dd z11) * dd z9 + star (dd z8) * dd z10
      + star (dd z9) * dd z11 + star (dd z14) * dd z12 + star (dd z15) * dd z13 + star (dd z12) * dd z14
      + star (dd z13) * dd z15 + star (dd z18) * dd z16 + star (dd z19) * dd z17
      + star (dd z16) * dd z18 + star (dd z17) * dd z19 := by
  unfold diagTop
  rw [dincT_p1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfT_p1_0, dfT_p1_1, dfT_p1_2, dfT_p1_3, dfT_p1_4, dfT_p1_5, dfT_p1_6, dfT_p1_7, dfT_p1_8, dfT_p1_9, dfT_p1_10, dfT_p1_11, dfT_p1_12, dfT_p1_13, dfT_p1_14, dfT_p1_15, dfT_p1_16, dfT_p1_17, dfT_p1_18, dfT_p1_19]
  simp only [dsT_p1_w0_0, dsT_p1_w0_1, dsT_p1_w0_2, dsT_p1_w0_3, dsT_p1_w0_4, dsT_p1_w0_5, dsT_p1_w0_6, dsT_p1_w0_7, dsT_p1_w0_8, dsT_p1_w0_9, dsT_p1_w0_10, dsT_p1_w0_11, dsT_p1_w0_12, dsT_p1_w0_13, dsT_p1_w0_14, dsT_p1_w0_15, dsT_p1_w0_16, dsT_p1_w0_17, dsT_p1_w0_18, dsT_p1_w0_19, SixQubit.signMul_false]
  try ring
theorem dsB_p1_w1_0 : SS.bdot w1 y0 = false := by decide
theorem dsB_p1_w1_1 : SS.bdot w1 y1 = false := by decide
theorem dsB_p1_w1_2 : SS.bdot w1 y2 = true := by decide
theorem dsB_p1_w1_3 : SS.bdot w1 y3 = true := by decide
theorem dsB_p1_w1_4 : SS.bdot w1 y4 = false := by decide
theorem dsB_p1_w1_5 : SS.bdot w1 y5 = false := by decide
theorem dsB_p1_w1_6 : SS.bdot w1 y6 = true := by decide
theorem dsB_p1_w1_7 : SS.bdot w1 y7 = true := by decide
theorem dsB_p1_w1_8 : SS.bdot w1 y8 = false := by decide
theorem dsB_p1_w1_9 : SS.bdot w1 y9 = false := by decide
theorem dsB_p1_w1_10 : SS.bdot w1 y10 = true := by decide
theorem dsB_p1_w1_11 : SS.bdot w1 y11 = true := by decide
theorem dsB_p1_w1_12 : SS.bdot w1 y12 = false := by decide
theorem dsB_p1_w1_13 : SS.bdot w1 y13 = false := by decide
theorem dsB_p1_w1_14 : SS.bdot w1 y14 = true := by decide
theorem dsB_p1_w1_15 : SS.bdot w1 y15 = true := by decide
theorem dsB_p1_w1_16 : SS.bdot w1 y16 = false := by decide
theorem dsB_p1_w1_17 : SS.bdot w1 y17 = false := by decide
theorem dsB_p1_w1_18 : SS.bdot w1 y18 = true := by decide
theorem dsB_p1_w1_19 : SS.bdot w1 y19 = true := by decide
theorem dexB_p1_w1 (c : SS.BitString 6 -> ℂ) :
    diagBot c p1 w1 = star (c y2) * c y0 + star (c y3) * c y1 - star (c y0) * c y2 - star (c y1) * c y3
      + star (c y6) * c y4 + star (c y7) * c y5 - star (c y4) * c y6 - star (c y5) * c y7
      + star (c y10) * c y8 + star (c y11) * c y9 - star (c y8) * c y10 - star (c y9) * c y11
      + star (c y14) * c y12 + star (c y15) * c y13 - star (c y12) * c y14 - star (c y13) * c y15
      + star (c y18) * c y16 + star (c y19) * c y17 - star (c y16) * c y18 - star (c y17) * c y19 := by
  unfold diagBot
  rw [dincB_p1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfB_p1_0, dfB_p1_1, dfB_p1_2, dfB_p1_3, dfB_p1_4, dfB_p1_5, dfB_p1_6, dfB_p1_7, dfB_p1_8, dfB_p1_9, dfB_p1_10, dfB_p1_11, dfB_p1_12, dfB_p1_13, dfB_p1_14, dfB_p1_15, dfB_p1_16, dfB_p1_17, dfB_p1_18, dfB_p1_19]
  simp only [dsB_p1_w1_0, dsB_p1_w1_1, dsB_p1_w1_2, dsB_p1_w1_3, dsB_p1_w1_4, dsB_p1_w1_5, dsB_p1_w1_6, dsB_p1_w1_7, dsB_p1_w1_8, dsB_p1_w1_9, dsB_p1_w1_10, dsB_p1_w1_11, dsB_p1_w1_12, dsB_p1_w1_13, dsB_p1_w1_14, dsB_p1_w1_15, dsB_p1_w1_16, dsB_p1_w1_17, dsB_p1_w1_18, dsB_p1_w1_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem dsT_p1_w1_0 : SS.bdot w1 z0 = false := by decide
theorem dsT_p1_w1_1 : SS.bdot w1 z1 = false := by decide
theorem dsT_p1_w1_2 : SS.bdot w1 z2 = true := by decide
theorem dsT_p1_w1_3 : SS.bdot w1 z3 = true := by decide
theorem dsT_p1_w1_4 : SS.bdot w1 z4 = false := by decide
theorem dsT_p1_w1_5 : SS.bdot w1 z5 = false := by decide
theorem dsT_p1_w1_6 : SS.bdot w1 z6 = true := by decide
theorem dsT_p1_w1_7 : SS.bdot w1 z7 = true := by decide
theorem dsT_p1_w1_8 : SS.bdot w1 z8 = false := by decide
theorem dsT_p1_w1_9 : SS.bdot w1 z9 = false := by decide
theorem dsT_p1_w1_10 : SS.bdot w1 z10 = true := by decide
theorem dsT_p1_w1_11 : SS.bdot w1 z11 = true := by decide
theorem dsT_p1_w1_12 : SS.bdot w1 z12 = false := by decide
theorem dsT_p1_w1_13 : SS.bdot w1 z13 = false := by decide
theorem dsT_p1_w1_14 : SS.bdot w1 z14 = true := by decide
theorem dsT_p1_w1_15 : SS.bdot w1 z15 = true := by decide
theorem dsT_p1_w1_16 : SS.bdot w1 z16 = false := by decide
theorem dsT_p1_w1_17 : SS.bdot w1 z17 = false := by decide
theorem dsT_p1_w1_18 : SS.bdot w1 z18 = true := by decide
theorem dsT_p1_w1_19 : SS.bdot w1 z19 = true := by decide
theorem dexT_p1_w1 (dd : SS.BitString 6 -> ℂ) :
    diagTop dd p1 w1 = star (dd z2) * dd z0
      + star (dd z3) * dd z1 - star (dd z0) * dd z2 - star (dd z1) * dd z3 + star (dd z6) * dd z4
      + star (dd z7) * dd z5 - star (dd z4) * dd z6 - star (dd z5) * dd z7 + star (dd z10) * dd z8
      + star (dd z11) * dd z9 - star (dd z8) * dd z10 - star (dd z9) * dd z11 + star (dd z14) * dd z12
      + star (dd z15) * dd z13 - star (dd z12) * dd z14 - star (dd z13) * dd z15
      + star (dd z18) * dd z16
      + star (dd z19) * dd z17 - star (dd z16) * dd z18 - star (dd z17) * dd z19 := by
  unfold diagTop
  rw [dincT_p1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfT_p1_0, dfT_p1_1, dfT_p1_2, dfT_p1_3, dfT_p1_4, dfT_p1_5, dfT_p1_6, dfT_p1_7, dfT_p1_8, dfT_p1_9, dfT_p1_10, dfT_p1_11, dfT_p1_12, dfT_p1_13, dfT_p1_14, dfT_p1_15, dfT_p1_16, dfT_p1_17, dfT_p1_18, dfT_p1_19]
  simp only [dsT_p1_w1_0, dsT_p1_w1_1, dsT_p1_w1_2, dsT_p1_w1_3, dsT_p1_w1_4, dsT_p1_w1_5, dsT_p1_w1_6, dsT_p1_w1_7, dsT_p1_w1_8, dsT_p1_w1_9, dsT_p1_w1_10, dsT_p1_w1_11, dsT_p1_w1_12, dsT_p1_w1_13, dsT_p1_w1_14, dsT_p1_w1_15, dsT_p1_w1_16, dsT_p1_w1_17, dsT_p1_w1_18, dsT_p1_w1_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem dsB_p1_w2_0 : SS.bdot w2 y0 = false := by decide
theorem dsB_p1_w2_1 : SS.bdot w2 y1 = true := by decide
theorem dsB_p1_w2_2 : SS.bdot w2 y2 = false := by decide
theorem dsB_p1_w2_3 : SS.bdot w2 y3 = true := by decide
theorem dsB_p1_w2_4 : SS.bdot w2 y4 = false := by decide
theorem dsB_p1_w2_5 : SS.bdot w2 y5 = true := by decide
theorem dsB_p1_w2_6 : SS.bdot w2 y6 = false := by decide
theorem dsB_p1_w2_7 : SS.bdot w2 y7 = true := by decide
theorem dsB_p1_w2_8 : SS.bdot w2 y8 = false := by decide
theorem dsB_p1_w2_9 : SS.bdot w2 y9 = true := by decide
theorem dsB_p1_w2_10 : SS.bdot w2 y10 = false := by decide
theorem dsB_p1_w2_11 : SS.bdot w2 y11 = true := by decide
theorem dsB_p1_w2_12 : SS.bdot w2 y12 = false := by decide
theorem dsB_p1_w2_13 : SS.bdot w2 y13 = true := by decide
theorem dsB_p1_w2_14 : SS.bdot w2 y14 = false := by decide
theorem dsB_p1_w2_15 : SS.bdot w2 y15 = true := by decide
theorem dsB_p1_w2_16 : SS.bdot w2 y16 = false := by decide
theorem dsB_p1_w2_17 : SS.bdot w2 y17 = true := by decide
theorem dsB_p1_w2_18 : SS.bdot w2 y18 = false := by decide
theorem dsB_p1_w2_19 : SS.bdot w2 y19 = true := by decide
theorem dexB_p1_w2 (c : SS.BitString 6 -> ℂ) :
    diagBot c p1 w2 = star (c y2) * c y0 - star (c y3) * c y1 + star (c y0) * c y2 - star (c y1) * c y3
      + star (c y6) * c y4 - star (c y7) * c y5 + star (c y4) * c y6 - star (c y5) * c y7
      + star (c y10) * c y8 - star (c y11) * c y9 + star (c y8) * c y10 - star (c y9) * c y11
      + star (c y14) * c y12 - star (c y15) * c y13 + star (c y12) * c y14 - star (c y13) * c y15
      + star (c y18) * c y16 - star (c y19) * c y17 + star (c y16) * c y18 - star (c y17) * c y19 := by
  unfold diagBot
  rw [dincB_p1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfB_p1_0, dfB_p1_1, dfB_p1_2, dfB_p1_3, dfB_p1_4, dfB_p1_5, dfB_p1_6, dfB_p1_7, dfB_p1_8, dfB_p1_9, dfB_p1_10, dfB_p1_11, dfB_p1_12, dfB_p1_13, dfB_p1_14, dfB_p1_15, dfB_p1_16, dfB_p1_17, dfB_p1_18, dfB_p1_19]
  simp only [dsB_p1_w2_0, dsB_p1_w2_1, dsB_p1_w2_2, dsB_p1_w2_3, dsB_p1_w2_4, dsB_p1_w2_5, dsB_p1_w2_6, dsB_p1_w2_7, dsB_p1_w2_8, dsB_p1_w2_9, dsB_p1_w2_10, dsB_p1_w2_11, dsB_p1_w2_12, dsB_p1_w2_13, dsB_p1_w2_14, dsB_p1_w2_15, dsB_p1_w2_16, dsB_p1_w2_17, dsB_p1_w2_18, dsB_p1_w2_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem dsT_p1_w2_0 : SS.bdot w2 z0 = false := by decide
theorem dsT_p1_w2_1 : SS.bdot w2 z1 = true := by decide
theorem dsT_p1_w2_2 : SS.bdot w2 z2 = false := by decide
theorem dsT_p1_w2_3 : SS.bdot w2 z3 = true := by decide
theorem dsT_p1_w2_4 : SS.bdot w2 z4 = false := by decide
theorem dsT_p1_w2_5 : SS.bdot w2 z5 = true := by decide
theorem dsT_p1_w2_6 : SS.bdot w2 z6 = false := by decide
theorem dsT_p1_w2_7 : SS.bdot w2 z7 = true := by decide
theorem dsT_p1_w2_8 : SS.bdot w2 z8 = false := by decide
theorem dsT_p1_w2_9 : SS.bdot w2 z9 = true := by decide
theorem dsT_p1_w2_10 : SS.bdot w2 z10 = false := by decide
theorem dsT_p1_w2_11 : SS.bdot w2 z11 = true := by decide
theorem dsT_p1_w2_12 : SS.bdot w2 z12 = false := by decide
theorem dsT_p1_w2_13 : SS.bdot w2 z13 = true := by decide
theorem dsT_p1_w2_14 : SS.bdot w2 z14 = false := by decide
theorem dsT_p1_w2_15 : SS.bdot w2 z15 = true := by decide
theorem dsT_p1_w2_16 : SS.bdot w2 z16 = false := by decide
theorem dsT_p1_w2_17 : SS.bdot w2 z17 = true := by decide
theorem dsT_p1_w2_18 : SS.bdot w2 z18 = false := by decide
theorem dsT_p1_w2_19 : SS.bdot w2 z19 = true := by decide
theorem dexT_p1_w2 (dd : SS.BitString 6 -> ℂ) :
    diagTop dd p1 w2 = star (dd z2) * dd z0 - star (dd z3) * dd z1
      + star (dd z0) * dd z2 - star (dd z1) * dd z3 + star (dd z6) * dd z4 - star (dd z7) * dd z5
      + star (dd z4) * dd z6 - star (dd z5) * dd z7 + star (dd z10) * dd z8 - star (dd z11) * dd z9
      + star (dd z8) * dd z10 - star (dd z9) * dd z11 + star (dd z14) * dd z12 - star (dd z15) * dd z13
      + star (dd z12) * dd z14 - star (dd z13) * dd z15
      + star (dd z18) * dd z16 - star (dd z19) * dd z17
      + star (dd z16) * dd z18 - star (dd z17) * dd z19 := by
  unfold diagTop
  rw [dincT_p1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfT_p1_0, dfT_p1_1, dfT_p1_2, dfT_p1_3, dfT_p1_4, dfT_p1_5, dfT_p1_6, dfT_p1_7, dfT_p1_8, dfT_p1_9, dfT_p1_10, dfT_p1_11, dfT_p1_12, dfT_p1_13, dfT_p1_14, dfT_p1_15, dfT_p1_16, dfT_p1_17, dfT_p1_18, dfT_p1_19]
  simp only [dsT_p1_w2_0, dsT_p1_w2_1, dsT_p1_w2_2, dsT_p1_w2_3, dsT_p1_w2_4, dsT_p1_w2_5, dsT_p1_w2_6, dsT_p1_w2_7, dsT_p1_w2_8, dsT_p1_w2_9, dsT_p1_w2_10, dsT_p1_w2_11, dsT_p1_w2_12, dsT_p1_w2_13, dsT_p1_w2_14, dsT_p1_w2_15, dsT_p1_w2_16, dsT_p1_w2_17, dsT_p1_w2_18, dsT_p1_w2_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem dsB_p1_w3_0 : SS.bdot w3 y0 = false := by decide
theorem dsB_p1_w3_1 : SS.bdot w3 y1 = true := by decide
theorem dsB_p1_w3_2 : SS.bdot w3 y2 = true := by decide
theorem dsB_p1_w3_3 : SS.bdot w3 y3 = false := by decide
theorem dsB_p1_w3_4 : SS.bdot w3 y4 = false := by decide
theorem dsB_p1_w3_5 : SS.bdot w3 y5 = true := by decide
theorem dsB_p1_w3_6 : SS.bdot w3 y6 = true := by decide
theorem dsB_p1_w3_7 : SS.bdot w3 y7 = false := by decide
theorem dsB_p1_w3_8 : SS.bdot w3 y8 = false := by decide
theorem dsB_p1_w3_9 : SS.bdot w3 y9 = true := by decide
theorem dsB_p1_w3_10 : SS.bdot w3 y10 = true := by decide
theorem dsB_p1_w3_11 : SS.bdot w3 y11 = false := by decide
theorem dsB_p1_w3_12 : SS.bdot w3 y12 = false := by decide
theorem dsB_p1_w3_13 : SS.bdot w3 y13 = true := by decide
theorem dsB_p1_w3_14 : SS.bdot w3 y14 = true := by decide
theorem dsB_p1_w3_15 : SS.bdot w3 y15 = false := by decide
theorem dsB_p1_w3_16 : SS.bdot w3 y16 = false := by decide
theorem dsB_p1_w3_17 : SS.bdot w3 y17 = true := by decide
theorem dsB_p1_w3_18 : SS.bdot w3 y18 = true := by decide
theorem dsB_p1_w3_19 : SS.bdot w3 y19 = false := by decide
theorem dexB_p1_w3 (c : SS.BitString 6 -> ℂ) :
    diagBot c p1 w3 = star (c y2) * c y0 - star (c y3) * c y1 - star (c y0) * c y2 + star (c y1) * c y3
      + star (c y6) * c y4 - star (c y7) * c y5 - star (c y4) * c y6 + star (c y5) * c y7
      + star (c y10) * c y8 - star (c y11) * c y9 - star (c y8) * c y10 + star (c y9) * c y11
      + star (c y14) * c y12 - star (c y15) * c y13 - star (c y12) * c y14 + star (c y13) * c y15
      + star (c y18) * c y16 - star (c y19) * c y17 - star (c y16) * c y18 + star (c y17) * c y19 := by
  unfold diagBot
  rw [dincB_p1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfB_p1_0, dfB_p1_1, dfB_p1_2, dfB_p1_3, dfB_p1_4, dfB_p1_5, dfB_p1_6, dfB_p1_7, dfB_p1_8, dfB_p1_9, dfB_p1_10, dfB_p1_11, dfB_p1_12, dfB_p1_13, dfB_p1_14, dfB_p1_15, dfB_p1_16, dfB_p1_17, dfB_p1_18, dfB_p1_19]
  simp only [dsB_p1_w3_0, dsB_p1_w3_1, dsB_p1_w3_2, dsB_p1_w3_3, dsB_p1_w3_4, dsB_p1_w3_5, dsB_p1_w3_6, dsB_p1_w3_7, dsB_p1_w3_8, dsB_p1_w3_9, dsB_p1_w3_10, dsB_p1_w3_11, dsB_p1_w3_12, dsB_p1_w3_13, dsB_p1_w3_14, dsB_p1_w3_15, dsB_p1_w3_16, dsB_p1_w3_17, dsB_p1_w3_18, dsB_p1_w3_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem dsT_p1_w3_0 : SS.bdot w3 z0 = false := by decide
theorem dsT_p1_w3_1 : SS.bdot w3 z1 = true := by decide
theorem dsT_p1_w3_2 : SS.bdot w3 z2 = true := by decide
theorem dsT_p1_w3_3 : SS.bdot w3 z3 = false := by decide
theorem dsT_p1_w3_4 : SS.bdot w3 z4 = false := by decide
theorem dsT_p1_w3_5 : SS.bdot w3 z5 = true := by decide
theorem dsT_p1_w3_6 : SS.bdot w3 z6 = true := by decide
theorem dsT_p1_w3_7 : SS.bdot w3 z7 = false := by decide
theorem dsT_p1_w3_8 : SS.bdot w3 z8 = false := by decide
theorem dsT_p1_w3_9 : SS.bdot w3 z9 = true := by decide
theorem dsT_p1_w3_10 : SS.bdot w3 z10 = true := by decide
theorem dsT_p1_w3_11 : SS.bdot w3 z11 = false := by decide
theorem dsT_p1_w3_12 : SS.bdot w3 z12 = false := by decide
theorem dsT_p1_w3_13 : SS.bdot w3 z13 = true := by decide
theorem dsT_p1_w3_14 : SS.bdot w3 z14 = true := by decide
theorem dsT_p1_w3_15 : SS.bdot w3 z15 = false := by decide
theorem dsT_p1_w3_16 : SS.bdot w3 z16 = false := by decide
theorem dsT_p1_w3_17 : SS.bdot w3 z17 = true := by decide
theorem dsT_p1_w3_18 : SS.bdot w3 z18 = true := by decide
theorem dsT_p1_w3_19 : SS.bdot w3 z19 = false := by decide
theorem dexT_p1_w3 (dd : SS.BitString 6 -> ℂ) :
    diagTop dd p1 w3 = star (dd z2) * dd z0 - star (dd z3) * dd z1 - star (dd z0) * dd z2
      + star (dd z1) * dd z3 + star (dd z6) * dd z4 - star (dd z7) * dd z5 - star (dd z4) * dd z6
      + star (dd z5) * dd z7 + star (dd z10) * dd z8 - star (dd z11) * dd z9 - star (dd z8) * dd z10
      + star (dd z9) * dd z11 + star (dd z14) * dd z12 - star (dd z15) * dd z13 - star (dd z12) * dd z14
      + star (dd z13) * dd z15
      + star (dd z18) * dd z16 - star (dd z19) * dd z17 - star (dd z16) * dd z18
      + star (dd z17) * dd z19 := by
  unfold diagTop
  rw [dincT_p1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfT_p1_0, dfT_p1_1, dfT_p1_2, dfT_p1_3, dfT_p1_4, dfT_p1_5, dfT_p1_6, dfT_p1_7, dfT_p1_8, dfT_p1_9, dfT_p1_10, dfT_p1_11, dfT_p1_12, dfT_p1_13, dfT_p1_14, dfT_p1_15, dfT_p1_16, dfT_p1_17, dfT_p1_18, dfT_p1_19]
  simp only [dsT_p1_w3_0, dsT_p1_w3_1, dsT_p1_w3_2, dsT_p1_w3_3, dsT_p1_w3_4, dsT_p1_w3_5, dsT_p1_w3_6, dsT_p1_w3_7, dsT_p1_w3_8, dsT_p1_w3_9, dsT_p1_w3_10, dsT_p1_w3_11, dsT_p1_w3_12, dsT_p1_w3_13, dsT_p1_w3_14, dsT_p1_w3_15, dsT_p1_w3_16, dsT_p1_w3_17, dsT_p1_w3_18, dsT_p1_w3_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem dsB_p2_w0_0 : SS.bdot w0 y0 = false := by decide
theorem dsB_p2_w0_1 : SS.bdot w0 y1 = false := by decide
theorem dsB_p2_w0_2 : SS.bdot w0 y2 = false := by decide
theorem dsB_p2_w0_3 : SS.bdot w0 y3 = false := by decide
theorem dsB_p2_w0_4 : SS.bdot w0 y4 = false := by decide
theorem dsB_p2_w0_5 : SS.bdot w0 y5 = false := by decide
theorem dsB_p2_w0_6 : SS.bdot w0 y6 = false := by decide
theorem dsB_p2_w0_7 : SS.bdot w0 y7 = false := by decide
theorem dsB_p2_w0_8 : SS.bdot w0 y8 = false := by decide
theorem dsB_p2_w0_9 : SS.bdot w0 y9 = false := by decide
theorem dsB_p2_w0_10 : SS.bdot w0 y10 = false := by decide
theorem dsB_p2_w0_11 : SS.bdot w0 y11 = false := by decide
theorem dsB_p2_w0_12 : SS.bdot w0 y12 = false := by decide
theorem dsB_p2_w0_13 : SS.bdot w0 y13 = false := by decide
theorem dsB_p2_w0_14 : SS.bdot w0 y14 = false := by decide
theorem dsB_p2_w0_15 : SS.bdot w0 y15 = false := by decide
theorem dsB_p2_w0_16 : SS.bdot w0 y16 = false := by decide
theorem dsB_p2_w0_17 : SS.bdot w0 y17 = false := by decide
theorem dsB_p2_w0_18 : SS.bdot w0 y18 = false := by decide
theorem dsB_p2_w0_19 : SS.bdot w0 y19 = false := by decide
theorem dexB_p2_w0 (c : SS.BitString 6 -> ℂ) :
    diagBot c p2 w0 = star (c y1) * c y0 + star (c y0) * c y1 + star (c y3) * c y2 + star (c y2) * c y3
      + star (c y5) * c y4 + star (c y4) * c y5 + star (c y7) * c y6 + star (c y6) * c y7
      + star (c y9) * c y8 + star (c y8) * c y9 + star (c y11) * c y10 + star (c y10) * c y11
      + star (c y13) * c y12 + star (c y12) * c y13 + star (c y15) * c y14 + star (c y14) * c y15
      + star (c y17) * c y16 + star (c y16) * c y17 + star (c y19) * c y18 + star (c y18) * c y19 := by
  unfold diagBot
  rw [dincB_p2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfB_p2_0, dfB_p2_1, dfB_p2_2, dfB_p2_3, dfB_p2_4, dfB_p2_5, dfB_p2_6, dfB_p2_7, dfB_p2_8, dfB_p2_9, dfB_p2_10, dfB_p2_11, dfB_p2_12, dfB_p2_13, dfB_p2_14, dfB_p2_15, dfB_p2_16, dfB_p2_17, dfB_p2_18, dfB_p2_19]
  simp only [dsB_p2_w0_0, dsB_p2_w0_1, dsB_p2_w0_2, dsB_p2_w0_3, dsB_p2_w0_4, dsB_p2_w0_5, dsB_p2_w0_6, dsB_p2_w0_7, dsB_p2_w0_8, dsB_p2_w0_9, dsB_p2_w0_10, dsB_p2_w0_11, dsB_p2_w0_12, dsB_p2_w0_13, dsB_p2_w0_14, dsB_p2_w0_15, dsB_p2_w0_16, dsB_p2_w0_17, dsB_p2_w0_18, dsB_p2_w0_19, SixQubit.signMul_false]
  try ring
theorem dsT_p2_w0_0 : SS.bdot w0 z0 = false := by decide
theorem dsT_p2_w0_1 : SS.bdot w0 z1 = false := by decide
theorem dsT_p2_w0_2 : SS.bdot w0 z2 = false := by decide
theorem dsT_p2_w0_3 : SS.bdot w0 z3 = false := by decide
theorem dsT_p2_w0_4 : SS.bdot w0 z4 = false := by decide
theorem dsT_p2_w0_5 : SS.bdot w0 z5 = false := by decide
theorem dsT_p2_w0_6 : SS.bdot w0 z6 = false := by decide
theorem dsT_p2_w0_7 : SS.bdot w0 z7 = false := by decide
theorem dsT_p2_w0_8 : SS.bdot w0 z8 = false := by decide
theorem dsT_p2_w0_9 : SS.bdot w0 z9 = false := by decide
theorem dsT_p2_w0_10 : SS.bdot w0 z10 = false := by decide
theorem dsT_p2_w0_11 : SS.bdot w0 z11 = false := by decide
theorem dsT_p2_w0_12 : SS.bdot w0 z12 = false := by decide
theorem dsT_p2_w0_13 : SS.bdot w0 z13 = false := by decide
theorem dsT_p2_w0_14 : SS.bdot w0 z14 = false := by decide
theorem dsT_p2_w0_15 : SS.bdot w0 z15 = false := by decide
theorem dsT_p2_w0_16 : SS.bdot w0 z16 = false := by decide
theorem dsT_p2_w0_17 : SS.bdot w0 z17 = false := by decide
theorem dsT_p2_w0_18 : SS.bdot w0 z18 = false := by decide
theorem dsT_p2_w0_19 : SS.bdot w0 z19 = false := by decide
theorem dexT_p2_w0 (dd : SS.BitString 6 -> ℂ) :
    diagTop dd p2 w0 = star (dd z1) * dd z0 + star (dd z0) * dd z1 + star (dd z3) * dd z2
      + star (dd z2) * dd z3 + star (dd z5) * dd z4 + star (dd z4) * dd z5 + star (dd z7) * dd z6
      + star (dd z6) * dd z7 + star (dd z9) * dd z8 + star (dd z8) * dd z9 + star (dd z11) * dd z10
      + star (dd z10) * dd z11 + star (dd z13) * dd z12 + star (dd z12) * dd z13
      + star (dd z15) * dd z14 + star (dd z14) * dd z15 + star (dd z17) * dd z16
      + star (dd z16) * dd z17 + star (dd z19) * dd z18 + star (dd z18) * dd z19 := by
  unfold diagTop
  rw [dincT_p2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfT_p2_0, dfT_p2_1, dfT_p2_2, dfT_p2_3, dfT_p2_4, dfT_p2_5, dfT_p2_6, dfT_p2_7, dfT_p2_8, dfT_p2_9, dfT_p2_10, dfT_p2_11, dfT_p2_12, dfT_p2_13, dfT_p2_14, dfT_p2_15, dfT_p2_16, dfT_p2_17, dfT_p2_18, dfT_p2_19]
  simp only [dsT_p2_w0_0, dsT_p2_w0_1, dsT_p2_w0_2, dsT_p2_w0_3, dsT_p2_w0_4, dsT_p2_w0_5, dsT_p2_w0_6, dsT_p2_w0_7, dsT_p2_w0_8, dsT_p2_w0_9, dsT_p2_w0_10, dsT_p2_w0_11, dsT_p2_w0_12, dsT_p2_w0_13, dsT_p2_w0_14, dsT_p2_w0_15, dsT_p2_w0_16, dsT_p2_w0_17, dsT_p2_w0_18, dsT_p2_w0_19, SixQubit.signMul_false]
  try ring
theorem dsB_p2_w1_0 : SS.bdot w1 y0 = false := by decide
theorem dsB_p2_w1_1 : SS.bdot w1 y1 = false := by decide
theorem dsB_p2_w1_2 : SS.bdot w1 y2 = true := by decide
theorem dsB_p2_w1_3 : SS.bdot w1 y3 = true := by decide
theorem dsB_p2_w1_4 : SS.bdot w1 y4 = false := by decide
theorem dsB_p2_w1_5 : SS.bdot w1 y5 = false := by decide
theorem dsB_p2_w1_6 : SS.bdot w1 y6 = true := by decide
theorem dsB_p2_w1_7 : SS.bdot w1 y7 = true := by decide
theorem dsB_p2_w1_8 : SS.bdot w1 y8 = false := by decide
theorem dsB_p2_w1_9 : SS.bdot w1 y9 = false := by decide
theorem dsB_p2_w1_10 : SS.bdot w1 y10 = true := by decide
theorem dsB_p2_w1_11 : SS.bdot w1 y11 = true := by decide
theorem dsB_p2_w1_12 : SS.bdot w1 y12 = false := by decide
theorem dsB_p2_w1_13 : SS.bdot w1 y13 = false := by decide
theorem dsB_p2_w1_14 : SS.bdot w1 y14 = true := by decide
theorem dsB_p2_w1_15 : SS.bdot w1 y15 = true := by decide
theorem dsB_p2_w1_16 : SS.bdot w1 y16 = false := by decide
theorem dsB_p2_w1_17 : SS.bdot w1 y17 = false := by decide
theorem dsB_p2_w1_18 : SS.bdot w1 y18 = true := by decide
theorem dsB_p2_w1_19 : SS.bdot w1 y19 = true := by decide
theorem dexB_p2_w1 (c : SS.BitString 6 -> ℂ) :
    diagBot c p2 w1 = star (c y1) * c y0 + star (c y0) * c y1 - star (c y3) * c y2 - star (c y2) * c y3
      + star (c y5) * c y4 + star (c y4) * c y5 - star (c y7) * c y6 - star (c y6) * c y7
      + star (c y9) * c y8 + star (c y8) * c y9 - star (c y11) * c y10 - star (c y10) * c y11
      + star (c y13) * c y12 + star (c y12) * c y13 - star (c y15) * c y14 - star (c y14) * c y15
      + star (c y17) * c y16 + star (c y16) * c y17 - star (c y19) * c y18 - star (c y18) * c y19 := by
  unfold diagBot
  rw [dincB_p2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfB_p2_0, dfB_p2_1, dfB_p2_2, dfB_p2_3, dfB_p2_4, dfB_p2_5, dfB_p2_6, dfB_p2_7, dfB_p2_8, dfB_p2_9, dfB_p2_10, dfB_p2_11, dfB_p2_12, dfB_p2_13, dfB_p2_14, dfB_p2_15, dfB_p2_16, dfB_p2_17, dfB_p2_18, dfB_p2_19]
  simp only [dsB_p2_w1_0, dsB_p2_w1_1, dsB_p2_w1_2, dsB_p2_w1_3, dsB_p2_w1_4, dsB_p2_w1_5, dsB_p2_w1_6, dsB_p2_w1_7, dsB_p2_w1_8, dsB_p2_w1_9, dsB_p2_w1_10, dsB_p2_w1_11, dsB_p2_w1_12, dsB_p2_w1_13, dsB_p2_w1_14, dsB_p2_w1_15, dsB_p2_w1_16, dsB_p2_w1_17, dsB_p2_w1_18, dsB_p2_w1_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem dsT_p2_w1_0 : SS.bdot w1 z0 = false := by decide
theorem dsT_p2_w1_1 : SS.bdot w1 z1 = false := by decide
theorem dsT_p2_w1_2 : SS.bdot w1 z2 = true := by decide
theorem dsT_p2_w1_3 : SS.bdot w1 z3 = true := by decide
theorem dsT_p2_w1_4 : SS.bdot w1 z4 = false := by decide
theorem dsT_p2_w1_5 : SS.bdot w1 z5 = false := by decide
theorem dsT_p2_w1_6 : SS.bdot w1 z6 = true := by decide
theorem dsT_p2_w1_7 : SS.bdot w1 z7 = true := by decide
theorem dsT_p2_w1_8 : SS.bdot w1 z8 = false := by decide
theorem dsT_p2_w1_9 : SS.bdot w1 z9 = false := by decide
theorem dsT_p2_w1_10 : SS.bdot w1 z10 = true := by decide
theorem dsT_p2_w1_11 : SS.bdot w1 z11 = true := by decide
theorem dsT_p2_w1_12 : SS.bdot w1 z12 = false := by decide
theorem dsT_p2_w1_13 : SS.bdot w1 z13 = false := by decide
theorem dsT_p2_w1_14 : SS.bdot w1 z14 = true := by decide
theorem dsT_p2_w1_15 : SS.bdot w1 z15 = true := by decide
theorem dsT_p2_w1_16 : SS.bdot w1 z16 = false := by decide
theorem dsT_p2_w1_17 : SS.bdot w1 z17 = false := by decide
theorem dsT_p2_w1_18 : SS.bdot w1 z18 = true := by decide
theorem dsT_p2_w1_19 : SS.bdot w1 z19 = true := by decide
theorem dexT_p2_w1 (dd : SS.BitString 6 -> ℂ) :
    diagTop dd p2 w1 = star (dd z1) * dd z0
      + star (dd z0) * dd z1 - star (dd z3) * dd z2 - star (dd z2) * dd z3 + star (dd z5) * dd z4
      + star (dd z4) * dd z5 - star (dd z7) * dd z6 - star (dd z6) * dd z7 + star (dd z9) * dd z8
      + star (dd z8) * dd z9 - star (dd z11) * dd z10 - star (dd z10) * dd z11 + star (dd z13) * dd z12
      + star (dd z12) * dd z13 - star (dd z15) * dd z14 - star (dd z14) * dd z15
      + star (dd z17) * dd z16
      + star (dd z16) * dd z17 - star (dd z19) * dd z18 - star (dd z18) * dd z19 := by
  unfold diagTop
  rw [dincT_p2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfT_p2_0, dfT_p2_1, dfT_p2_2, dfT_p2_3, dfT_p2_4, dfT_p2_5, dfT_p2_6, dfT_p2_7, dfT_p2_8, dfT_p2_9, dfT_p2_10, dfT_p2_11, dfT_p2_12, dfT_p2_13, dfT_p2_14, dfT_p2_15, dfT_p2_16, dfT_p2_17, dfT_p2_18, dfT_p2_19]
  simp only [dsT_p2_w1_0, dsT_p2_w1_1, dsT_p2_w1_2, dsT_p2_w1_3, dsT_p2_w1_4, dsT_p2_w1_5, dsT_p2_w1_6, dsT_p2_w1_7, dsT_p2_w1_8, dsT_p2_w1_9, dsT_p2_w1_10, dsT_p2_w1_11, dsT_p2_w1_12, dsT_p2_w1_13, dsT_p2_w1_14, dsT_p2_w1_15, dsT_p2_w1_16, dsT_p2_w1_17, dsT_p2_w1_18, dsT_p2_w1_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem dsB_p2_w2_0 : SS.bdot w2 y0 = false := by decide
theorem dsB_p2_w2_1 : SS.bdot w2 y1 = true := by decide
theorem dsB_p2_w2_2 : SS.bdot w2 y2 = false := by decide
theorem dsB_p2_w2_3 : SS.bdot w2 y3 = true := by decide
theorem dsB_p2_w2_4 : SS.bdot w2 y4 = false := by decide
theorem dsB_p2_w2_5 : SS.bdot w2 y5 = true := by decide
theorem dsB_p2_w2_6 : SS.bdot w2 y6 = false := by decide
theorem dsB_p2_w2_7 : SS.bdot w2 y7 = true := by decide
theorem dsB_p2_w2_8 : SS.bdot w2 y8 = false := by decide
theorem dsB_p2_w2_9 : SS.bdot w2 y9 = true := by decide
theorem dsB_p2_w2_10 : SS.bdot w2 y10 = false := by decide
theorem dsB_p2_w2_11 : SS.bdot w2 y11 = true := by decide
theorem dsB_p2_w2_12 : SS.bdot w2 y12 = false := by decide
theorem dsB_p2_w2_13 : SS.bdot w2 y13 = true := by decide
theorem dsB_p2_w2_14 : SS.bdot w2 y14 = false := by decide
theorem dsB_p2_w2_15 : SS.bdot w2 y15 = true := by decide
theorem dsB_p2_w2_16 : SS.bdot w2 y16 = false := by decide
theorem dsB_p2_w2_17 : SS.bdot w2 y17 = true := by decide
theorem dsB_p2_w2_18 : SS.bdot w2 y18 = false := by decide
theorem dsB_p2_w2_19 : SS.bdot w2 y19 = true := by decide
theorem dexB_p2_w2 (c : SS.BitString 6 -> ℂ) :
    diagBot c p2 w2 = star (c y1) * c y0 - star (c y0) * c y1 + star (c y3) * c y2 - star (c y2) * c y3
      + star (c y5) * c y4 - star (c y4) * c y5 + star (c y7) * c y6 - star (c y6) * c y7
      + star (c y9) * c y8 - star (c y8) * c y9 + star (c y11) * c y10 - star (c y10) * c y11
      + star (c y13) * c y12 - star (c y12) * c y13 + star (c y15) * c y14 - star (c y14) * c y15
      + star (c y17) * c y16 - star (c y16) * c y17 + star (c y19) * c y18 - star (c y18) * c y19 := by
  unfold diagBot
  rw [dincB_p2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfB_p2_0, dfB_p2_1, dfB_p2_2, dfB_p2_3, dfB_p2_4, dfB_p2_5, dfB_p2_6, dfB_p2_7, dfB_p2_8, dfB_p2_9, dfB_p2_10, dfB_p2_11, dfB_p2_12, dfB_p2_13, dfB_p2_14, dfB_p2_15, dfB_p2_16, dfB_p2_17, dfB_p2_18, dfB_p2_19]
  simp only [dsB_p2_w2_0, dsB_p2_w2_1, dsB_p2_w2_2, dsB_p2_w2_3, dsB_p2_w2_4, dsB_p2_w2_5, dsB_p2_w2_6, dsB_p2_w2_7, dsB_p2_w2_8, dsB_p2_w2_9, dsB_p2_w2_10, dsB_p2_w2_11, dsB_p2_w2_12, dsB_p2_w2_13, dsB_p2_w2_14, dsB_p2_w2_15, dsB_p2_w2_16, dsB_p2_w2_17, dsB_p2_w2_18, dsB_p2_w2_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem dsT_p2_w2_0 : SS.bdot w2 z0 = false := by decide
theorem dsT_p2_w2_1 : SS.bdot w2 z1 = true := by decide
theorem dsT_p2_w2_2 : SS.bdot w2 z2 = false := by decide
theorem dsT_p2_w2_3 : SS.bdot w2 z3 = true := by decide
theorem dsT_p2_w2_4 : SS.bdot w2 z4 = false := by decide
theorem dsT_p2_w2_5 : SS.bdot w2 z5 = true := by decide
theorem dsT_p2_w2_6 : SS.bdot w2 z6 = false := by decide
theorem dsT_p2_w2_7 : SS.bdot w2 z7 = true := by decide
theorem dsT_p2_w2_8 : SS.bdot w2 z8 = false := by decide
theorem dsT_p2_w2_9 : SS.bdot w2 z9 = true := by decide
theorem dsT_p2_w2_10 : SS.bdot w2 z10 = false := by decide
theorem dsT_p2_w2_11 : SS.bdot w2 z11 = true := by decide
theorem dsT_p2_w2_12 : SS.bdot w2 z12 = false := by decide
theorem dsT_p2_w2_13 : SS.bdot w2 z13 = true := by decide
theorem dsT_p2_w2_14 : SS.bdot w2 z14 = false := by decide
theorem dsT_p2_w2_15 : SS.bdot w2 z15 = true := by decide
theorem dsT_p2_w2_16 : SS.bdot w2 z16 = false := by decide
theorem dsT_p2_w2_17 : SS.bdot w2 z17 = true := by decide
theorem dsT_p2_w2_18 : SS.bdot w2 z18 = false := by decide
theorem dsT_p2_w2_19 : SS.bdot w2 z19 = true := by decide
theorem dexT_p2_w2 (dd : SS.BitString 6 -> ℂ) :
    diagTop dd p2 w2 = star (dd z1) * dd z0 - star (dd z0) * dd z1
      + star (dd z3) * dd z2 - star (dd z2) * dd z3 + star (dd z5) * dd z4 - star (dd z4) * dd z5
      + star (dd z7) * dd z6 - star (dd z6) * dd z7 + star (dd z9) * dd z8 - star (dd z8) * dd z9
      + star (dd z11) * dd z10 - star (dd z10) * dd z11
      + star (dd z13) * dd z12 - star (dd z12) * dd z13
      + star (dd z15) * dd z14 - star (dd z14) * dd z15
      + star (dd z17) * dd z16 - star (dd z16) * dd z17
      + star (dd z19) * dd z18 - star (dd z18) * dd z19 := by
  unfold diagTop
  rw [dincT_p2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfT_p2_0, dfT_p2_1, dfT_p2_2, dfT_p2_3, dfT_p2_4, dfT_p2_5, dfT_p2_6, dfT_p2_7, dfT_p2_8, dfT_p2_9, dfT_p2_10, dfT_p2_11, dfT_p2_12, dfT_p2_13, dfT_p2_14, dfT_p2_15, dfT_p2_16, dfT_p2_17, dfT_p2_18, dfT_p2_19]
  simp only [dsT_p2_w2_0, dsT_p2_w2_1, dsT_p2_w2_2, dsT_p2_w2_3, dsT_p2_w2_4, dsT_p2_w2_5, dsT_p2_w2_6, dsT_p2_w2_7, dsT_p2_w2_8, dsT_p2_w2_9, dsT_p2_w2_10, dsT_p2_w2_11, dsT_p2_w2_12, dsT_p2_w2_13, dsT_p2_w2_14, dsT_p2_w2_15, dsT_p2_w2_16, dsT_p2_w2_17, dsT_p2_w2_18, dsT_p2_w2_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem dsB_p2_w3_0 : SS.bdot w3 y0 = false := by decide
theorem dsB_p2_w3_1 : SS.bdot w3 y1 = true := by decide
theorem dsB_p2_w3_2 : SS.bdot w3 y2 = true := by decide
theorem dsB_p2_w3_3 : SS.bdot w3 y3 = false := by decide
theorem dsB_p2_w3_4 : SS.bdot w3 y4 = false := by decide
theorem dsB_p2_w3_5 : SS.bdot w3 y5 = true := by decide
theorem dsB_p2_w3_6 : SS.bdot w3 y6 = true := by decide
theorem dsB_p2_w3_7 : SS.bdot w3 y7 = false := by decide
theorem dsB_p2_w3_8 : SS.bdot w3 y8 = false := by decide
theorem dsB_p2_w3_9 : SS.bdot w3 y9 = true := by decide
theorem dsB_p2_w3_10 : SS.bdot w3 y10 = true := by decide
theorem dsB_p2_w3_11 : SS.bdot w3 y11 = false := by decide
theorem dsB_p2_w3_12 : SS.bdot w3 y12 = false := by decide
theorem dsB_p2_w3_13 : SS.bdot w3 y13 = true := by decide
theorem dsB_p2_w3_14 : SS.bdot w3 y14 = true := by decide
theorem dsB_p2_w3_15 : SS.bdot w3 y15 = false := by decide
theorem dsB_p2_w3_16 : SS.bdot w3 y16 = false := by decide
theorem dsB_p2_w3_17 : SS.bdot w3 y17 = true := by decide
theorem dsB_p2_w3_18 : SS.bdot w3 y18 = true := by decide
theorem dsB_p2_w3_19 : SS.bdot w3 y19 = false := by decide
theorem dexB_p2_w3 (c : SS.BitString 6 -> ℂ) :
    diagBot c p2 w3 = star (c y1) * c y0 - star (c y0) * c y1 - star (c y3) * c y2 + star (c y2) * c y3
      + star (c y5) * c y4 - star (c y4) * c y5 - star (c y7) * c y6 + star (c y6) * c y7
      + star (c y9) * c y8 - star (c y8) * c y9 - star (c y11) * c y10 + star (c y10) * c y11
      + star (c y13) * c y12 - star (c y12) * c y13 - star (c y15) * c y14 + star (c y14) * c y15
      + star (c y17) * c y16 - star (c y16) * c y17 - star (c y19) * c y18 + star (c y18) * c y19 := by
  unfold diagBot
  rw [dincB_p2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfB_p2_0, dfB_p2_1, dfB_p2_2, dfB_p2_3, dfB_p2_4, dfB_p2_5, dfB_p2_6, dfB_p2_7, dfB_p2_8, dfB_p2_9, dfB_p2_10, dfB_p2_11, dfB_p2_12, dfB_p2_13, dfB_p2_14, dfB_p2_15, dfB_p2_16, dfB_p2_17, dfB_p2_18, dfB_p2_19]
  simp only [dsB_p2_w3_0, dsB_p2_w3_1, dsB_p2_w3_2, dsB_p2_w3_3, dsB_p2_w3_4, dsB_p2_w3_5, dsB_p2_w3_6, dsB_p2_w3_7, dsB_p2_w3_8, dsB_p2_w3_9, dsB_p2_w3_10, dsB_p2_w3_11, dsB_p2_w3_12, dsB_p2_w3_13, dsB_p2_w3_14, dsB_p2_w3_15, dsB_p2_w3_16, dsB_p2_w3_17, dsB_p2_w3_18, dsB_p2_w3_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem dsT_p2_w3_0 : SS.bdot w3 z0 = false := by decide
theorem dsT_p2_w3_1 : SS.bdot w3 z1 = true := by decide
theorem dsT_p2_w3_2 : SS.bdot w3 z2 = true := by decide
theorem dsT_p2_w3_3 : SS.bdot w3 z3 = false := by decide
theorem dsT_p2_w3_4 : SS.bdot w3 z4 = false := by decide
theorem dsT_p2_w3_5 : SS.bdot w3 z5 = true := by decide
theorem dsT_p2_w3_6 : SS.bdot w3 z6 = true := by decide
theorem dsT_p2_w3_7 : SS.bdot w3 z7 = false := by decide
theorem dsT_p2_w3_8 : SS.bdot w3 z8 = false := by decide
theorem dsT_p2_w3_9 : SS.bdot w3 z9 = true := by decide
theorem dsT_p2_w3_10 : SS.bdot w3 z10 = true := by decide
theorem dsT_p2_w3_11 : SS.bdot w3 z11 = false := by decide
theorem dsT_p2_w3_12 : SS.bdot w3 z12 = false := by decide
theorem dsT_p2_w3_13 : SS.bdot w3 z13 = true := by decide
theorem dsT_p2_w3_14 : SS.bdot w3 z14 = true := by decide
theorem dsT_p2_w3_15 : SS.bdot w3 z15 = false := by decide
theorem dsT_p2_w3_16 : SS.bdot w3 z16 = false := by decide
theorem dsT_p2_w3_17 : SS.bdot w3 z17 = true := by decide
theorem dsT_p2_w3_18 : SS.bdot w3 z18 = true := by decide
theorem dsT_p2_w3_19 : SS.bdot w3 z19 = false := by decide
theorem dexT_p2_w3 (dd : SS.BitString 6 -> ℂ) :
    diagTop dd p2 w3 = star (dd z1) * dd z0 - star (dd z0) * dd z1 - star (dd z3) * dd z2
      + star (dd z2) * dd z3 + star (dd z5) * dd z4 - star (dd z4) * dd z5 - star (dd z7) * dd z6
      + star (dd z6) * dd z7 + star (dd z9) * dd z8 - star (dd z8) * dd z9 - star (dd z11) * dd z10
      + star (dd z10) * dd z11
      + star (dd z13) * dd z12 - star (dd z12) * dd z13 - star (dd z15) * dd z14
      + star (dd z14) * dd z15
      + star (dd z17) * dd z16 - star (dd z16) * dd z17 - star (dd z19) * dd z18
      + star (dd z18) * dd z19 := by
  unfold diagTop
  rw [dincT_p2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfT_p2_0, dfT_p2_1, dfT_p2_2, dfT_p2_3, dfT_p2_4, dfT_p2_5, dfT_p2_6, dfT_p2_7, dfT_p2_8, dfT_p2_9, dfT_p2_10, dfT_p2_11, dfT_p2_12, dfT_p2_13, dfT_p2_14, dfT_p2_15, dfT_p2_16, dfT_p2_17, dfT_p2_18, dfT_p2_19]
  simp only [dsT_p2_w3_0, dsT_p2_w3_1, dsT_p2_w3_2, dsT_p2_w3_3, dsT_p2_w3_4, dsT_p2_w3_5, dsT_p2_w3_6, dsT_p2_w3_7, dsT_p2_w3_8, dsT_p2_w3_9, dsT_p2_w3_10, dsT_p2_w3_11, dsT_p2_w3_12, dsT_p2_w3_13, dsT_p2_w3_14, dsT_p2_w3_15, dsT_p2_w3_16, dsT_p2_w3_17, dsT_p2_w3_18, dsT_p2_w3_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem dsB_p3_w0_0 : SS.bdot w0 y0 = false := by decide
theorem dsB_p3_w0_1 : SS.bdot w0 y1 = false := by decide
theorem dsB_p3_w0_2 : SS.bdot w0 y2 = false := by decide
theorem dsB_p3_w0_3 : SS.bdot w0 y3 = false := by decide
theorem dsB_p3_w0_4 : SS.bdot w0 y4 = false := by decide
theorem dsB_p3_w0_5 : SS.bdot w0 y5 = false := by decide
theorem dsB_p3_w0_6 : SS.bdot w0 y6 = false := by decide
theorem dsB_p3_w0_7 : SS.bdot w0 y7 = false := by decide
theorem dsB_p3_w0_8 : SS.bdot w0 y8 = false := by decide
theorem dsB_p3_w0_9 : SS.bdot w0 y9 = false := by decide
theorem dsB_p3_w0_10 : SS.bdot w0 y10 = false := by decide
theorem dsB_p3_w0_11 : SS.bdot w0 y11 = false := by decide
theorem dsB_p3_w0_12 : SS.bdot w0 y12 = false := by decide
theorem dsB_p3_w0_13 : SS.bdot w0 y13 = false := by decide
theorem dsB_p3_w0_14 : SS.bdot w0 y14 = false := by decide
theorem dsB_p3_w0_15 : SS.bdot w0 y15 = false := by decide
theorem dsB_p3_w0_16 : SS.bdot w0 y16 = false := by decide
theorem dsB_p3_w0_17 : SS.bdot w0 y17 = false := by decide
theorem dsB_p3_w0_18 : SS.bdot w0 y18 = false := by decide
theorem dsB_p3_w0_19 : SS.bdot w0 y19 = false := by decide
theorem dexB_p3_w0 (c : SS.BitString 6 -> ℂ) :
    diagBot c p3 w0 = star (c y3) * c y0 + star (c y2) * c y1 + star (c y1) * c y2 + star (c y0) * c y3
      + star (c y7) * c y4 + star (c y6) * c y5 + star (c y5) * c y6 + star (c y4) * c y7
      + star (c y11) * c y8 + star (c y10) * c y9 + star (c y9) * c y10 + star (c y8) * c y11
      + star (c y15) * c y12 + star (c y14) * c y13 + star (c y13) * c y14 + star (c y12) * c y15
      + star (c y19) * c y16 + star (c y18) * c y17 + star (c y17) * c y18 + star (c y16) * c y19 := by
  unfold diagBot
  rw [dincB_p3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfB_p3_0, dfB_p3_1, dfB_p3_2, dfB_p3_3, dfB_p3_4, dfB_p3_5, dfB_p3_6, dfB_p3_7, dfB_p3_8, dfB_p3_9, dfB_p3_10, dfB_p3_11, dfB_p3_12, dfB_p3_13, dfB_p3_14, dfB_p3_15, dfB_p3_16, dfB_p3_17, dfB_p3_18, dfB_p3_19]
  simp only [dsB_p3_w0_0, dsB_p3_w0_1, dsB_p3_w0_2, dsB_p3_w0_3, dsB_p3_w0_4, dsB_p3_w0_5, dsB_p3_w0_6, dsB_p3_w0_7, dsB_p3_w0_8, dsB_p3_w0_9, dsB_p3_w0_10, dsB_p3_w0_11, dsB_p3_w0_12, dsB_p3_w0_13, dsB_p3_w0_14, dsB_p3_w0_15, dsB_p3_w0_16, dsB_p3_w0_17, dsB_p3_w0_18, dsB_p3_w0_19, SixQubit.signMul_false]
  try ring
theorem dsT_p3_w0_0 : SS.bdot w0 z0 = false := by decide
theorem dsT_p3_w0_1 : SS.bdot w0 z1 = false := by decide
theorem dsT_p3_w0_2 : SS.bdot w0 z2 = false := by decide
theorem dsT_p3_w0_3 : SS.bdot w0 z3 = false := by decide
theorem dsT_p3_w0_4 : SS.bdot w0 z4 = false := by decide
theorem dsT_p3_w0_5 : SS.bdot w0 z5 = false := by decide
theorem dsT_p3_w0_6 : SS.bdot w0 z6 = false := by decide
theorem dsT_p3_w0_7 : SS.bdot w0 z7 = false := by decide
theorem dsT_p3_w0_8 : SS.bdot w0 z8 = false := by decide
theorem dsT_p3_w0_9 : SS.bdot w0 z9 = false := by decide
theorem dsT_p3_w0_10 : SS.bdot w0 z10 = false := by decide
theorem dsT_p3_w0_11 : SS.bdot w0 z11 = false := by decide
theorem dsT_p3_w0_12 : SS.bdot w0 z12 = false := by decide
theorem dsT_p3_w0_13 : SS.bdot w0 z13 = false := by decide
theorem dsT_p3_w0_14 : SS.bdot w0 z14 = false := by decide
theorem dsT_p3_w0_15 : SS.bdot w0 z15 = false := by decide
theorem dsT_p3_w0_16 : SS.bdot w0 z16 = false := by decide
theorem dsT_p3_w0_17 : SS.bdot w0 z17 = false := by decide
theorem dsT_p3_w0_18 : SS.bdot w0 z18 = false := by decide
theorem dsT_p3_w0_19 : SS.bdot w0 z19 = false := by decide
theorem dexT_p3_w0 (dd : SS.BitString 6 -> ℂ) :
    diagTop dd p3 w0 = star (dd z3) * dd z0 + star (dd z2) * dd z1 + star (dd z1) * dd z2
      + star (dd z0) * dd z3 + star (dd z7) * dd z4 + star (dd z6) * dd z5 + star (dd z5) * dd z6
      + star (dd z4) * dd z7 + star (dd z11) * dd z8 + star (dd z10) * dd z9 + star (dd z9) * dd z10
      + star (dd z8) * dd z11 + star (dd z15) * dd z12 + star (dd z14) * dd z13 + star (dd z13) * dd z14
      + star (dd z12) * dd z15 + star (dd z19) * dd z16 + star (dd z18) * dd z17
      + star (dd z17) * dd z18 + star (dd z16) * dd z19 := by
  unfold diagTop
  rw [dincT_p3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfT_p3_0, dfT_p3_1, dfT_p3_2, dfT_p3_3, dfT_p3_4, dfT_p3_5, dfT_p3_6, dfT_p3_7, dfT_p3_8, dfT_p3_9, dfT_p3_10, dfT_p3_11, dfT_p3_12, dfT_p3_13, dfT_p3_14, dfT_p3_15, dfT_p3_16, dfT_p3_17, dfT_p3_18, dfT_p3_19]
  simp only [dsT_p3_w0_0, dsT_p3_w0_1, dsT_p3_w0_2, dsT_p3_w0_3, dsT_p3_w0_4, dsT_p3_w0_5, dsT_p3_w0_6, dsT_p3_w0_7, dsT_p3_w0_8, dsT_p3_w0_9, dsT_p3_w0_10, dsT_p3_w0_11, dsT_p3_w0_12, dsT_p3_w0_13, dsT_p3_w0_14, dsT_p3_w0_15, dsT_p3_w0_16, dsT_p3_w0_17, dsT_p3_w0_18, dsT_p3_w0_19, SixQubit.signMul_false]
  try ring
theorem dsB_p3_w1_0 : SS.bdot w1 y0 = false := by decide
theorem dsB_p3_w1_1 : SS.bdot w1 y1 = false := by decide
theorem dsB_p3_w1_2 : SS.bdot w1 y2 = true := by decide
theorem dsB_p3_w1_3 : SS.bdot w1 y3 = true := by decide
theorem dsB_p3_w1_4 : SS.bdot w1 y4 = false := by decide
theorem dsB_p3_w1_5 : SS.bdot w1 y5 = false := by decide
theorem dsB_p3_w1_6 : SS.bdot w1 y6 = true := by decide
theorem dsB_p3_w1_7 : SS.bdot w1 y7 = true := by decide
theorem dsB_p3_w1_8 : SS.bdot w1 y8 = false := by decide
theorem dsB_p3_w1_9 : SS.bdot w1 y9 = false := by decide
theorem dsB_p3_w1_10 : SS.bdot w1 y10 = true := by decide
theorem dsB_p3_w1_11 : SS.bdot w1 y11 = true := by decide
theorem dsB_p3_w1_12 : SS.bdot w1 y12 = false := by decide
theorem dsB_p3_w1_13 : SS.bdot w1 y13 = false := by decide
theorem dsB_p3_w1_14 : SS.bdot w1 y14 = true := by decide
theorem dsB_p3_w1_15 : SS.bdot w1 y15 = true := by decide
theorem dsB_p3_w1_16 : SS.bdot w1 y16 = false := by decide
theorem dsB_p3_w1_17 : SS.bdot w1 y17 = false := by decide
theorem dsB_p3_w1_18 : SS.bdot w1 y18 = true := by decide
theorem dsB_p3_w1_19 : SS.bdot w1 y19 = true := by decide
theorem dexB_p3_w1 (c : SS.BitString 6 -> ℂ) :
    diagBot c p3 w1 = star (c y3) * c y0 + star (c y2) * c y1 - star (c y1) * c y2 - star (c y0) * c y3
      + star (c y7) * c y4 + star (c y6) * c y5 - star (c y5) * c y6 - star (c y4) * c y7
      + star (c y11) * c y8 + star (c y10) * c y9 - star (c y9) * c y10 - star (c y8) * c y11
      + star (c y15) * c y12 + star (c y14) * c y13 - star (c y13) * c y14 - star (c y12) * c y15
      + star (c y19) * c y16 + star (c y18) * c y17 - star (c y17) * c y18 - star (c y16) * c y19 := by
  unfold diagBot
  rw [dincB_p3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfB_p3_0, dfB_p3_1, dfB_p3_2, dfB_p3_3, dfB_p3_4, dfB_p3_5, dfB_p3_6, dfB_p3_7, dfB_p3_8, dfB_p3_9, dfB_p3_10, dfB_p3_11, dfB_p3_12, dfB_p3_13, dfB_p3_14, dfB_p3_15, dfB_p3_16, dfB_p3_17, dfB_p3_18, dfB_p3_19]
  simp only [dsB_p3_w1_0, dsB_p3_w1_1, dsB_p3_w1_2, dsB_p3_w1_3, dsB_p3_w1_4, dsB_p3_w1_5, dsB_p3_w1_6, dsB_p3_w1_7, dsB_p3_w1_8, dsB_p3_w1_9, dsB_p3_w1_10, dsB_p3_w1_11, dsB_p3_w1_12, dsB_p3_w1_13, dsB_p3_w1_14, dsB_p3_w1_15, dsB_p3_w1_16, dsB_p3_w1_17, dsB_p3_w1_18, dsB_p3_w1_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem dsT_p3_w1_0 : SS.bdot w1 z0 = false := by decide
theorem dsT_p3_w1_1 : SS.bdot w1 z1 = false := by decide
theorem dsT_p3_w1_2 : SS.bdot w1 z2 = true := by decide
theorem dsT_p3_w1_3 : SS.bdot w1 z3 = true := by decide
theorem dsT_p3_w1_4 : SS.bdot w1 z4 = false := by decide
theorem dsT_p3_w1_5 : SS.bdot w1 z5 = false := by decide
theorem dsT_p3_w1_6 : SS.bdot w1 z6 = true := by decide
theorem dsT_p3_w1_7 : SS.bdot w1 z7 = true := by decide
theorem dsT_p3_w1_8 : SS.bdot w1 z8 = false := by decide
theorem dsT_p3_w1_9 : SS.bdot w1 z9 = false := by decide
theorem dsT_p3_w1_10 : SS.bdot w1 z10 = true := by decide
theorem dsT_p3_w1_11 : SS.bdot w1 z11 = true := by decide
theorem dsT_p3_w1_12 : SS.bdot w1 z12 = false := by decide
theorem dsT_p3_w1_13 : SS.bdot w1 z13 = false := by decide
theorem dsT_p3_w1_14 : SS.bdot w1 z14 = true := by decide
theorem dsT_p3_w1_15 : SS.bdot w1 z15 = true := by decide
theorem dsT_p3_w1_16 : SS.bdot w1 z16 = false := by decide
theorem dsT_p3_w1_17 : SS.bdot w1 z17 = false := by decide
theorem dsT_p3_w1_18 : SS.bdot w1 z18 = true := by decide
theorem dsT_p3_w1_19 : SS.bdot w1 z19 = true := by decide
theorem dexT_p3_w1 (dd : SS.BitString 6 -> ℂ) :
    diagTop dd p3 w1 = star (dd z3) * dd z0
      + star (dd z2) * dd z1 - star (dd z1) * dd z2 - star (dd z0) * dd z3 + star (dd z7) * dd z4
      + star (dd z6) * dd z5 - star (dd z5) * dd z6 - star (dd z4) * dd z7 + star (dd z11) * dd z8
      + star (dd z10) * dd z9 - star (dd z9) * dd z10 - star (dd z8) * dd z11 + star (dd z15) * dd z12
      + star (dd z14) * dd z13 - star (dd z13) * dd z14 - star (dd z12) * dd z15
      + star (dd z19) * dd z16
      + star (dd z18) * dd z17 - star (dd z17) * dd z18 - star (dd z16) * dd z19 := by
  unfold diagTop
  rw [dincT_p3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfT_p3_0, dfT_p3_1, dfT_p3_2, dfT_p3_3, dfT_p3_4, dfT_p3_5, dfT_p3_6, dfT_p3_7, dfT_p3_8, dfT_p3_9, dfT_p3_10, dfT_p3_11, dfT_p3_12, dfT_p3_13, dfT_p3_14, dfT_p3_15, dfT_p3_16, dfT_p3_17, dfT_p3_18, dfT_p3_19]
  simp only [dsT_p3_w1_0, dsT_p3_w1_1, dsT_p3_w1_2, dsT_p3_w1_3, dsT_p3_w1_4, dsT_p3_w1_5, dsT_p3_w1_6, dsT_p3_w1_7, dsT_p3_w1_8, dsT_p3_w1_9, dsT_p3_w1_10, dsT_p3_w1_11, dsT_p3_w1_12, dsT_p3_w1_13, dsT_p3_w1_14, dsT_p3_w1_15, dsT_p3_w1_16, dsT_p3_w1_17, dsT_p3_w1_18, dsT_p3_w1_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem dsB_p3_w2_0 : SS.bdot w2 y0 = false := by decide
theorem dsB_p3_w2_1 : SS.bdot w2 y1 = true := by decide
theorem dsB_p3_w2_2 : SS.bdot w2 y2 = false := by decide
theorem dsB_p3_w2_3 : SS.bdot w2 y3 = true := by decide
theorem dsB_p3_w2_4 : SS.bdot w2 y4 = false := by decide
theorem dsB_p3_w2_5 : SS.bdot w2 y5 = true := by decide
theorem dsB_p3_w2_6 : SS.bdot w2 y6 = false := by decide
theorem dsB_p3_w2_7 : SS.bdot w2 y7 = true := by decide
theorem dsB_p3_w2_8 : SS.bdot w2 y8 = false := by decide
theorem dsB_p3_w2_9 : SS.bdot w2 y9 = true := by decide
theorem dsB_p3_w2_10 : SS.bdot w2 y10 = false := by decide
theorem dsB_p3_w2_11 : SS.bdot w2 y11 = true := by decide
theorem dsB_p3_w2_12 : SS.bdot w2 y12 = false := by decide
theorem dsB_p3_w2_13 : SS.bdot w2 y13 = true := by decide
theorem dsB_p3_w2_14 : SS.bdot w2 y14 = false := by decide
theorem dsB_p3_w2_15 : SS.bdot w2 y15 = true := by decide
theorem dsB_p3_w2_16 : SS.bdot w2 y16 = false := by decide
theorem dsB_p3_w2_17 : SS.bdot w2 y17 = true := by decide
theorem dsB_p3_w2_18 : SS.bdot w2 y18 = false := by decide
theorem dsB_p3_w2_19 : SS.bdot w2 y19 = true := by decide
theorem dexB_p3_w2 (c : SS.BitString 6 -> ℂ) :
    diagBot c p3 w2 = star (c y3) * c y0 - star (c y2) * c y1 + star (c y1) * c y2 - star (c y0) * c y3
      + star (c y7) * c y4 - star (c y6) * c y5 + star (c y5) * c y6 - star (c y4) * c y7
      + star (c y11) * c y8 - star (c y10) * c y9 + star (c y9) * c y10 - star (c y8) * c y11
      + star (c y15) * c y12 - star (c y14) * c y13 + star (c y13) * c y14 - star (c y12) * c y15
      + star (c y19) * c y16 - star (c y18) * c y17 + star (c y17) * c y18 - star (c y16) * c y19 := by
  unfold diagBot
  rw [dincB_p3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfB_p3_0, dfB_p3_1, dfB_p3_2, dfB_p3_3, dfB_p3_4, dfB_p3_5, dfB_p3_6, dfB_p3_7, dfB_p3_8, dfB_p3_9, dfB_p3_10, dfB_p3_11, dfB_p3_12, dfB_p3_13, dfB_p3_14, dfB_p3_15, dfB_p3_16, dfB_p3_17, dfB_p3_18, dfB_p3_19]
  simp only [dsB_p3_w2_0, dsB_p3_w2_1, dsB_p3_w2_2, dsB_p3_w2_3, dsB_p3_w2_4, dsB_p3_w2_5, dsB_p3_w2_6, dsB_p3_w2_7, dsB_p3_w2_8, dsB_p3_w2_9, dsB_p3_w2_10, dsB_p3_w2_11, dsB_p3_w2_12, dsB_p3_w2_13, dsB_p3_w2_14, dsB_p3_w2_15, dsB_p3_w2_16, dsB_p3_w2_17, dsB_p3_w2_18, dsB_p3_w2_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem dsT_p3_w2_0 : SS.bdot w2 z0 = false := by decide
theorem dsT_p3_w2_1 : SS.bdot w2 z1 = true := by decide
theorem dsT_p3_w2_2 : SS.bdot w2 z2 = false := by decide
theorem dsT_p3_w2_3 : SS.bdot w2 z3 = true := by decide
theorem dsT_p3_w2_4 : SS.bdot w2 z4 = false := by decide
theorem dsT_p3_w2_5 : SS.bdot w2 z5 = true := by decide
theorem dsT_p3_w2_6 : SS.bdot w2 z6 = false := by decide
theorem dsT_p3_w2_7 : SS.bdot w2 z7 = true := by decide
theorem dsT_p3_w2_8 : SS.bdot w2 z8 = false := by decide
theorem dsT_p3_w2_9 : SS.bdot w2 z9 = true := by decide
theorem dsT_p3_w2_10 : SS.bdot w2 z10 = false := by decide
theorem dsT_p3_w2_11 : SS.bdot w2 z11 = true := by decide
theorem dsT_p3_w2_12 : SS.bdot w2 z12 = false := by decide
theorem dsT_p3_w2_13 : SS.bdot w2 z13 = true := by decide
theorem dsT_p3_w2_14 : SS.bdot w2 z14 = false := by decide
theorem dsT_p3_w2_15 : SS.bdot w2 z15 = true := by decide
theorem dsT_p3_w2_16 : SS.bdot w2 z16 = false := by decide
theorem dsT_p3_w2_17 : SS.bdot w2 z17 = true := by decide
theorem dsT_p3_w2_18 : SS.bdot w2 z18 = false := by decide
theorem dsT_p3_w2_19 : SS.bdot w2 z19 = true := by decide
theorem dexT_p3_w2 (dd : SS.BitString 6 -> ℂ) :
    diagTop dd p3 w2 = star (dd z3) * dd z0 - star (dd z2) * dd z1
      + star (dd z1) * dd z2 - star (dd z0) * dd z3 + star (dd z7) * dd z4 - star (dd z6) * dd z5
      + star (dd z5) * dd z6 - star (dd z4) * dd z7 + star (dd z11) * dd z8 - star (dd z10) * dd z9
      + star (dd z9) * dd z10 - star (dd z8) * dd z11 + star (dd z15) * dd z12 - star (dd z14) * dd z13
      + star (dd z13) * dd z14 - star (dd z12) * dd z15
      + star (dd z19) * dd z16 - star (dd z18) * dd z17
      + star (dd z17) * dd z18 - star (dd z16) * dd z19 := by
  unfold diagTop
  rw [dincT_p3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfT_p3_0, dfT_p3_1, dfT_p3_2, dfT_p3_3, dfT_p3_4, dfT_p3_5, dfT_p3_6, dfT_p3_7, dfT_p3_8, dfT_p3_9, dfT_p3_10, dfT_p3_11, dfT_p3_12, dfT_p3_13, dfT_p3_14, dfT_p3_15, dfT_p3_16, dfT_p3_17, dfT_p3_18, dfT_p3_19]
  simp only [dsT_p3_w2_0, dsT_p3_w2_1, dsT_p3_w2_2, dsT_p3_w2_3, dsT_p3_w2_4, dsT_p3_w2_5, dsT_p3_w2_6, dsT_p3_w2_7, dsT_p3_w2_8, dsT_p3_w2_9, dsT_p3_w2_10, dsT_p3_w2_11, dsT_p3_w2_12, dsT_p3_w2_13, dsT_p3_w2_14, dsT_p3_w2_15, dsT_p3_w2_16, dsT_p3_w2_17, dsT_p3_w2_18, dsT_p3_w2_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem dsB_p3_w3_0 : SS.bdot w3 y0 = false := by decide
theorem dsB_p3_w3_1 : SS.bdot w3 y1 = true := by decide
theorem dsB_p3_w3_2 : SS.bdot w3 y2 = true := by decide
theorem dsB_p3_w3_3 : SS.bdot w3 y3 = false := by decide
theorem dsB_p3_w3_4 : SS.bdot w3 y4 = false := by decide
theorem dsB_p3_w3_5 : SS.bdot w3 y5 = true := by decide
theorem dsB_p3_w3_6 : SS.bdot w3 y6 = true := by decide
theorem dsB_p3_w3_7 : SS.bdot w3 y7 = false := by decide
theorem dsB_p3_w3_8 : SS.bdot w3 y8 = false := by decide
theorem dsB_p3_w3_9 : SS.bdot w3 y9 = true := by decide
theorem dsB_p3_w3_10 : SS.bdot w3 y10 = true := by decide
theorem dsB_p3_w3_11 : SS.bdot w3 y11 = false := by decide
theorem dsB_p3_w3_12 : SS.bdot w3 y12 = false := by decide
theorem dsB_p3_w3_13 : SS.bdot w3 y13 = true := by decide
theorem dsB_p3_w3_14 : SS.bdot w3 y14 = true := by decide
theorem dsB_p3_w3_15 : SS.bdot w3 y15 = false := by decide
theorem dsB_p3_w3_16 : SS.bdot w3 y16 = false := by decide
theorem dsB_p3_w3_17 : SS.bdot w3 y17 = true := by decide
theorem dsB_p3_w3_18 : SS.bdot w3 y18 = true := by decide
theorem dsB_p3_w3_19 : SS.bdot w3 y19 = false := by decide
theorem dexB_p3_w3 (c : SS.BitString 6 -> ℂ) :
    diagBot c p3 w3 = star (c y3) * c y0 - star (c y2) * c y1 - star (c y1) * c y2 + star (c y0) * c y3
      + star (c y7) * c y4 - star (c y6) * c y5 - star (c y5) * c y6 + star (c y4) * c y7
      + star (c y11) * c y8 - star (c y10) * c y9 - star (c y9) * c y10 + star (c y8) * c y11
      + star (c y15) * c y12 - star (c y14) * c y13 - star (c y13) * c y14 + star (c y12) * c y15
      + star (c y19) * c y16 - star (c y18) * c y17 - star (c y17) * c y18 + star (c y16) * c y19 := by
  unfold diagBot
  rw [dincB_p3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfB_p3_0, dfB_p3_1, dfB_p3_2, dfB_p3_3, dfB_p3_4, dfB_p3_5, dfB_p3_6, dfB_p3_7, dfB_p3_8, dfB_p3_9, dfB_p3_10, dfB_p3_11, dfB_p3_12, dfB_p3_13, dfB_p3_14, dfB_p3_15, dfB_p3_16, dfB_p3_17, dfB_p3_18, dfB_p3_19]
  simp only [dsB_p3_w3_0, dsB_p3_w3_1, dsB_p3_w3_2, dsB_p3_w3_3, dsB_p3_w3_4, dsB_p3_w3_5, dsB_p3_w3_6, dsB_p3_w3_7, dsB_p3_w3_8, dsB_p3_w3_9, dsB_p3_w3_10, dsB_p3_w3_11, dsB_p3_w3_12, dsB_p3_w3_13, dsB_p3_w3_14, dsB_p3_w3_15, dsB_p3_w3_16, dsB_p3_w3_17, dsB_p3_w3_18, dsB_p3_w3_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem dsT_p3_w3_0 : SS.bdot w3 z0 = false := by decide
theorem dsT_p3_w3_1 : SS.bdot w3 z1 = true := by decide
theorem dsT_p3_w3_2 : SS.bdot w3 z2 = true := by decide
theorem dsT_p3_w3_3 : SS.bdot w3 z3 = false := by decide
theorem dsT_p3_w3_4 : SS.bdot w3 z4 = false := by decide
theorem dsT_p3_w3_5 : SS.bdot w3 z5 = true := by decide
theorem dsT_p3_w3_6 : SS.bdot w3 z6 = true := by decide
theorem dsT_p3_w3_7 : SS.bdot w3 z7 = false := by decide
theorem dsT_p3_w3_8 : SS.bdot w3 z8 = false := by decide
theorem dsT_p3_w3_9 : SS.bdot w3 z9 = true := by decide
theorem dsT_p3_w3_10 : SS.bdot w3 z10 = true := by decide
theorem dsT_p3_w3_11 : SS.bdot w3 z11 = false := by decide
theorem dsT_p3_w3_12 : SS.bdot w3 z12 = false := by decide
theorem dsT_p3_w3_13 : SS.bdot w3 z13 = true := by decide
theorem dsT_p3_w3_14 : SS.bdot w3 z14 = true := by decide
theorem dsT_p3_w3_15 : SS.bdot w3 z15 = false := by decide
theorem dsT_p3_w3_16 : SS.bdot w3 z16 = false := by decide
theorem dsT_p3_w3_17 : SS.bdot w3 z17 = true := by decide
theorem dsT_p3_w3_18 : SS.bdot w3 z18 = true := by decide
theorem dsT_p3_w3_19 : SS.bdot w3 z19 = false := by decide
theorem dexT_p3_w3 (dd : SS.BitString 6 -> ℂ) :
    diagTop dd p3 w3 = star (dd z3) * dd z0 - star (dd z2) * dd z1 - star (dd z1) * dd z2
      + star (dd z0) * dd z3 + star (dd z7) * dd z4 - star (dd z6) * dd z5 - star (dd z5) * dd z6
      + star (dd z4) * dd z7 + star (dd z11) * dd z8 - star (dd z10) * dd z9 - star (dd z9) * dd z10
      + star (dd z8) * dd z11 + star (dd z15) * dd z12 - star (dd z14) * dd z13 - star (dd z13) * dd z14
      + star (dd z12) * dd z15
      + star (dd z19) * dd z16 - star (dd z18) * dd z17 - star (dd z17) * dd z18
      + star (dd z16) * dd z19 := by
  unfold diagTop
  rw [dincT_p3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfT_p3_0, dfT_p3_1, dfT_p3_2, dfT_p3_3, dfT_p3_4, dfT_p3_5, dfT_p3_6, dfT_p3_7, dfT_p3_8, dfT_p3_9, dfT_p3_10, dfT_p3_11, dfT_p3_12, dfT_p3_13, dfT_p3_14, dfT_p3_15, dfT_p3_16, dfT_p3_17, dfT_p3_18, dfT_p3_19]
  simp only [dsT_p3_w3_0, dsT_p3_w3_1, dsT_p3_w3_2, dsT_p3_w3_3, dsT_p3_w3_4, dsT_p3_w3_5, dsT_p3_w3_6, dsT_p3_w3_7, dsT_p3_w3_8, dsT_p3_w3_9, dsT_p3_w3_10, dsT_p3_w3_11, dsT_p3_w3_12, dsT_p3_w3_13, dsT_p3_w3_14, dsT_p3_w3_15, dsT_p3_w3_16, dsT_p3_w3_17, dsT_p3_w3_18, dsT_p3_w3_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

/-! ## The moment system -/

/-- The two normalizations, the six one-coordinate and the fifteen
two-coordinate moment equalities, and the nonnegativity of every
probability. -/
structure MomentSystem (q0  q1  q2  q3  q4  q5  q6  q7  q8  q9  q10  q11  q12  q13  q14  q15  q16  q17
     q18  q19  r0  r1  r2  r3  r4  r5  r6  r7  r8  r9  r10  r11  r12  r13  r14  r15  r16  r17  r18  r19 : Real) : Prop where
  n0 : q0 + q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 + q9 + q10 + q11 + q12 + q13 + q14 + q15 + q16 + q17
      + q18 + q19 = 1
  n1 : r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15 + r16 + r17
      + r18 + r19 = 1
  m1 : q2 + q3 + q6 + q7 + q10 + q11 + q14 + q15 + q18 + q19 = r2 + r3 + r6 + r7 + r10 + r11 + r14 + r15
      + r18 + r19
  m2 : q1 + q3 + q5 + q7 + q9 + q11 + q13 + q15 + q17 + q19 = r1 + r3 + r5 + r7 + r9 + r11 + r13 + r15
      + r17 + r19
  m3 : q8 + q9 + q10 + q11 + q12 + q13 + q14 + q15 + q16 + q17 + q18 + q19 = r0 + r1 + r2 + r3 + r16
      + r17 + r18 + r19
  m4 : q4 + q5 + q6 + q7 + q12 + q13 + q14 + q15 + q16 + q17 + q18 + q19 = r4 + r5 + r6 + r7 + r16 + r17
      + r18 + r19
  m5 : q4 + q5 + q6 + q7 + q8 + q9 + q10 + q11 + q16 + q17 + q18 + q19 = r8 + r9 + r10 + r11 + r16 + r17
      + r18 + r19
  m6 : q4 + q5 + q6 + q7 + q8 + q9 + q10 + q11 + q12 + q13 + q14 + q15 = r12 + r13 + r14 + r15 + r16
      + r17 + r18 + r19
  m12 : q3 + q7 + q11 + q15 + q19 = r3 + r7 + r11 + r15 + r19
  m13 : q10 + q11 + q14 + q15 + q18 + q19 = r2 + r3 + r18 + r19
  m14 : q6 + q7 + q14 + q15 + q18 + q19 = r6 + r7 + r18 + r19
  m15 : q6 + q7 + q10 + q11 + q18 + q19 = r10 + r11 + r18 + r19
  m16 : q6 + q7 + q10 + q11 + q14 + q15 = r14 + r15 + r18 + r19
  m23 : q9 + q11 + q13 + q15 + q17 + q19 = r1 + r3 + r17 + r19
  m24 : q5 + q7 + q13 + q15 + q17 + q19 = r5 + r7 + r17 + r19
  m25 : q5 + q7 + q9 + q11 + q17 + q19 = r9 + r11 + r17 + r19
  m26 : q5 + q7 + q9 + q11 + q13 + q15 = r13 + r15 + r17 + r19
  m34 : q12 + q13 + q14 + q15 + q16 + q17 + q18 + q19 = r16 + r17 + r18 + r19
  m35 : q8 + q9 + q10 + q11 + q16 + q17 + q18 + q19 = r16 + r17 + r18 + r19
  m36 : q8 + q9 + q10 + q11 + q12 + q13 + q14 + q15 = r16 + r17 + r18 + r19
  m45 : q4 + q5 + q6 + q7 + q16 + q17 + q18 + q19 = r16 + r17 + r18 + r19
  m46 : q4 + q5 + q6 + q7 + q12 + q13 + q14 + q15 = r16 + r17 + r18 + r19
  m56 : q4 + q5 + q6 + q7 + q8 + q9 + q10 + q11 = r16 + r17 + r18 + r19

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

/-- The ten squared norms are pinned by the moment polytope. -/
theorem MomentSystem.norms {q0  q1  q2  q3  q4  q5  q6  q7  q8  q9  q10  q11  q12  q13  q14  q15  q16
     q17  q18  q19  r0  r1  r2  r3  r4  r5  r6  r7  r8  r9  r10  r11  r12  r13  r14  r15  r16  r17  r18
     r19 : Real}
    (h : MomentSystem q0  q1  q2  q3  q4  q5  q6  q7  q8  q9  q10  q11  q12  q13  q14  q15  q16  q17
       q18  q19  r0  r1  r2  r3  r4  r5  r6  r7  r8  r9  r10  r11  r12  r13  r14  r15  r16  r17  r18
       r19) :
    q0 + q1 + q2 + q3 = 1/3 ∧ q4 + q5 + q6 + q7 = 1/6 ∧ q8 + q9 + q10 + q11 = 1/6
      ∧ q12 + q13 + q14 + q15 = 1/6 ∧ q16 + q17 + q18 + q19 = 1/6 ∧ r0 + r1 + r2 + r3 = 1/6
      ∧ r4 + r5 + r6 + r7 = 1/6 ∧ r8 + r9 + r10 + r11 = 1/6 ∧ r12 + r13 + r14 + r15 = 1/6
      ∧ r16 + r17 + r18 + r19 = 1/3 := by
  obtain ⟨n0 , n1 , m1 , m2 , m3 , m4 , m5 , m6 , m12 , m13 , m14 , m15 , m16 , m23 , m24 , m25 , m26
    , m34 , m35 , m36 , m45 , m46 , m56 , nq0 , nq1 , nq2 , nq3 , nq4 , nq5 , nq6 , nq7 , nq8 , nq9
    , nq10 , nq11 , nq12 , nq13 , nq14 , nq15 , nq16 , nq17 , nq18 , nq19 , nr0 , nr1 , nr2 , nr3 , nr4
    , nr5 , nr6 , nr7 , nr8 , nr9 , nr10 , nr11 , nr12 , nr13 , nr14 , nr15 , nr16 , nr17 , nr18 , nr19⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- The four diagonal entries of the reduced density matrix on the free pair
agree; these are the moment equalities for `I`, `Z₁`, `Z₂` and `Z₁Z₂`. -/
theorem MomentSystem.marginal {q0  q1  q2  q3  q4  q5  q6  q7  q8  q9  q10  q11  q12  q13  q14  q15  q16
     q17  q18  q19  r0  r1  r2  r3  r4  r5  r6  r7  r8  r9  r10  r11  r12  r13  r14  r15  r16  r17  r18
     r19 : Real}
    (h : MomentSystem q0  q1  q2  q3  q4  q5  q6  q7  q8  q9  q10  q11  q12  q13  q14  q15  q16  q17
       q18  q19  r0  r1  r2  r3  r4  r5  r6  r7  r8  r9  r10  r11  r12  r13  r14  r15  r16  r17  r18
       r19) :
    q0 + q4 + q8 + q12 + q16 = r0 + r4 + r8 + r12 + r16
      ∧ q1 + q5 + q9 + q13 + q17 = r1 + r5 + r9 + r13 + r17
      ∧ q2 + q6 + q10 + q14 + q18 = r2 + r6 + r10 + r14 + r18
      ∧ q3 + q7 + q11 + q15 + q19 = r3 + r7 + r11 + r15 + r19 := by
  obtain ⟨n0 , n1 , m1 , m2 , m3 , m4 , m5 , m6 , m12 , m13 , m14 , m15 , m16 , m23 , m24 , m25 , m26
    , m34 , m35 , m36 , m45 , m46 , m56 , nq0 , nq1 , nq2 , nq3 , nq4 , nq5 , nq6 , nq7 , nq8 , nq9
    , nq10 , nq11 , nq12 , nq13 , nq14 , nq15 , nq16 , nq17 , nq18 , nq19 , nr0 , nr1 , nr2 , nr3 , nr4
    , nr5 , nr6 , nr7 , nr8 , nr9 , nr10 , nr11 , nr12 , nr13 , nr14 , nr15 , nr16 , nr17 , nr18 , nr19⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-! ## The ten vectors of `ℂ⁴` -/

def uu (c : SS.BitString 6 -> ℂ) : Fin 4 -> ℂ := ![c y0, c y1, c y2, c y3]
def aa1 (c : SS.BitString 6 -> ℂ) : Fin 4 -> ℂ := ![c y4, c y5, c y6, c y7]
def aa2 (c : SS.BitString 6 -> ℂ) : Fin 4 -> ℂ := ![c y8, c y9, c y10, c y11]
def aa3 (c : SS.BitString 6 -> ℂ) : Fin 4 -> ℂ := ![c y12, c y13, c y14, c y15]
def aa4 (c : SS.BitString 6 -> ℂ) : Fin 4 -> ℂ := ![c y16, c y17, c y18, c y19]
def bb1 (d : SS.BitString 6 -> ℂ) : Fin 4 -> ℂ := ![d z0, d z1, d z2, d z3]
def bb2 (d : SS.BitString 6 -> ℂ) : Fin 4 -> ℂ := ![d z4, d z5, d z6, d z7]
def bb3 (d : SS.BitString 6 -> ℂ) : Fin 4 -> ℂ := ![d z8, d z9, d z10, d z11]
def bb4 (d : SS.BitString 6 -> ℂ) : Fin 4 -> ℂ := ![d z12, d z13, d z14, d z15]
def vv (d : SS.BitString 6 -> ℂ) : Fin 4 -> ℂ := ![d z16, d z17, d z18, d z19]

@[simp] theorem uu_0 (c : SS.BitString 6 -> ℂ) : uu c 0 = c y0 := rfl
@[simp] theorem uu_1 (c : SS.BitString 6 -> ℂ) : uu c 1 = c y1 := rfl
@[simp] theorem uu_2 (c : SS.BitString 6 -> ℂ) : uu c 2 = c y2 := rfl
@[simp] theorem uu_3 (c : SS.BitString 6 -> ℂ) : uu c 3 = c y3 := rfl
@[simp] theorem aa1_0 (c : SS.BitString 6 -> ℂ) : aa1 c 0 = c y4 := rfl
@[simp] theorem aa1_1 (c : SS.BitString 6 -> ℂ) : aa1 c 1 = c y5 := rfl
@[simp] theorem aa1_2 (c : SS.BitString 6 -> ℂ) : aa1 c 2 = c y6 := rfl
@[simp] theorem aa1_3 (c : SS.BitString 6 -> ℂ) : aa1 c 3 = c y7 := rfl
@[simp] theorem aa2_0 (c : SS.BitString 6 -> ℂ) : aa2 c 0 = c y8 := rfl
@[simp] theorem aa2_1 (c : SS.BitString 6 -> ℂ) : aa2 c 1 = c y9 := rfl
@[simp] theorem aa2_2 (c : SS.BitString 6 -> ℂ) : aa2 c 2 = c y10 := rfl
@[simp] theorem aa2_3 (c : SS.BitString 6 -> ℂ) : aa2 c 3 = c y11 := rfl
@[simp] theorem aa3_0 (c : SS.BitString 6 -> ℂ) : aa3 c 0 = c y12 := rfl
@[simp] theorem aa3_1 (c : SS.BitString 6 -> ℂ) : aa3 c 1 = c y13 := rfl
@[simp] theorem aa3_2 (c : SS.BitString 6 -> ℂ) : aa3 c 2 = c y14 := rfl
@[simp] theorem aa3_3 (c : SS.BitString 6 -> ℂ) : aa3 c 3 = c y15 := rfl
@[simp] theorem aa4_0 (c : SS.BitString 6 -> ℂ) : aa4 c 0 = c y16 := rfl
@[simp] theorem aa4_1 (c : SS.BitString 6 -> ℂ) : aa4 c 1 = c y17 := rfl
@[simp] theorem aa4_2 (c : SS.BitString 6 -> ℂ) : aa4 c 2 = c y18 := rfl
@[simp] theorem aa4_3 (c : SS.BitString 6 -> ℂ) : aa4 c 3 = c y19 := rfl
@[simp] theorem bb1_0 (d : SS.BitString 6 -> ℂ) : bb1 d 0 = d z0 := rfl
@[simp] theorem bb1_1 (d : SS.BitString 6 -> ℂ) : bb1 d 1 = d z1 := rfl
@[simp] theorem bb1_2 (d : SS.BitString 6 -> ℂ) : bb1 d 2 = d z2 := rfl
@[simp] theorem bb1_3 (d : SS.BitString 6 -> ℂ) : bb1 d 3 = d z3 := rfl
@[simp] theorem bb2_0 (d : SS.BitString 6 -> ℂ) : bb2 d 0 = d z4 := rfl
@[simp] theorem bb2_1 (d : SS.BitString 6 -> ℂ) : bb2 d 1 = d z5 := rfl
@[simp] theorem bb2_2 (d : SS.BitString 6 -> ℂ) : bb2 d 2 = d z6 := rfl
@[simp] theorem bb2_3 (d : SS.BitString 6 -> ℂ) : bb2 d 3 = d z7 := rfl
@[simp] theorem bb3_0 (d : SS.BitString 6 -> ℂ) : bb3 d 0 = d z8 := rfl
@[simp] theorem bb3_1 (d : SS.BitString 6 -> ℂ) : bb3 d 1 = d z9 := rfl
@[simp] theorem bb3_2 (d : SS.BitString 6 -> ℂ) : bb3 d 2 = d z10 := rfl
@[simp] theorem bb3_3 (d : SS.BitString 6 -> ℂ) : bb3 d 3 = d z11 := rfl
@[simp] theorem bb4_0 (d : SS.BitString 6 -> ℂ) : bb4 d 0 = d z12 := rfl
@[simp] theorem bb4_1 (d : SS.BitString 6 -> ℂ) : bb4 d 1 = d z13 := rfl
@[simp] theorem bb4_2 (d : SS.BitString 6 -> ℂ) : bb4 d 2 = d z14 := rfl
@[simp] theorem bb4_3 (d : SS.BitString 6 -> ℂ) : bb4 d 3 = d z15 := rfl
@[simp] theorem vv_0 (d : SS.BitString 6 -> ℂ) : vv d 0 = d z16 := rfl
@[simp] theorem vv_1 (d : SS.BitString 6 -> ℂ) : vv d 1 = d z17 := rfl
@[simp] theorem vv_2 (d : SS.BitString 6 -> ℂ) : vv d 2 = d z18 := rfl
@[simp] theorem vv_3 (d : SS.BitString 6 -> ℂ) : vv d 3 = d z19 := rfl

/-! ## The dressed one-flip layer

For a single zero-angle qubit `A` and an active coordinate `i` the errors
`Z_A X_i`, `X_A X_i` and `Y_A X_i` all have weight two, so their off-diagonal
rows are available.  Together with the undressed row they carry all four
entries of each of the two one-qubit partial traces of `|u><b_i| + |a_i><u|`.
-/

def k1 : SS.BitString 6 := bs true  false true  false false false  -- 101000
def k2 : SS.BitString 6 := bs true  false false true  false false  -- 100100
def k3 : SS.BitString 6 := bs true  false false false true  false  -- 100010
def k4 : SS.BitString 6 := bs true  false false false false true  -- 100001
def l1 : SS.BitString 6 := bs false true  true  false false false  -- 011000
def l2 : SS.BitString 6 := bs false true  false true  false false  -- 010100
def l3 : SS.BitString 6 := bs false true  false false true  false  -- 010010
def l4 : SS.BitString 6 := bs false true  false false false true  -- 010001

theorem inc_k1 :
    S1.filter (fun y => SS.bxor y k1 ∈ S0) = {z0, z1, z2, z3, z16, z17, z18, z19} := by decide
theorem flip_k1_0 : SS.bxor z0 k1 = y2 := by decide
theorem flip_k1_1 : SS.bxor z1 k1 = y3 := by decide
theorem flip_k1_2 : SS.bxor z2 k1 = y0 := by decide
theorem flip_k1_3 : SS.bxor z3 k1 = y1 := by decide
theorem flip_k1_16 : SS.bxor z16 k1 = y6 := by decide
theorem flip_k1_17 : SS.bxor z17 k1 = y7 := by decide
theorem flip_k1_18 : SS.bxor z18 k1 = y4 := by decide
theorem flip_k1_19 : SS.bxor z19 k1 = y5 := by decide
theorem inc_k2 :
    S1.filter (fun y => SS.bxor y k2 ∈ S0) = {z4, z5, z6, z7, z16, z17, z18, z19} := by decide
theorem flip_k2_4 : SS.bxor z4 k2 = y2 := by decide
theorem flip_k2_5 : SS.bxor z5 k2 = y3 := by decide
theorem flip_k2_6 : SS.bxor z6 k2 = y0 := by decide
theorem flip_k2_7 : SS.bxor z7 k2 = y1 := by decide
theorem flip_k2_16 : SS.bxor z16 k2 = y10 := by decide
theorem flip_k2_17 : SS.bxor z17 k2 = y11 := by decide
theorem flip_k2_18 : SS.bxor z18 k2 = y8 := by decide
theorem flip_k2_19 : SS.bxor z19 k2 = y9 := by decide
theorem inc_k3 :
    S1.filter (fun y => SS.bxor y k3 ∈ S0) = {z8, z9, z10, z11, z16, z17, z18, z19} := by decide
theorem flip_k3_8 : SS.bxor z8 k3 = y2 := by decide
theorem flip_k3_9 : SS.bxor z9 k3 = y3 := by decide
theorem flip_k3_10 : SS.bxor z10 k3 = y0 := by decide
theorem flip_k3_11 : SS.bxor z11 k3 = y1 := by decide
theorem flip_k3_16 : SS.bxor z16 k3 = y14 := by decide
theorem flip_k3_17 : SS.bxor z17 k3 = y15 := by decide
theorem flip_k3_18 : SS.bxor z18 k3 = y12 := by decide
theorem flip_k3_19 : SS.bxor z19 k3 = y13 := by decide
theorem inc_k4 :
    S1.filter (fun y => SS.bxor y k4 ∈ S0) = {z12, z13, z14, z15, z16, z17, z18, z19} := by decide
theorem flip_k4_12 : SS.bxor z12 k4 = y2 := by decide
theorem flip_k4_13 : SS.bxor z13 k4 = y3 := by decide
theorem flip_k4_14 : SS.bxor z14 k4 = y0 := by decide
theorem flip_k4_15 : SS.bxor z15 k4 = y1 := by decide
theorem flip_k4_16 : SS.bxor z16 k4 = y18 := by decide
theorem flip_k4_17 : SS.bxor z17 k4 = y19 := by decide
theorem flip_k4_18 : SS.bxor z18 k4 = y16 := by decide
theorem flip_k4_19 : SS.bxor z19 k4 = y17 := by decide
theorem inc_l1 :
    S1.filter (fun y => SS.bxor y l1 ∈ S0) = {z0, z1, z2, z3, z16, z17, z18, z19} := by decide
theorem flip_l1_0 : SS.bxor z0 l1 = y1 := by decide
theorem flip_l1_1 : SS.bxor z1 l1 = y0 := by decide
theorem flip_l1_2 : SS.bxor z2 l1 = y3 := by decide
theorem flip_l1_3 : SS.bxor z3 l1 = y2 := by decide
theorem flip_l1_16 : SS.bxor z16 l1 = y5 := by decide
theorem flip_l1_17 : SS.bxor z17 l1 = y4 := by decide
theorem flip_l1_18 : SS.bxor z18 l1 = y7 := by decide
theorem flip_l1_19 : SS.bxor z19 l1 = y6 := by decide
theorem inc_l2 :
    S1.filter (fun y => SS.bxor y l2 ∈ S0) = {z4, z5, z6, z7, z16, z17, z18, z19} := by decide
theorem flip_l2_4 : SS.bxor z4 l2 = y1 := by decide
theorem flip_l2_5 : SS.bxor z5 l2 = y0 := by decide
theorem flip_l2_6 : SS.bxor z6 l2 = y3 := by decide
theorem flip_l2_7 : SS.bxor z7 l2 = y2 := by decide
theorem flip_l2_16 : SS.bxor z16 l2 = y9 := by decide
theorem flip_l2_17 : SS.bxor z17 l2 = y8 := by decide
theorem flip_l2_18 : SS.bxor z18 l2 = y11 := by decide
theorem flip_l2_19 : SS.bxor z19 l2 = y10 := by decide
theorem inc_l3 :
    S1.filter (fun y => SS.bxor y l3 ∈ S0) = {z8, z9, z10, z11, z16, z17, z18, z19} := by decide
theorem flip_l3_8 : SS.bxor z8 l3 = y1 := by decide
theorem flip_l3_9 : SS.bxor z9 l3 = y0 := by decide
theorem flip_l3_10 : SS.bxor z10 l3 = y3 := by decide
theorem flip_l3_11 : SS.bxor z11 l3 = y2 := by decide
theorem flip_l3_16 : SS.bxor z16 l3 = y13 := by decide
theorem flip_l3_17 : SS.bxor z17 l3 = y12 := by decide
theorem flip_l3_18 : SS.bxor z18 l3 = y15 := by decide
theorem flip_l3_19 : SS.bxor z19 l3 = y14 := by decide
theorem inc_l4 :
    S1.filter (fun y => SS.bxor y l4 ∈ S0) = {z12, z13, z14, z15, z16, z17, z18, z19} := by decide
theorem flip_l4_12 : SS.bxor z12 l4 = y1 := by decide
theorem flip_l4_13 : SS.bxor z13 l4 = y0 := by decide
theorem flip_l4_14 : SS.bxor z14 l4 = y3 := by decide
theorem flip_l4_15 : SS.bxor z15 l4 = y2 := by decide
theorem flip_l4_16 : SS.bxor z16 l4 = y17 := by decide
theorem flip_l4_17 : SS.bxor z17 l4 = y16 := by decide
theorem flip_l4_18 : SS.bxor z18 l4 = y19 := by decide
theorem flip_l4_19 : SS.bxor z19 l4 = y18 := by decide

theorem sg_f1_p1_0 : SS.bdot p1 z0 = false := by decide
theorem sg_f1_p1_1 : SS.bdot p1 z1 = false := by decide
theorem sg_f1_p1_2 : SS.bdot p1 z2 = true := by decide
theorem sg_f1_p1_3 : SS.bdot p1 z3 = true := by decide
theorem sg_f1_p1_16 : SS.bdot p1 z16 = false := by decide
theorem sg_f1_p1_17 : SS.bdot p1 z17 = false := by decide
theorem sg_f1_p1_18 : SS.bdot p1 z18 = true := by decide
theorem sg_f1_p1_19 : SS.bdot p1 z19 = true := by decide
theorem ex_f1_p1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d f1 p1 = star (c y0) * d z0 + star (c y1) * d z1 - star (c y2) * d z2 - star (c y3) * d z3
      + star (c y4) * d z16 + star (c y5) * d z17 - star (c y6) * d z18 - star (c y7) * d z19 := by
  unfold offSum
  rw [inc_f1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_f1_0, flip_f1_1, flip_f1_2, flip_f1_3, flip_f1_16, flip_f1_17, flip_f1_18, flip_f1_19]
  simp only [sg_f1_p1_0, sg_f1_p1_1, sg_f1_p1_2, sg_f1_p1_3, sg_f1_p1_16, sg_f1_p1_17, sg_f1_p1_18, sg_f1_p1_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_f1_p2_0 : SS.bdot p2 z0 = false := by decide
theorem sg_f1_p2_1 : SS.bdot p2 z1 = true := by decide
theorem sg_f1_p2_2 : SS.bdot p2 z2 = false := by decide
theorem sg_f1_p2_3 : SS.bdot p2 z3 = true := by decide
theorem sg_f1_p2_16 : SS.bdot p2 z16 = false := by decide
theorem sg_f1_p2_17 : SS.bdot p2 z17 = true := by decide
theorem sg_f1_p2_18 : SS.bdot p2 z18 = false := by decide
theorem sg_f1_p2_19 : SS.bdot p2 z19 = true := by decide
theorem ex_f1_p2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d f1 p2 = star (c y0) * d z0 - star (c y1) * d z1 + star (c y2) * d z2 - star (c y3) * d z3
      + star (c y4) * d z16 - star (c y5) * d z17 + star (c y6) * d z18 - star (c y7) * d z19 := by
  unfold offSum
  rw [inc_f1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_f1_0, flip_f1_1, flip_f1_2, flip_f1_3, flip_f1_16, flip_f1_17, flip_f1_18, flip_f1_19]
  simp only [sg_f1_p2_0, sg_f1_p2_1, sg_f1_p2_2, sg_f1_p2_3, sg_f1_p2_16, sg_f1_p2_17, sg_f1_p2_18, sg_f1_p2_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_k1_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg_k1_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg_k1_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg_k1_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg_k1_w0_16 : SS.bdot w0 z16 = false := by decide
theorem sg_k1_w0_17 : SS.bdot w0 z17 = false := by decide
theorem sg_k1_w0_18 : SS.bdot w0 z18 = false := by decide
theorem sg_k1_w0_19 : SS.bdot w0 z19 = false := by decide
theorem ex_k1_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d k1 w0 = star (c y2) * d z0 + star (c y3) * d z1 + star (c y0) * d z2 + star (c y1) * d z3
      + star (c y6) * d z16 + star (c y7) * d z17 + star (c y4) * d z18 + star (c y5) * d z19 := by
  unfold offSum
  rw [inc_k1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_k1_0, flip_k1_1, flip_k1_2, flip_k1_3, flip_k1_16, flip_k1_17, flip_k1_18, flip_k1_19]
  simp only [sg_k1_w0_0, sg_k1_w0_1, sg_k1_w0_2, sg_k1_w0_3, sg_k1_w0_16, sg_k1_w0_17, sg_k1_w0_18, sg_k1_w0_19, SixQubit.signMul_false]
  try ring
theorem sg_k1_p1_0 : SS.bdot p1 z0 = false := by decide
theorem sg_k1_p1_1 : SS.bdot p1 z1 = false := by decide
theorem sg_k1_p1_2 : SS.bdot p1 z2 = true := by decide
theorem sg_k1_p1_3 : SS.bdot p1 z3 = true := by decide
theorem sg_k1_p1_16 : SS.bdot p1 z16 = false := by decide
theorem sg_k1_p1_17 : SS.bdot p1 z17 = false := by decide
theorem sg_k1_p1_18 : SS.bdot p1 z18 = true := by decide
theorem sg_k1_p1_19 : SS.bdot p1 z19 = true := by decide
theorem ex_k1_p1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d k1 p1 = star (c y2) * d z0 + star (c y3) * d z1 - star (c y0) * d z2 - star (c y1) * d z3
      + star (c y6) * d z16 + star (c y7) * d z17 - star (c y4) * d z18 - star (c y5) * d z19 := by
  unfold offSum
  rw [inc_k1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_k1_0, flip_k1_1, flip_k1_2, flip_k1_3, flip_k1_16, flip_k1_17, flip_k1_18, flip_k1_19]
  simp only [sg_k1_p1_0, sg_k1_p1_1, sg_k1_p1_2, sg_k1_p1_3, sg_k1_p1_16, sg_k1_p1_17, sg_k1_p1_18, sg_k1_p1_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_l1_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg_l1_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg_l1_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg_l1_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg_l1_w0_16 : SS.bdot w0 z16 = false := by decide
theorem sg_l1_w0_17 : SS.bdot w0 z17 = false := by decide
theorem sg_l1_w0_18 : SS.bdot w0 z18 = false := by decide
theorem sg_l1_w0_19 : SS.bdot w0 z19 = false := by decide
theorem ex_l1_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d l1 w0 = star (c y1) * d z0 + star (c y0) * d z1 + star (c y3) * d z2 + star (c y2) * d z3
      + star (c y5) * d z16 + star (c y4) * d z17 + star (c y7) * d z18 + star (c y6) * d z19 := by
  unfold offSum
  rw [inc_l1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_l1_0, flip_l1_1, flip_l1_2, flip_l1_3, flip_l1_16, flip_l1_17, flip_l1_18, flip_l1_19]
  simp only [sg_l1_w0_0, sg_l1_w0_1, sg_l1_w0_2, sg_l1_w0_3, sg_l1_w0_16, sg_l1_w0_17, sg_l1_w0_18, sg_l1_w0_19, SixQubit.signMul_false]
  try ring
theorem sg_l1_p2_0 : SS.bdot p2 z0 = false := by decide
theorem sg_l1_p2_1 : SS.bdot p2 z1 = true := by decide
theorem sg_l1_p2_2 : SS.bdot p2 z2 = false := by decide
theorem sg_l1_p2_3 : SS.bdot p2 z3 = true := by decide
theorem sg_l1_p2_16 : SS.bdot p2 z16 = false := by decide
theorem sg_l1_p2_17 : SS.bdot p2 z17 = true := by decide
theorem sg_l1_p2_18 : SS.bdot p2 z18 = false := by decide
theorem sg_l1_p2_19 : SS.bdot p2 z19 = true := by decide
theorem ex_l1_p2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d l1 p2 = star (c y1) * d z0 - star (c y0) * d z1 + star (c y3) * d z2 - star (c y2) * d z3
      + star (c y5) * d z16 - star (c y4) * d z17 + star (c y7) * d z18 - star (c y6) * d z19 := by
  unfold offSum
  rw [inc_l1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_l1_0, flip_l1_1, flip_l1_2, flip_l1_3, flip_l1_16, flip_l1_17, flip_l1_18, flip_l1_19]
  simp only [sg_l1_p2_0, sg_l1_p2_1, sg_l1_p2_2, sg_l1_p2_3, sg_l1_p2_16, sg_l1_p2_17, sg_l1_p2_18, sg_l1_p2_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_f2_p1_4 : SS.bdot p1 z4 = false := by decide
theorem sg_f2_p1_5 : SS.bdot p1 z5 = false := by decide
theorem sg_f2_p1_6 : SS.bdot p1 z6 = true := by decide
theorem sg_f2_p1_7 : SS.bdot p1 z7 = true := by decide
theorem sg_f2_p1_16 : SS.bdot p1 z16 = false := by decide
theorem sg_f2_p1_17 : SS.bdot p1 z17 = false := by decide
theorem sg_f2_p1_18 : SS.bdot p1 z18 = true := by decide
theorem sg_f2_p1_19 : SS.bdot p1 z19 = true := by decide
theorem ex_f2_p1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d f2 p1 = star (c y0) * d z4 + star (c y1) * d z5 - star (c y2) * d z6 - star (c y3) * d z7
      + star (c y8) * d z16 + star (c y9) * d z17 - star (c y10) * d z18 - star (c y11) * d z19 := by
  unfold offSum
  rw [inc_f2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_f2_4, flip_f2_5, flip_f2_6, flip_f2_7, flip_f2_16, flip_f2_17, flip_f2_18, flip_f2_19]
  simp only [sg_f2_p1_4, sg_f2_p1_5, sg_f2_p1_6, sg_f2_p1_7, sg_f2_p1_16, sg_f2_p1_17, sg_f2_p1_18, sg_f2_p1_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_f2_p2_4 : SS.bdot p2 z4 = false := by decide
theorem sg_f2_p2_5 : SS.bdot p2 z5 = true := by decide
theorem sg_f2_p2_6 : SS.bdot p2 z6 = false := by decide
theorem sg_f2_p2_7 : SS.bdot p2 z7 = true := by decide
theorem sg_f2_p2_16 : SS.bdot p2 z16 = false := by decide
theorem sg_f2_p2_17 : SS.bdot p2 z17 = true := by decide
theorem sg_f2_p2_18 : SS.bdot p2 z18 = false := by decide
theorem sg_f2_p2_19 : SS.bdot p2 z19 = true := by decide
theorem ex_f2_p2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d f2 p2 = star (c y0) * d z4 - star (c y1) * d z5 + star (c y2) * d z6 - star (c y3) * d z7
      + star (c y8) * d z16 - star (c y9) * d z17 + star (c y10) * d z18 - star (c y11) * d z19 := by
  unfold offSum
  rw [inc_f2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_f2_4, flip_f2_5, flip_f2_6, flip_f2_7, flip_f2_16, flip_f2_17, flip_f2_18, flip_f2_19]
  simp only [sg_f2_p2_4, sg_f2_p2_5, sg_f2_p2_6, sg_f2_p2_7, sg_f2_p2_16, sg_f2_p2_17, sg_f2_p2_18, sg_f2_p2_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_k2_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg_k2_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg_k2_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg_k2_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg_k2_w0_16 : SS.bdot w0 z16 = false := by decide
theorem sg_k2_w0_17 : SS.bdot w0 z17 = false := by decide
theorem sg_k2_w0_18 : SS.bdot w0 z18 = false := by decide
theorem sg_k2_w0_19 : SS.bdot w0 z19 = false := by decide
theorem ex_k2_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d k2 w0 = star (c y2) * d z4 + star (c y3) * d z5 + star (c y0) * d z6 + star (c y1) * d z7
      + star (c y10) * d z16 + star (c y11) * d z17 + star (c y8) * d z18 + star (c y9) * d z19 := by
  unfold offSum
  rw [inc_k2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_k2_4, flip_k2_5, flip_k2_6, flip_k2_7, flip_k2_16, flip_k2_17, flip_k2_18, flip_k2_19]
  simp only [sg_k2_w0_4, sg_k2_w0_5, sg_k2_w0_6, sg_k2_w0_7, sg_k2_w0_16, sg_k2_w0_17, sg_k2_w0_18, sg_k2_w0_19, SixQubit.signMul_false]
  try ring
theorem sg_k2_p1_4 : SS.bdot p1 z4 = false := by decide
theorem sg_k2_p1_5 : SS.bdot p1 z5 = false := by decide
theorem sg_k2_p1_6 : SS.bdot p1 z6 = true := by decide
theorem sg_k2_p1_7 : SS.bdot p1 z7 = true := by decide
theorem sg_k2_p1_16 : SS.bdot p1 z16 = false := by decide
theorem sg_k2_p1_17 : SS.bdot p1 z17 = false := by decide
theorem sg_k2_p1_18 : SS.bdot p1 z18 = true := by decide
theorem sg_k2_p1_19 : SS.bdot p1 z19 = true := by decide
theorem ex_k2_p1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d k2 p1 = star (c y2) * d z4 + star (c y3) * d z5 - star (c y0) * d z6 - star (c y1) * d z7
      + star (c y10) * d z16 + star (c y11) * d z17 - star (c y8) * d z18 - star (c y9) * d z19 := by
  unfold offSum
  rw [inc_k2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_k2_4, flip_k2_5, flip_k2_6, flip_k2_7, flip_k2_16, flip_k2_17, flip_k2_18, flip_k2_19]
  simp only [sg_k2_p1_4, sg_k2_p1_5, sg_k2_p1_6, sg_k2_p1_7, sg_k2_p1_16, sg_k2_p1_17, sg_k2_p1_18, sg_k2_p1_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_l2_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg_l2_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg_l2_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg_l2_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg_l2_w0_16 : SS.bdot w0 z16 = false := by decide
theorem sg_l2_w0_17 : SS.bdot w0 z17 = false := by decide
theorem sg_l2_w0_18 : SS.bdot w0 z18 = false := by decide
theorem sg_l2_w0_19 : SS.bdot w0 z19 = false := by decide
theorem ex_l2_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d l2 w0 = star (c y1) * d z4 + star (c y0) * d z5 + star (c y3) * d z6 + star (c y2) * d z7
      + star (c y9) * d z16 + star (c y8) * d z17 + star (c y11) * d z18 + star (c y10) * d z19 := by
  unfold offSum
  rw [inc_l2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_l2_4, flip_l2_5, flip_l2_6, flip_l2_7, flip_l2_16, flip_l2_17, flip_l2_18, flip_l2_19]
  simp only [sg_l2_w0_4, sg_l2_w0_5, sg_l2_w0_6, sg_l2_w0_7, sg_l2_w0_16, sg_l2_w0_17, sg_l2_w0_18, sg_l2_w0_19, SixQubit.signMul_false]
  try ring
theorem sg_l2_p2_4 : SS.bdot p2 z4 = false := by decide
theorem sg_l2_p2_5 : SS.bdot p2 z5 = true := by decide
theorem sg_l2_p2_6 : SS.bdot p2 z6 = false := by decide
theorem sg_l2_p2_7 : SS.bdot p2 z7 = true := by decide
theorem sg_l2_p2_16 : SS.bdot p2 z16 = false := by decide
theorem sg_l2_p2_17 : SS.bdot p2 z17 = true := by decide
theorem sg_l2_p2_18 : SS.bdot p2 z18 = false := by decide
theorem sg_l2_p2_19 : SS.bdot p2 z19 = true := by decide
theorem ex_l2_p2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d l2 p2 = star (c y1) * d z4 - star (c y0) * d z5 + star (c y3) * d z6 - star (c y2) * d z7
      + star (c y9) * d z16 - star (c y8) * d z17 + star (c y11) * d z18 - star (c y10) * d z19 := by
  unfold offSum
  rw [inc_l2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_l2_4, flip_l2_5, flip_l2_6, flip_l2_7, flip_l2_16, flip_l2_17, flip_l2_18, flip_l2_19]
  simp only [sg_l2_p2_4, sg_l2_p2_5, sg_l2_p2_6, sg_l2_p2_7, sg_l2_p2_16, sg_l2_p2_17, sg_l2_p2_18, sg_l2_p2_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_f3_p1_8 : SS.bdot p1 z8 = false := by decide
theorem sg_f3_p1_9 : SS.bdot p1 z9 = false := by decide
theorem sg_f3_p1_10 : SS.bdot p1 z10 = true := by decide
theorem sg_f3_p1_11 : SS.bdot p1 z11 = true := by decide
theorem sg_f3_p1_16 : SS.bdot p1 z16 = false := by decide
theorem sg_f3_p1_17 : SS.bdot p1 z17 = false := by decide
theorem sg_f3_p1_18 : SS.bdot p1 z18 = true := by decide
theorem sg_f3_p1_19 : SS.bdot p1 z19 = true := by decide
theorem ex_f3_p1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d f3 p1 = star (c y0) * d z8
      + star (c y1) * d z9 - star (c y2) * d z10 - star (c y3) * d z11 + star (c y12) * d z16
      + star (c y13) * d z17 - star (c y14) * d z18 - star (c y15) * d z19 := by
  unfold offSum
  rw [inc_f3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_f3_8, flip_f3_9, flip_f3_10, flip_f3_11, flip_f3_16, flip_f3_17, flip_f3_18, flip_f3_19]
  simp only [sg_f3_p1_8, sg_f3_p1_9, sg_f3_p1_10, sg_f3_p1_11, sg_f3_p1_16, sg_f3_p1_17, sg_f3_p1_18, sg_f3_p1_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_f3_p2_8 : SS.bdot p2 z8 = false := by decide
theorem sg_f3_p2_9 : SS.bdot p2 z9 = true := by decide
theorem sg_f3_p2_10 : SS.bdot p2 z10 = false := by decide
theorem sg_f3_p2_11 : SS.bdot p2 z11 = true := by decide
theorem sg_f3_p2_16 : SS.bdot p2 z16 = false := by decide
theorem sg_f3_p2_17 : SS.bdot p2 z17 = true := by decide
theorem sg_f3_p2_18 : SS.bdot p2 z18 = false := by decide
theorem sg_f3_p2_19 : SS.bdot p2 z19 = true := by decide
theorem ex_f3_p2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d f3 p2 = star (c y0) * d z8 - star (c y1) * d z9
      + star (c y2) * d z10 - star (c y3) * d z11 + star (c y12) * d z16 - star (c y13) * d z17
      + star (c y14) * d z18 - star (c y15) * d z19 := by
  unfold offSum
  rw [inc_f3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_f3_8, flip_f3_9, flip_f3_10, flip_f3_11, flip_f3_16, flip_f3_17, flip_f3_18, flip_f3_19]
  simp only [sg_f3_p2_8, sg_f3_p2_9, sg_f3_p2_10, sg_f3_p2_11, sg_f3_p2_16, sg_f3_p2_17, sg_f3_p2_18, sg_f3_p2_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_k3_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_k3_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg_k3_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg_k3_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg_k3_w0_16 : SS.bdot w0 z16 = false := by decide
theorem sg_k3_w0_17 : SS.bdot w0 z17 = false := by decide
theorem sg_k3_w0_18 : SS.bdot w0 z18 = false := by decide
theorem sg_k3_w0_19 : SS.bdot w0 z19 = false := by decide
theorem ex_k3_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d k3 w0 = star (c y2) * d z8 + star (c y3) * d z9 + star (c y0) * d z10
      + star (c y1) * d z11 + star (c y14) * d z16 + star (c y15) * d z17 + star (c y12) * d z18
      + star (c y13) * d z19 := by
  unfold offSum
  rw [inc_k3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_k3_8, flip_k3_9, flip_k3_10, flip_k3_11, flip_k3_16, flip_k3_17, flip_k3_18, flip_k3_19]
  simp only [sg_k3_w0_8, sg_k3_w0_9, sg_k3_w0_10, sg_k3_w0_11, sg_k3_w0_16, sg_k3_w0_17, sg_k3_w0_18, sg_k3_w0_19, SixQubit.signMul_false]
  try ring
theorem sg_k3_p1_8 : SS.bdot p1 z8 = false := by decide
theorem sg_k3_p1_9 : SS.bdot p1 z9 = false := by decide
theorem sg_k3_p1_10 : SS.bdot p1 z10 = true := by decide
theorem sg_k3_p1_11 : SS.bdot p1 z11 = true := by decide
theorem sg_k3_p1_16 : SS.bdot p1 z16 = false := by decide
theorem sg_k3_p1_17 : SS.bdot p1 z17 = false := by decide
theorem sg_k3_p1_18 : SS.bdot p1 z18 = true := by decide
theorem sg_k3_p1_19 : SS.bdot p1 z19 = true := by decide
theorem ex_k3_p1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d k3 p1 = star (c y2) * d z8
      + star (c y3) * d z9 - star (c y0) * d z10 - star (c y1) * d z11 + star (c y14) * d z16
      + star (c y15) * d z17 - star (c y12) * d z18 - star (c y13) * d z19 := by
  unfold offSum
  rw [inc_k3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_k3_8, flip_k3_9, flip_k3_10, flip_k3_11, flip_k3_16, flip_k3_17, flip_k3_18, flip_k3_19]
  simp only [sg_k3_p1_8, sg_k3_p1_9, sg_k3_p1_10, sg_k3_p1_11, sg_k3_p1_16, sg_k3_p1_17, sg_k3_p1_18, sg_k3_p1_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_l3_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_l3_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg_l3_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg_l3_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg_l3_w0_16 : SS.bdot w0 z16 = false := by decide
theorem sg_l3_w0_17 : SS.bdot w0 z17 = false := by decide
theorem sg_l3_w0_18 : SS.bdot w0 z18 = false := by decide
theorem sg_l3_w0_19 : SS.bdot w0 z19 = false := by decide
theorem ex_l3_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d l3 w0 = star (c y1) * d z8 + star (c y0) * d z9 + star (c y3) * d z10
      + star (c y2) * d z11 + star (c y13) * d z16 + star (c y12) * d z17 + star (c y15) * d z18
      + star (c y14) * d z19 := by
  unfold offSum
  rw [inc_l3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_l3_8, flip_l3_9, flip_l3_10, flip_l3_11, flip_l3_16, flip_l3_17, flip_l3_18, flip_l3_19]
  simp only [sg_l3_w0_8, sg_l3_w0_9, sg_l3_w0_10, sg_l3_w0_11, sg_l3_w0_16, sg_l3_w0_17, sg_l3_w0_18, sg_l3_w0_19, SixQubit.signMul_false]
  try ring
theorem sg_l3_p2_8 : SS.bdot p2 z8 = false := by decide
theorem sg_l3_p2_9 : SS.bdot p2 z9 = true := by decide
theorem sg_l3_p2_10 : SS.bdot p2 z10 = false := by decide
theorem sg_l3_p2_11 : SS.bdot p2 z11 = true := by decide
theorem sg_l3_p2_16 : SS.bdot p2 z16 = false := by decide
theorem sg_l3_p2_17 : SS.bdot p2 z17 = true := by decide
theorem sg_l3_p2_18 : SS.bdot p2 z18 = false := by decide
theorem sg_l3_p2_19 : SS.bdot p2 z19 = true := by decide
theorem ex_l3_p2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d l3 p2 = star (c y1) * d z8 - star (c y0) * d z9
      + star (c y3) * d z10 - star (c y2) * d z11 + star (c y13) * d z16 - star (c y12) * d z17
      + star (c y15) * d z18 - star (c y14) * d z19 := by
  unfold offSum
  rw [inc_l3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_l3_8, flip_l3_9, flip_l3_10, flip_l3_11, flip_l3_16, flip_l3_17, flip_l3_18, flip_l3_19]
  simp only [sg_l3_p2_8, sg_l3_p2_9, sg_l3_p2_10, sg_l3_p2_11, sg_l3_p2_16, sg_l3_p2_17, sg_l3_p2_18, sg_l3_p2_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_f4_p1_12 : SS.bdot p1 z12 = false := by decide
theorem sg_f4_p1_13 : SS.bdot p1 z13 = false := by decide
theorem sg_f4_p1_14 : SS.bdot p1 z14 = true := by decide
theorem sg_f4_p1_15 : SS.bdot p1 z15 = true := by decide
theorem sg_f4_p1_16 : SS.bdot p1 z16 = false := by decide
theorem sg_f4_p1_17 : SS.bdot p1 z17 = false := by decide
theorem sg_f4_p1_18 : SS.bdot p1 z18 = true := by decide
theorem sg_f4_p1_19 : SS.bdot p1 z19 = true := by decide
theorem ex_f4_p1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d f4 p1 = star (c y0) * d z12
      + star (c y1) * d z13 - star (c y2) * d z14 - star (c y3) * d z15 + star (c y16) * d z16
      + star (c y17) * d z17 - star (c y18) * d z18 - star (c y19) * d z19 := by
  unfold offSum
  rw [inc_f4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_f4_12, flip_f4_13, flip_f4_14, flip_f4_15, flip_f4_16, flip_f4_17, flip_f4_18, flip_f4_19]
  simp only [sg_f4_p1_12, sg_f4_p1_13, sg_f4_p1_14, sg_f4_p1_15, sg_f4_p1_16, sg_f4_p1_17, sg_f4_p1_18, sg_f4_p1_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_f4_p2_12 : SS.bdot p2 z12 = false := by decide
theorem sg_f4_p2_13 : SS.bdot p2 z13 = true := by decide
theorem sg_f4_p2_14 : SS.bdot p2 z14 = false := by decide
theorem sg_f4_p2_15 : SS.bdot p2 z15 = true := by decide
theorem sg_f4_p2_16 : SS.bdot p2 z16 = false := by decide
theorem sg_f4_p2_17 : SS.bdot p2 z17 = true := by decide
theorem sg_f4_p2_18 : SS.bdot p2 z18 = false := by decide
theorem sg_f4_p2_19 : SS.bdot p2 z19 = true := by decide
theorem ex_f4_p2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d f4 p2 = star (c y0) * d z12 - star (c y1) * d z13
      + star (c y2) * d z14 - star (c y3) * d z15 + star (c y16) * d z16 - star (c y17) * d z17
      + star (c y18) * d z18 - star (c y19) * d z19 := by
  unfold offSum
  rw [inc_f4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_f4_12, flip_f4_13, flip_f4_14, flip_f4_15, flip_f4_16, flip_f4_17, flip_f4_18, flip_f4_19]
  simp only [sg_f4_p2_12, sg_f4_p2_13, sg_f4_p2_14, sg_f4_p2_15, sg_f4_p2_16, sg_f4_p2_17, sg_f4_p2_18, sg_f4_p2_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_k4_w0_12 : SS.bdot w0 z12 = false := by decide
theorem sg_k4_w0_13 : SS.bdot w0 z13 = false := by decide
theorem sg_k4_w0_14 : SS.bdot w0 z14 = false := by decide
theorem sg_k4_w0_15 : SS.bdot w0 z15 = false := by decide
theorem sg_k4_w0_16 : SS.bdot w0 z16 = false := by decide
theorem sg_k4_w0_17 : SS.bdot w0 z17 = false := by decide
theorem sg_k4_w0_18 : SS.bdot w0 z18 = false := by decide
theorem sg_k4_w0_19 : SS.bdot w0 z19 = false := by decide
theorem ex_k4_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d k4 w0 = star (c y2) * d z12 + star (c y3) * d z13 + star (c y0) * d z14
      + star (c y1) * d z15 + star (c y18) * d z16 + star (c y19) * d z17 + star (c y16) * d z18
      + star (c y17) * d z19 := by
  unfold offSum
  rw [inc_k4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_k4_12, flip_k4_13, flip_k4_14, flip_k4_15, flip_k4_16, flip_k4_17, flip_k4_18, flip_k4_19]
  simp only [sg_k4_w0_12, sg_k4_w0_13, sg_k4_w0_14, sg_k4_w0_15, sg_k4_w0_16, sg_k4_w0_17, sg_k4_w0_18, sg_k4_w0_19, SixQubit.signMul_false]
  try ring
theorem sg_k4_p1_12 : SS.bdot p1 z12 = false := by decide
theorem sg_k4_p1_13 : SS.bdot p1 z13 = false := by decide
theorem sg_k4_p1_14 : SS.bdot p1 z14 = true := by decide
theorem sg_k4_p1_15 : SS.bdot p1 z15 = true := by decide
theorem sg_k4_p1_16 : SS.bdot p1 z16 = false := by decide
theorem sg_k4_p1_17 : SS.bdot p1 z17 = false := by decide
theorem sg_k4_p1_18 : SS.bdot p1 z18 = true := by decide
theorem sg_k4_p1_19 : SS.bdot p1 z19 = true := by decide
theorem ex_k4_p1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d k4 p1 = star (c y2) * d z12
      + star (c y3) * d z13 - star (c y0) * d z14 - star (c y1) * d z15 + star (c y18) * d z16
      + star (c y19) * d z17 - star (c y16) * d z18 - star (c y17) * d z19 := by
  unfold offSum
  rw [inc_k4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_k4_12, flip_k4_13, flip_k4_14, flip_k4_15, flip_k4_16, flip_k4_17, flip_k4_18, flip_k4_19]
  simp only [sg_k4_p1_12, sg_k4_p1_13, sg_k4_p1_14, sg_k4_p1_15, sg_k4_p1_16, sg_k4_p1_17, sg_k4_p1_18, sg_k4_p1_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring
theorem sg_l4_w0_12 : SS.bdot w0 z12 = false := by decide
theorem sg_l4_w0_13 : SS.bdot w0 z13 = false := by decide
theorem sg_l4_w0_14 : SS.bdot w0 z14 = false := by decide
theorem sg_l4_w0_15 : SS.bdot w0 z15 = false := by decide
theorem sg_l4_w0_16 : SS.bdot w0 z16 = false := by decide
theorem sg_l4_w0_17 : SS.bdot w0 z17 = false := by decide
theorem sg_l4_w0_18 : SS.bdot w0 z18 = false := by decide
theorem sg_l4_w0_19 : SS.bdot w0 z19 = false := by decide
theorem ex_l4_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d l4 w0 = star (c y1) * d z12 + star (c y0) * d z13 + star (c y3) * d z14
      + star (c y2) * d z15 + star (c y17) * d z16 + star (c y16) * d z17 + star (c y19) * d z18
      + star (c y18) * d z19 := by
  unfold offSum
  rw [inc_l4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_l4_12, flip_l4_13, flip_l4_14, flip_l4_15, flip_l4_16, flip_l4_17, flip_l4_18, flip_l4_19]
  simp only [sg_l4_w0_12, sg_l4_w0_13, sg_l4_w0_14, sg_l4_w0_15, sg_l4_w0_16, sg_l4_w0_17, sg_l4_w0_18, sg_l4_w0_19, SixQubit.signMul_false]
  try ring
theorem sg_l4_p2_12 : SS.bdot p2 z12 = false := by decide
theorem sg_l4_p2_13 : SS.bdot p2 z13 = true := by decide
theorem sg_l4_p2_14 : SS.bdot p2 z14 = false := by decide
theorem sg_l4_p2_15 : SS.bdot p2 z15 = true := by decide
theorem sg_l4_p2_16 : SS.bdot p2 z16 = false := by decide
theorem sg_l4_p2_17 : SS.bdot p2 z17 = true := by decide
theorem sg_l4_p2_18 : SS.bdot p2 z18 = false := by decide
theorem sg_l4_p2_19 : SS.bdot p2 z19 = true := by decide
theorem ex_l4_p2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d l4 p2 = star (c y1) * d z12 - star (c y0) * d z13
      + star (c y3) * d z14 - star (c y2) * d z15 + star (c y17) * d z16 - star (c y16) * d z17
      + star (c y19) * d z18 - star (c y18) * d z19 := by
  unfold offSum
  rw [inc_l4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_l4_12, flip_l4_13, flip_l4_14, flip_l4_15, flip_l4_16, flip_l4_17, flip_l4_18, flip_l4_19]
  simp only [sg_l4_p2_12, sg_l4_p2_13, sg_l4_p2_14, sg_l4_p2_15, sg_l4_p2_16, sg_l4_p2_17, sg_l4_p2_18, sg_l4_p2_19, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

/-! ## The two-flip relations -/

/-- The weight-two flip `g12` isolates the reciprocal pair
`a2† b1 + a1† b2`. -/
theorem two_flip_12 (c d : SS.BitString 6 -> ℂ) (h : offSum c d g12 w0 = 0) :
    Trace5.ip (aa2 c) (bb1 d) + Trace5.ip (aa1 c) (bb2 d) = 0 := by
  rw [ex_g12_w0] at h
  simp only [Trace5.ip, aa2_0, aa2_1, aa2_2, aa2_3, bb1_0, bb1_1, bb1_2, bb1_3, aa1_0, aa1_1, aa1_2, aa1_3, bb2_0, bb2_1, bb2_2, bb2_3]
  linear_combination h
/-- The weight-two flip `g13` isolates the reciprocal pair
`a3† b1 + a1† b3`. -/
theorem two_flip_13 (c d : SS.BitString 6 -> ℂ) (h : offSum c d g13 w0 = 0) :
    Trace5.ip (aa3 c) (bb1 d) + Trace5.ip (aa1 c) (bb3 d) = 0 := by
  rw [ex_g13_w0] at h
  simp only [Trace5.ip, aa3_0, aa3_1, aa3_2, aa3_3, bb1_0, bb1_1, bb1_2, bb1_3, aa1_0, aa1_1, aa1_2, aa1_3, bb3_0, bb3_1, bb3_2, bb3_3]
  linear_combination h
/-- The weight-two flip `g14` isolates the reciprocal pair
`a4† b1 + a1† b4`. -/
theorem two_flip_14 (c d : SS.BitString 6 -> ℂ) (h : offSum c d g14 w0 = 0) :
    Trace5.ip (aa4 c) (bb1 d) + Trace5.ip (aa1 c) (bb4 d) = 0 := by
  rw [ex_g14_w0] at h
  simp only [Trace5.ip, aa4_0, aa4_1, aa4_2, aa4_3, bb1_0, bb1_1, bb1_2, bb1_3, aa1_0, aa1_1, aa1_2, aa1_3, bb4_0, bb4_1, bb4_2, bb4_3]
  linear_combination h
/-- The weight-two flip `g23` isolates the reciprocal pair
`a3† b2 + a2† b3`. -/
theorem two_flip_23 (c d : SS.BitString 6 -> ℂ) (h : offSum c d g23 w0 = 0) :
    Trace5.ip (aa3 c) (bb2 d) + Trace5.ip (aa2 c) (bb3 d) = 0 := by
  rw [ex_g23_w0] at h
  simp only [Trace5.ip, aa3_0, aa3_1, aa3_2, aa3_3, bb2_0, bb2_1, bb2_2, bb2_3, aa2_0, aa2_1, aa2_2, aa2_3, bb3_0, bb3_1, bb3_2, bb3_3]
  linear_combination h
/-- The weight-two flip `g24` isolates the reciprocal pair
`a4† b2 + a2† b4`. -/
theorem two_flip_24 (c d : SS.BitString 6 -> ℂ) (h : offSum c d g24 w0 = 0) :
    Trace5.ip (aa4 c) (bb2 d) + Trace5.ip (aa2 c) (bb4 d) = 0 := by
  rw [ex_g24_w0] at h
  simp only [Trace5.ip, aa4_0, aa4_1, aa4_2, aa4_3, bb2_0, bb2_1, bb2_2, bb2_3, aa2_0, aa2_1, aa2_2, aa2_3, bb4_0, bb4_1, bb4_2, bb4_3]
  linear_combination h
/-- The weight-two flip `g34` isolates the reciprocal pair
`a4† b3 + a3† b4`. -/
theorem two_flip_34 (c d : SS.BitString 6 -> ℂ) (h : offSum c d g34 w0 = 0) :
    Trace5.ip (aa4 c) (bb3 d) + Trace5.ip (aa3 c) (bb4 d) = 0 := by
  rw [ex_g34_w0] at h
  simp only [Trace5.ip, aa4_0, aa4_1, aa4_2, aa4_3, bb3_0, bb3_1, bb3_2, bb3_3, aa3_0, aa3_1, aa3_2, aa3_3, bb4_0, bb4_1, bb4_2, bb4_3]
  linear_combination h

/-! ## The frame reduction -/

/-- **Orbit 5: the frame reduction.**  From the moment polytope, the eight
one-flip rows that separate the two anchors, and the twelve diagonal rows on
the free pair, the anchor `u` is orthogonal to all four bottom vectors and the
two frame operators coincide. -/
theorem frame_reduction (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem (Complex.normSq  (c  y0))  (Complex.normSq  (c  y1))  (Complex.normSq  (c  y2))
       (Complex.normSq  (c  y3))  (Complex.normSq  (c  y4))  (Complex.normSq  (c  y5))  (Complex.normSq
       (c  y6))  (Complex.normSq  (c  y7))  (Complex.normSq  (c  y8))  (Complex.normSq  (c  y9))
       (Complex.normSq  (c  y10))  (Complex.normSq  (c  y11))  (Complex.normSq  (c  y12))
       (Complex.normSq  (c  y13))  (Complex.normSq  (c  y14))  (Complex.normSq  (c  y15))
       (Complex.normSq  (c  y16))  (Complex.normSq  (c  y17))  (Complex.normSq  (c  y18))
       (Complex.normSq  (c  y19))  (Complex.normSq  (d  z0))  (Complex.normSq  (d  z1))  (Complex.normSq
       (d  z2))  (Complex.normSq  (d  z3))  (Complex.normSq  (d  z4))  (Complex.normSq  (d  z5))
       (Complex.normSq  (d  z6))  (Complex.normSq  (d  z7))  (Complex.normSq  (d  z8))  (Complex.normSq
       (d  z9))  (Complex.normSq  (d  z10))  (Complex.normSq  (d  z11))  (Complex.normSq  (d  z12))
       (Complex.normSq  (d  z13))  (Complex.normSq  (d  z14))  (Complex.normSq  (d  z15))
       (Complex.normSq  (d  z16))  (Complex.normSq  (d  z17))  (Complex.normSq  (d  z18))
       (Complex.normSq  (d  z19)))
    (ho1a : offSum c d f1 w0 = 0)
    (ho1b : offSum c d f1 f2 = 0)
    (ho2a : offSum c d f2 w0 = 0)
    (ho2b : offSum c d f2 f3 = 0)
    (ho3a : offSum c d f3 w0 = 0)
    (ho3b : offSum c d f3 f4 = 0)
    (ho4a : offSum c d f4 w0 = 0)
    (ho4b : offSum c d f4 f1 = 0)
    (hd11 : diagBot c p1 w0 = diagTop d p1 w0)
    (hd12 : diagBot c p1 w1 = diagTop d p1 w1)
    (hd13 : diagBot c p1 w2 = diagTop d p1 w2)
    (hd14 : diagBot c p1 w3 = diagTop d p1 w3)
    (hd21 : diagBot c p2 w0 = diagTop d p2 w0)
    (hd22 : diagBot c p2 w1 = diagTop d p2 w1)
    (hd23 : diagBot c p2 w2 = diagTop d p2 w2)
    (hd24 : diagBot c p2 w3 = diagTop d p2 w3)
    (hd31 : diagBot c p3 w0 = diagTop d p3 w0)
    (hd32 : diagBot c p3 w1 = diagTop d p3 w1)
    (hd33 : diagBot c p3 w2 = diagTop d p3 w2)
    (hd34 : diagBot c p3 w3 = diagTop d p3 w3)
    : Trace5.ip (uu c) (aa1 c) = 0 ∧ Trace5.ip (uu c) (aa2 c) = 0 ∧
      Trace5.ip (uu c) (aa3 c) = 0 ∧ Trace5.ip (uu c) (aa4 c) = 0 ∧
      Trace5.ip (aa1 c) (vv d) = 0 ∧ Trace5.ip (aa2 c) (vv d) = 0 ∧
      Trace5.ip (aa3 c) (vv d) = 0 ∧ Trace5.ip (aa4 c) (vv d) = 0 ∧
      Trace5.ip (uu c) (bb1 d) = 0 ∧ Trace5.ip (uu c) (bb2 d) = 0 ∧
      Trace5.ip (uu c) (bb3 d) = 0 ∧ Trace5.ip (uu c) (bb4 d) = 0 ∧
      ∀ k l : Fin 4, Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) k l
        = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) k l := by
  obtain ⟨nu, na1, na2, na3, na4, nb1, nb2, nb3, nb4, nv⟩ := hm.norms
  obtain ⟨mg0, mg1, mg2, mg3⟩ := hm.marginal
  have hnuu : Trace5.nsq (uu c) = 1/3 := by
    simp only [Trace5.nsq, uu_0, uu_1, uu_2, uu_3]
    linarith
  have hnaa1 : Trace5.nsq (aa1 c) = 1/6 := by
    simp only [Trace5.nsq, aa1_0, aa1_1, aa1_2, aa1_3]
    linarith
  have hnaa2 : Trace5.nsq (aa2 c) = 1/6 := by
    simp only [Trace5.nsq, aa2_0, aa2_1, aa2_2, aa2_3]
    linarith
  have hnaa3 : Trace5.nsq (aa3 c) = 1/6 := by
    simp only [Trace5.nsq, aa3_0, aa3_1, aa3_2, aa3_3]
    linarith
  have hnaa4 : Trace5.nsq (aa4 c) = 1/6 := by
    simp only [Trace5.nsq, aa4_0, aa4_1, aa4_2, aa4_3]
    linarith
  have hnbb1 : Trace5.nsq (bb1 d) = 1/6 := by
    simp only [Trace5.nsq, bb1_0, bb1_1, bb1_2, bb1_3]
    linarith
  have hnbb2 : Trace5.nsq (bb2 d) = 1/6 := by
    simp only [Trace5.nsq, bb2_0, bb2_1, bb2_2, bb2_3]
    linarith
  have hnbb3 : Trace5.nsq (bb3 d) = 1/6 := by
    simp only [Trace5.nsq, bb3_0, bb3_1, bb3_2, bb3_3]
    linarith
  have hnbb4 : Trace5.nsq (bb4 d) = 1/6 := by
    simp only [Trace5.nsq, bb4_0, bb4_1, bb4_2, bb4_3]
    linarith
  have hnvv : Trace5.nsq (vv d) = 1/3 := by
    simp only [Trace5.nsq, vv_0, vv_1, vv_2, vv_3]
    linarith
  rw [ex_f1_w0] at ho1a
  rw [ex_f1_f2] at ho1b
  rw [ex_f2_w0] at ho2a
  rw [ex_f2_f3] at ho2b
  rw [ex_f3_w0] at ho3a
  rw [ex_f3_f4] at ho3b
  rw [ex_f4_w0] at ho4a
  rw [ex_f4_f1] at ho4b
  have hq1 : Trace5.ip (uu c) (bb1 d) = 0 := by
    simp only [Trace5.ip, uu_0, uu_1, uu_2, uu_3, bb1_0, bb1_1, bb1_2, bb1_3]
    linear_combination (1/2 : ℂ) * ho1a + (1/2 : ℂ) * ho1b
  have hq2 : Trace5.ip (uu c) (bb2 d) = 0 := by
    simp only [Trace5.ip, uu_0, uu_1, uu_2, uu_3, bb2_0, bb2_1, bb2_2, bb2_3]
    linear_combination (1/2 : ℂ) * ho2a + (1/2 : ℂ) * ho2b
  have hq3 : Trace5.ip (uu c) (bb3 d) = 0 := by
    simp only [Trace5.ip, uu_0, uu_1, uu_2, uu_3, bb3_0, bb3_1, bb3_2, bb3_3]
    linear_combination (1/2 : ℂ) * ho3a + (1/2 : ℂ) * ho3b
  have hq4 : Trace5.ip (uu c) (bb4 d) = 0 := by
    simp only [Trace5.ip, uu_0, uu_1, uu_2, uu_3, bb4_0, bb4_1, bb4_2, bb4_3]
    linear_combination (1/2 : ℂ) * ho4a + (1/2 : ℂ) * ho4b
  have hav1 : Trace5.ip (aa1 c) (vv d) = 0 := by
    simp only [Trace5.ip, aa1_0, aa1_1, aa1_2, aa1_3, vv_0, vv_1, vv_2, vv_3]
    linear_combination (1/2 : ℂ) * ho1a - (1/2 : ℂ) * ho1b
  have hav2 : Trace5.ip (aa2 c) (vv d) = 0 := by
    simp only [Trace5.ip, aa2_0, aa2_1, aa2_2, aa2_3, vv_0, vv_1, vv_2, vv_3]
    linear_combination (1/2 : ℂ) * ho2a - (1/2 : ℂ) * ho2b
  have hav3 : Trace5.ip (aa3 c) (vv d) = 0 := by
    simp only [Trace5.ip, aa3_0, aa3_1, aa3_2, aa3_3, vv_0, vv_1, vv_2, vv_3]
    linear_combination (1/2 : ℂ) * ho3a - (1/2 : ℂ) * ho3b
  have hav4 : Trace5.ip (aa4 c) (vv d) = 0 := by
    simp only [Trace5.ip, aa4_0, aa4_1, aa4_2, aa4_3, vv_0, vv_1, vv_2, vv_3]
    linear_combination (1/2 : ℂ) * ho4a - (1/2 : ℂ) * ho4b
  rw [dexB_p1_w0, dexT_p1_w0] at hd11
  rw [dexB_p1_w1, dexT_p1_w1] at hd12
  rw [dexB_p1_w2, dexT_p1_w2] at hd13
  rw [dexB_p1_w3, dexT_p1_w3] at hd14
  rw [dexB_p2_w0, dexT_p2_w0] at hd21
  rw [dexB_p2_w1, dexT_p2_w1] at hd22
  rw [dexB_p2_w2, dexT_p2_w2] at hd23
  rw [dexB_p2_w3, dexT_p2_w3] at hd24
  rw [dexB_p3_w0, dexT_p3_w0] at hd31
  rw [dexB_p3_w1, dexT_p3_w1] at hd32
  rw [dexB_p3_w2, dexT_p3_w2] at hd33
  rw [dexB_p3_w3, dexT_p3_w3] at hd34
  have fk00 : uu c 0 * star (uu c 0)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 0 0
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 0 0
        + vv d 0 * star (vv d 0) := by
    simp only [Trace5.fr, uu_0, uu_0, aa1_0, aa2_0, aa3_0, aa4_0, aa1_0, aa2_0, aa3_0, aa4_0, vv_0, vv_0, bb1_0, bb2_0, bb3_0, bb4_0, bb1_0, bb2_0, bb3_0, bb4_0]
    have hc : ((Complex.normSq (c y0) + Complex.normSq (c y4) + Complex.normSq (c y8)
        + Complex.normSq (c y12) + Complex.normSq (c y16)
        : Real) : ℂ) = ((Complex.normSq (d z0) + Complex.normSq (d z4) + Complex.normSq (d z8)
        + Complex.normSq (d z12) + Complex.normSq (d z16) : Real) : ℂ) := by
      exact_mod_cast mg0
    push_cast [← SixQubit.star_mul_self] at hc
    linear_combination hc
  have fk01 : uu c 0 * star (uu c 1)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 0 1
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 0 1
        + vv d 0 * star (vv d 1) := by
    simp only [Trace5.fr, uu_0, uu_1, aa1_0, aa2_0, aa3_0, aa4_0, aa1_1, aa2_1, aa3_1, aa4_1, vv_0, vv_1, bb1_0, bb2_0, bb3_0, bb4_0, bb1_1, bb2_1, bb3_1, bb4_1]
    linear_combination (1/4 : ℂ) * hd21 + (1/4 : ℂ) * hd22 + (1/4 : ℂ) * hd23 + (1/4 : ℂ) * hd24
  have fk02 : uu c 0 * star (uu c 2)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 0 2
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 0 2
        + vv d 0 * star (vv d 2) := by
    simp only [Trace5.fr, uu_0, uu_2, aa1_0, aa2_0, aa3_0, aa4_0, aa1_2, aa2_2, aa3_2, aa4_2, vv_0, vv_2, bb1_0, bb2_0, bb3_0, bb4_0, bb1_2, bb2_2, bb3_2, bb4_2]
    linear_combination (1/4 : ℂ) * hd11 + (1/4 : ℂ) * hd12 + (1/4 : ℂ) * hd13 + (1/4 : ℂ) * hd14
  have fk03 : uu c 0 * star (uu c 3)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 0 3
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 0 3
        + vv d 0 * star (vv d 3) := by
    simp only [Trace5.fr, uu_0, uu_3, aa1_0, aa2_0, aa3_0, aa4_0, aa1_3, aa2_3, aa3_3, aa4_3, vv_0, vv_3, bb1_0, bb2_0, bb3_0, bb4_0, bb1_3, bb2_3, bb3_3, bb4_3]
    linear_combination (1/4 : ℂ) * hd31 + (1/4 : ℂ) * hd32 + (1/4 : ℂ) * hd33 + (1/4 : ℂ) * hd34
  have fk10 : uu c 1 * star (uu c 0)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 1 0
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 1 0
        + vv d 1 * star (vv d 0) := by
    simp only [Trace5.fr, uu_1, uu_0, aa1_1, aa2_1, aa3_1, aa4_1, aa1_0, aa2_0, aa3_0, aa4_0, vv_1, vv_0, bb1_1, bb2_1, bb3_1, bb4_1, bb1_0, bb2_0, bb3_0, bb4_0]
    linear_combination (1/4 : ℂ) * hd21 + (1/4 : ℂ) * hd22 + (-1/4 : ℂ) * hd23 + (-1/4 : ℂ) * hd24
  have fk11 : uu c 1 * star (uu c 1)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 1 1
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 1 1
        + vv d 1 * star (vv d 1) := by
    simp only [Trace5.fr, uu_1, uu_1, aa1_1, aa2_1, aa3_1, aa4_1, aa1_1, aa2_1, aa3_1, aa4_1, vv_1, vv_1, bb1_1, bb2_1, bb3_1, bb4_1, bb1_1, bb2_1, bb3_1, bb4_1]
    have hc : ((Complex.normSq (c y1) + Complex.normSq (c y5) + Complex.normSq (c y9)
        + Complex.normSq (c y13) + Complex.normSq (c y17)
        : Real) : ℂ) = ((Complex.normSq (d z1) + Complex.normSq (d z5) + Complex.normSq (d z9)
        + Complex.normSq (d z13) + Complex.normSq (d z17) : Real) : ℂ) := by
      exact_mod_cast mg1
    push_cast [← SixQubit.star_mul_self] at hc
    linear_combination hc
  have fk12 : uu c 1 * star (uu c 2)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 1 2
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 1 2
        + vv d 1 * star (vv d 2) := by
    simp only [Trace5.fr, uu_1, uu_2, aa1_1, aa2_1, aa3_1, aa4_1, aa1_2, aa2_2, aa3_2, aa4_2, vv_1, vv_2, bb1_1, bb2_1, bb3_1, bb4_1, bb1_2, bb2_2, bb3_2, bb4_2]
    linear_combination (1/4 : ℂ) * hd31 + (1/4 : ℂ) * hd32 + (-1/4 : ℂ) * hd33 + (-1/4 : ℂ) * hd34
  have fk13 : uu c 1 * star (uu c 3)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 1 3
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 1 3
        + vv d 1 * star (vv d 3) := by
    simp only [Trace5.fr, uu_1, uu_3, aa1_1, aa2_1, aa3_1, aa4_1, aa1_3, aa2_3, aa3_3, aa4_3, vv_1, vv_3, bb1_1, bb2_1, bb3_1, bb4_1, bb1_3, bb2_3, bb3_3, bb4_3]
    linear_combination (1/4 : ℂ) * hd11 + (1/4 : ℂ) * hd12 + (-1/4 : ℂ) * hd13 + (-1/4 : ℂ) * hd14
  have fk20 : uu c 2 * star (uu c 0)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 2 0
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 2 0
        + vv d 2 * star (vv d 0) := by
    simp only [Trace5.fr, uu_2, uu_0, aa1_2, aa2_2, aa3_2, aa4_2, aa1_0, aa2_0, aa3_0, aa4_0, vv_2, vv_0, bb1_2, bb2_2, bb3_2, bb4_2, bb1_0, bb2_0, bb3_0, bb4_0]
    linear_combination (1/4 : ℂ) * hd11 + (-1/4 : ℂ) * hd12 + (1/4 : ℂ) * hd13 + (-1/4 : ℂ) * hd14
  have fk21 : uu c 2 * star (uu c 1)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 2 1
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 2 1
        + vv d 2 * star (vv d 1) := by
    simp only [Trace5.fr, uu_2, uu_1, aa1_2, aa2_2, aa3_2, aa4_2, aa1_1, aa2_1, aa3_1, aa4_1, vv_2, vv_1, bb1_2, bb2_2, bb3_2, bb4_2, bb1_1, bb2_1, bb3_1, bb4_1]
    linear_combination (1/4 : ℂ) * hd31 + (-1/4 : ℂ) * hd32 + (1/4 : ℂ) * hd33 + (-1/4 : ℂ) * hd34
  have fk22 : uu c 2 * star (uu c 2)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 2 2
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 2 2
        + vv d 2 * star (vv d 2) := by
    simp only [Trace5.fr, uu_2, uu_2, aa1_2, aa2_2, aa3_2, aa4_2, aa1_2, aa2_2, aa3_2, aa4_2, vv_2, vv_2, bb1_2, bb2_2, bb3_2, bb4_2, bb1_2, bb2_2, bb3_2, bb4_2]
    have hc : ((Complex.normSq (c y2) + Complex.normSq (c y6) + Complex.normSq (c y10)
        + Complex.normSq (c y14) + Complex.normSq (c y18)
        : Real) : ℂ) = ((Complex.normSq (d z2) + Complex.normSq (d z6) + Complex.normSq (d z10)
        + Complex.normSq (d z14) + Complex.normSq (d z18) : Real) : ℂ) := by
      exact_mod_cast mg2
    push_cast [← SixQubit.star_mul_self] at hc
    linear_combination hc
  have fk23 : uu c 2 * star (uu c 3)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 2 3
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 2 3
        + vv d 2 * star (vv d 3) := by
    simp only [Trace5.fr, uu_2, uu_3, aa1_2, aa2_2, aa3_2, aa4_2, aa1_3, aa2_3, aa3_3, aa4_3, vv_2, vv_3, bb1_2, bb2_2, bb3_2, bb4_2, bb1_3, bb2_3, bb3_3, bb4_3]
    linear_combination (1/4 : ℂ) * hd21 + (-1/4 : ℂ) * hd22 + (1/4 : ℂ) * hd23 + (-1/4 : ℂ) * hd24
  have fk30 : uu c 3 * star (uu c 0)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 3 0
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 3 0
        + vv d 3 * star (vv d 0) := by
    simp only [Trace5.fr, uu_3, uu_0, aa1_3, aa2_3, aa3_3, aa4_3, aa1_0, aa2_0, aa3_0, aa4_0, vv_3, vv_0, bb1_3, bb2_3, bb3_3, bb4_3, bb1_0, bb2_0, bb3_0, bb4_0]
    linear_combination (1/4 : ℂ) * hd31 + (-1/4 : ℂ) * hd32 + (-1/4 : ℂ) * hd33 + (1/4 : ℂ) * hd34
  have fk31 : uu c 3 * star (uu c 1)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 3 1
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 3 1
        + vv d 3 * star (vv d 1) := by
    simp only [Trace5.fr, uu_3, uu_1, aa1_3, aa2_3, aa3_3, aa4_3, aa1_1, aa2_1, aa3_1, aa4_1, vv_3, vv_1, bb1_3, bb2_3, bb3_3, bb4_3, bb1_1, bb2_1, bb3_1, bb4_1]
    linear_combination (1/4 : ℂ) * hd11 + (-1/4 : ℂ) * hd12 + (-1/4 : ℂ) * hd13 + (1/4 : ℂ) * hd14
  have fk32 : uu c 3 * star (uu c 2)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 3 2
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 3 2
        + vv d 3 * star (vv d 2) := by
    simp only [Trace5.fr, uu_3, uu_2, aa1_3, aa2_3, aa3_3, aa4_3, aa1_2, aa2_2, aa3_2, aa4_2, vv_3, vv_2, bb1_3, bb2_3, bb3_3, bb4_3, bb1_2, bb2_2, bb3_2, bb4_2]
    linear_combination (1/4 : ℂ) * hd21 + (-1/4 : ℂ) * hd22 + (-1/4 : ℂ) * hd23 + (1/4 : ℂ) * hd24
  have fk33 : uu c 3 * star (uu c 3)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 3 3
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 3 3
        + vv d 3 * star (vv d 3) := by
    simp only [Trace5.fr, uu_3, uu_3, aa1_3, aa2_3, aa3_3, aa4_3, aa1_3, aa2_3, aa3_3, aa4_3, vv_3, vv_3, bb1_3, bb2_3, bb3_3, bb4_3, bb1_3, bb2_3, bb3_3, bb4_3]
    have hc : ((Complex.normSq (c y3) + Complex.normSq (c y7) + Complex.normSq (c y11)
        + Complex.normSq (c y15) + Complex.normSq (c y19)
        : Real) : ℂ) = ((Complex.normSq (d z3) + Complex.normSq (d z7) + Complex.normSq (d z11)
        + Complex.normSq (d z15) + Complex.normSq (d z19) : Real) : ℂ) := by
      exact_mod_cast mg3
    push_cast [← SixQubit.star_mul_self] at hc
    linear_combination hc
  have hf : ∀ k l : Fin 4, uu c k * star (uu c l)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) k l
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) k l + vv d k * star (vv d l) := by
    intro k l
    fin_cases k <;> fin_cases l
    exacts [fk00 , fk01 , fk02 , fk03 , fk10 , fk11 , fk12 , fk13 , fk20 , fk21 , fk22 , fk23 , fk30
      , fk31 , fk32 , fk33]
  obtain ⟨t1, t2, t3, t4, tf⟩ := Trace5.cs_tight (uu c) (vv d) (aa1 c) (aa2 c) (aa3 c)
    (aa4 c) (bb1 d) (bb2 d) (bb3 d) (bb4 d) hnuu hnvv hq1 hq2 hq3 hq4 hf
  exact ⟨t1, t2, t3, t4, hav1, hav2, hav3, hav4, hq1, hq2, hq3, hq4, tf⟩

/-! ## The headline no-go -/

/-- **Orbit 5 admits no exact completion.**  The hypotheses are exactly the
moment polytope, twenty-eight off-diagonal Knill--Laflamme rows of weight at
most two, and the twelve diagonal rows supported on the free pair.  No
algebraic normalisation is assumed: the Schmidt gauge of the paper is replaced
by the scalar invariant `Flip5.dsc` and the anchor rephasing is discharged by
`Flip5.anchor_scale`. -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem (Complex.normSq  (c  y0))  (Complex.normSq  (c  y1))  (Complex.normSq  (c  y2))
       (Complex.normSq  (c  y3))  (Complex.normSq  (c  y4))  (Complex.normSq  (c  y5))  (Complex.normSq
       (c  y6))  (Complex.normSq  (c  y7))  (Complex.normSq  (c  y8))  (Complex.normSq  (c  y9))
       (Complex.normSq  (c  y10))  (Complex.normSq  (c  y11))  (Complex.normSq  (c  y12))
       (Complex.normSq  (c  y13))  (Complex.normSq  (c  y14))  (Complex.normSq  (c  y15))
       (Complex.normSq  (c  y16))  (Complex.normSq  (c  y17))  (Complex.normSq  (c  y18))
       (Complex.normSq  (c  y19))  (Complex.normSq  (d  z0))  (Complex.normSq  (d  z1))  (Complex.normSq
       (d  z2))  (Complex.normSq  (d  z3))  (Complex.normSq  (d  z4))  (Complex.normSq  (d  z5))
       (Complex.normSq  (d  z6))  (Complex.normSq  (d  z7))  (Complex.normSq  (d  z8))  (Complex.normSq
       (d  z9))  (Complex.normSq  (d  z10))  (Complex.normSq  (d  z11))  (Complex.normSq  (d  z12))
       (Complex.normSq  (d  z13))  (Complex.normSq  (d  z14))  (Complex.normSq  (d  z15))
       (Complex.normSq  (d  z16))  (Complex.normSq  (d  z17))  (Complex.normSq  (d  z18))
       (Complex.normSq  (d  z19)))
    (ho1a : offSum c d f1 w0 = 0)
    (ho1b : offSum c d f1 f2 = 0)
    (ho2a : offSum c d f2 w0 = 0)
    (ho2b : offSum c d f2 f3 = 0)
    (ho3a : offSum c d f3 w0 = 0)
    (ho3b : offSum c d f3 f4 = 0)
    (ho4a : offSum c d f4 w0 = 0)
    (ho4b : offSum c d f4 f1 = 0)
    (hz11 : offSum c d f1 p1 = 0)
    (hz12 : offSum c d f1 p2 = 0)
    (hk10 : offSum c d k1 w0 = 0)
    (hk11 : offSum c d k1 p1 = 0)
    (hl10 : offSum c d l1 w0 = 0)
    (hl12 : offSum c d l1 p2 = 0)
    (hz21 : offSum c d f2 p1 = 0)
    (hz22 : offSum c d f2 p2 = 0)
    (hk20 : offSum c d k2 w0 = 0)
    (hk21 : offSum c d k2 p1 = 0)
    (hl20 : offSum c d l2 w0 = 0)
    (hl22 : offSum c d l2 p2 = 0)
    (hz31 : offSum c d f3 p1 = 0)
    (hz32 : offSum c d f3 p2 = 0)
    (hk30 : offSum c d k3 w0 = 0)
    (hk31 : offSum c d k3 p1 = 0)
    (hl30 : offSum c d l3 w0 = 0)
    (hl32 : offSum c d l3 p2 = 0)
    (hz41 : offSum c d f4 p1 = 0)
    (hz42 : offSum c d f4 p2 = 0)
    (hk40 : offSum c d k4 w0 = 0)
    (hk41 : offSum c d k4 p1 = 0)
    (hl40 : offSum c d l4 w0 = 0)
    (hl42 : offSum c d l4 p2 = 0)
    (ht12 : offSum c d g12 w0 = 0)
    (ht13 : offSum c d g13 w0 = 0)
    (ht14 : offSum c d g14 w0 = 0)
    (ht23 : offSum c d g23 w0 = 0)
    (ht24 : offSum c d g24 w0 = 0)
    (ht34 : offSum c d g34 w0 = 0)
    (hd11 : diagBot c p1 w0 = diagTop d p1 w0)
    (hd12 : diagBot c p1 w1 = diagTop d p1 w1)
    (hd13 : diagBot c p1 w2 = diagTop d p1 w2)
    (hd14 : diagBot c p1 w3 = diagTop d p1 w3)
    (hd21 : diagBot c p2 w0 = diagTop d p2 w0)
    (hd22 : diagBot c p2 w1 = diagTop d p2 w1)
    (hd23 : diagBot c p2 w2 = diagTop d p2 w2)
    (hd24 : diagBot c p2 w3 = diagTop d p2 w3)
    (hd31 : diagBot c p3 w0 = diagTop d p3 w0)
    (hd32 : diagBot c p3 w1 = diagTop d p3 w1)
    (hd33 : diagBot c p3 w2 = diagTop d p3 w2)
    (hd34 : diagBot c p3 w3 = diagTop d p3 w3)
    : False := by
  obtain ⟨nu, na1, na2, na3, na4, nb1, nb2, nb3, nb4, nv⟩ := hm.norms
  obtain ⟨mg0, mg1, mg2, mg3⟩ := hm.marginal
  have hnuu : Trace5.nsq (uu c) = 1/3 := by
    simp only [Trace5.nsq, uu_0, uu_1, uu_2, uu_3]
    linarith
  have hnaa1 : Trace5.nsq (aa1 c) = 1/6 := by
    simp only [Trace5.nsq, aa1_0, aa1_1, aa1_2, aa1_3]
    linarith
  have hnaa2 : Trace5.nsq (aa2 c) = 1/6 := by
    simp only [Trace5.nsq, aa2_0, aa2_1, aa2_2, aa2_3]
    linarith
  have hnaa3 : Trace5.nsq (aa3 c) = 1/6 := by
    simp only [Trace5.nsq, aa3_0, aa3_1, aa3_2, aa3_3]
    linarith
  have hnaa4 : Trace5.nsq (aa4 c) = 1/6 := by
    simp only [Trace5.nsq, aa4_0, aa4_1, aa4_2, aa4_3]
    linarith
  have hnbb1 : Trace5.nsq (bb1 d) = 1/6 := by
    simp only [Trace5.nsq, bb1_0, bb1_1, bb1_2, bb1_3]
    linarith
  have hnbb2 : Trace5.nsq (bb2 d) = 1/6 := by
    simp only [Trace5.nsq, bb2_0, bb2_1, bb2_2, bb2_3]
    linarith
  have hnbb3 : Trace5.nsq (bb3 d) = 1/6 := by
    simp only [Trace5.nsq, bb3_0, bb3_1, bb3_2, bb3_3]
    linarith
  have hnbb4 : Trace5.nsq (bb4 d) = 1/6 := by
    simp only [Trace5.nsq, bb4_0, bb4_1, bb4_2, bb4_3]
    linarith
  have hnvv : Trace5.nsq (vv d) = 1/3 := by
    simp only [Trace5.nsq, vv_0, vv_1, vv_2, vv_3]
    linarith
  have x12 : Trace5.ip (aa1 c) (bb2 d) + Trace5.ip (aa2 c) (bb1 d) = 0 := by
    linear_combination two_flip_12 c d ht12
  have x13 : Trace5.ip (aa1 c) (bb3 d) + Trace5.ip (aa3 c) (bb1 d) = 0 := by
    linear_combination two_flip_13 c d ht13
  have x14 : Trace5.ip (aa1 c) (bb4 d) + Trace5.ip (aa4 c) (bb1 d) = 0 := by
    linear_combination two_flip_14 c d ht14
  have x23 : Trace5.ip (aa2 c) (bb3 d) + Trace5.ip (aa3 c) (bb2 d) = 0 := by
    linear_combination two_flip_23 c d ht23
  have x24 : Trace5.ip (aa2 c) (bb4 d) + Trace5.ip (aa4 c) (bb2 d) = 0 := by
    linear_combination two_flip_24 c d ht24
  have x34 : Trace5.ip (aa3 c) (bb4 d) + Trace5.ip (aa4 c) (bb3 d) = 0 := by
    linear_combination two_flip_34 c d ht34
  rw [ex_f1_f2] at ho1b
  rw [ex_f2_f3] at ho2b
  rw [ex_f3_f4] at ho3b
  rw [ex_f4_f1] at ho4b
  rw [ex_f1_w0] at ho1a
  rw [ex_f1_p1] at hz11
  rw [ex_f1_p2] at hz12
  rw [ex_k1_w0] at hk10
  rw [ex_k1_p1] at hk11
  rw [ex_l1_w0] at hl10
  rw [ex_l1_p2] at hl12
  rw [ex_f2_w0] at ho2a
  rw [ex_f2_p1] at hz21
  rw [ex_f2_p2] at hz22
  rw [ex_k2_w0] at hk20
  rw [ex_k2_p1] at hk21
  rw [ex_l2_w0] at hl20
  rw [ex_l2_p2] at hl22
  rw [ex_f3_w0] at ho3a
  rw [ex_f3_p1] at hz31
  rw [ex_f3_p2] at hz32
  rw [ex_k3_w0] at hk30
  rw [ex_k3_p1] at hk31
  rw [ex_l3_w0] at hl30
  rw [ex_l3_p2] at hl32
  rw [ex_f4_w0] at ho4a
  rw [ex_f4_p1] at hz41
  rw [ex_f4_p2] at hz42
  rw [ex_k4_w0] at hk40
  rw [ex_k4_p1] at hk41
  rw [ex_l4_w0] at hl40
  rw [ex_l4_p2] at hl42
  have hq1 : Trace5.ip (uu c) (bb1 d) = 0 := by
    simp only [Trace5.ip, uu_0, uu_1, uu_2, uu_3, bb1_0, bb1_1, bb1_2, bb1_3]
    linear_combination (1/2 : ℂ) * ho1a + (1/2 : ℂ) * ho1b
  have hq2 : Trace5.ip (uu c) (bb2 d) = 0 := by
    simp only [Trace5.ip, uu_0, uu_1, uu_2, uu_3, bb2_0, bb2_1, bb2_2, bb2_3]
    linear_combination (1/2 : ℂ) * ho2a + (1/2 : ℂ) * ho2b
  have hq3 : Trace5.ip (uu c) (bb3 d) = 0 := by
    simp only [Trace5.ip, uu_0, uu_1, uu_2, uu_3, bb3_0, bb3_1, bb3_2, bb3_3]
    linear_combination (1/2 : ℂ) * ho3a + (1/2 : ℂ) * ho3b
  have hq4 : Trace5.ip (uu c) (bb4 d) = 0 := by
    simp only [Trace5.ip, uu_0, uu_1, uu_2, uu_3, bb4_0, bb4_1, bb4_2, bb4_3]
    linear_combination (1/2 : ℂ) * ho4a + (1/2 : ℂ) * ho4b
  rw [dexB_p1_w0, dexT_p1_w0] at hd11
  rw [dexB_p1_w1, dexT_p1_w1] at hd12
  rw [dexB_p1_w2, dexT_p1_w2] at hd13
  rw [dexB_p1_w3, dexT_p1_w3] at hd14
  rw [dexB_p2_w0, dexT_p2_w0] at hd21
  rw [dexB_p2_w1, dexT_p2_w1] at hd22
  rw [dexB_p2_w2, dexT_p2_w2] at hd23
  rw [dexB_p2_w3, dexT_p2_w3] at hd24
  rw [dexB_p3_w0, dexT_p3_w0] at hd31
  rw [dexB_p3_w1, dexT_p3_w1] at hd32
  rw [dexB_p3_w2, dexT_p3_w2] at hd33
  rw [dexB_p3_w3, dexT_p3_w3] at hd34
  have fk00 : uu c 0 * star (uu c 0)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 0 0
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 0 0
        + vv d 0 * star (vv d 0) := by
    simp only [Trace5.fr, uu_0, uu_0, aa1_0, aa2_0, aa3_0, aa4_0, aa1_0, aa2_0, aa3_0, aa4_0, vv_0, vv_0, bb1_0, bb2_0, bb3_0, bb4_0, bb1_0, bb2_0, bb3_0, bb4_0]
    have hc : ((Complex.normSq (c y0) + Complex.normSq (c y4) + Complex.normSq (c y8)
        + Complex.normSq (c y12) + Complex.normSq (c y16)
        : Real) : ℂ) = ((Complex.normSq (d z0) + Complex.normSq (d z4) + Complex.normSq (d z8)
        + Complex.normSq (d z12) + Complex.normSq (d z16) : Real) : ℂ) := by
      exact_mod_cast mg0
    push_cast [← SixQubit.star_mul_self] at hc
    linear_combination hc
  have fk01 : uu c 0 * star (uu c 1)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 0 1
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 0 1
        + vv d 0 * star (vv d 1) := by
    simp only [Trace5.fr, uu_0, uu_1, aa1_0, aa2_0, aa3_0, aa4_0, aa1_1, aa2_1, aa3_1, aa4_1, vv_0, vv_1, bb1_0, bb2_0, bb3_0, bb4_0, bb1_1, bb2_1, bb3_1, bb4_1]
    linear_combination (1/4 : ℂ) * hd21 + (1/4 : ℂ) * hd22 + (1/4 : ℂ) * hd23 + (1/4 : ℂ) * hd24
  have fk02 : uu c 0 * star (uu c 2)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 0 2
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 0 2
        + vv d 0 * star (vv d 2) := by
    simp only [Trace5.fr, uu_0, uu_2, aa1_0, aa2_0, aa3_0, aa4_0, aa1_2, aa2_2, aa3_2, aa4_2, vv_0, vv_2, bb1_0, bb2_0, bb3_0, bb4_0, bb1_2, bb2_2, bb3_2, bb4_2]
    linear_combination (1/4 : ℂ) * hd11 + (1/4 : ℂ) * hd12 + (1/4 : ℂ) * hd13 + (1/4 : ℂ) * hd14
  have fk03 : uu c 0 * star (uu c 3)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 0 3
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 0 3
        + vv d 0 * star (vv d 3) := by
    simp only [Trace5.fr, uu_0, uu_3, aa1_0, aa2_0, aa3_0, aa4_0, aa1_3, aa2_3, aa3_3, aa4_3, vv_0, vv_3, bb1_0, bb2_0, bb3_0, bb4_0, bb1_3, bb2_3, bb3_3, bb4_3]
    linear_combination (1/4 : ℂ) * hd31 + (1/4 : ℂ) * hd32 + (1/4 : ℂ) * hd33 + (1/4 : ℂ) * hd34
  have fk10 : uu c 1 * star (uu c 0)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 1 0
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 1 0
        + vv d 1 * star (vv d 0) := by
    simp only [Trace5.fr, uu_1, uu_0, aa1_1, aa2_1, aa3_1, aa4_1, aa1_0, aa2_0, aa3_0, aa4_0, vv_1, vv_0, bb1_1, bb2_1, bb3_1, bb4_1, bb1_0, bb2_0, bb3_0, bb4_0]
    linear_combination (1/4 : ℂ) * hd21 + (1/4 : ℂ) * hd22 + (-1/4 : ℂ) * hd23 + (-1/4 : ℂ) * hd24
  have fk11 : uu c 1 * star (uu c 1)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 1 1
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 1 1
        + vv d 1 * star (vv d 1) := by
    simp only [Trace5.fr, uu_1, uu_1, aa1_1, aa2_1, aa3_1, aa4_1, aa1_1, aa2_1, aa3_1, aa4_1, vv_1, vv_1, bb1_1, bb2_1, bb3_1, bb4_1, bb1_1, bb2_1, bb3_1, bb4_1]
    have hc : ((Complex.normSq (c y1) + Complex.normSq (c y5) + Complex.normSq (c y9)
        + Complex.normSq (c y13) + Complex.normSq (c y17)
        : Real) : ℂ) = ((Complex.normSq (d z1) + Complex.normSq (d z5) + Complex.normSq (d z9)
        + Complex.normSq (d z13) + Complex.normSq (d z17) : Real) : ℂ) := by
      exact_mod_cast mg1
    push_cast [← SixQubit.star_mul_self] at hc
    linear_combination hc
  have fk12 : uu c 1 * star (uu c 2)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 1 2
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 1 2
        + vv d 1 * star (vv d 2) := by
    simp only [Trace5.fr, uu_1, uu_2, aa1_1, aa2_1, aa3_1, aa4_1, aa1_2, aa2_2, aa3_2, aa4_2, vv_1, vv_2, bb1_1, bb2_1, bb3_1, bb4_1, bb1_2, bb2_2, bb3_2, bb4_2]
    linear_combination (1/4 : ℂ) * hd31 + (1/4 : ℂ) * hd32 + (-1/4 : ℂ) * hd33 + (-1/4 : ℂ) * hd34
  have fk13 : uu c 1 * star (uu c 3)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 1 3
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 1 3
        + vv d 1 * star (vv d 3) := by
    simp only [Trace5.fr, uu_1, uu_3, aa1_1, aa2_1, aa3_1, aa4_1, aa1_3, aa2_3, aa3_3, aa4_3, vv_1, vv_3, bb1_1, bb2_1, bb3_1, bb4_1, bb1_3, bb2_3, bb3_3, bb4_3]
    linear_combination (1/4 : ℂ) * hd11 + (1/4 : ℂ) * hd12 + (-1/4 : ℂ) * hd13 + (-1/4 : ℂ) * hd14
  have fk20 : uu c 2 * star (uu c 0)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 2 0
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 2 0
        + vv d 2 * star (vv d 0) := by
    simp only [Trace5.fr, uu_2, uu_0, aa1_2, aa2_2, aa3_2, aa4_2, aa1_0, aa2_0, aa3_0, aa4_0, vv_2, vv_0, bb1_2, bb2_2, bb3_2, bb4_2, bb1_0, bb2_0, bb3_0, bb4_0]
    linear_combination (1/4 : ℂ) * hd11 + (-1/4 : ℂ) * hd12 + (1/4 : ℂ) * hd13 + (-1/4 : ℂ) * hd14
  have fk21 : uu c 2 * star (uu c 1)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 2 1
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 2 1
        + vv d 2 * star (vv d 1) := by
    simp only [Trace5.fr, uu_2, uu_1, aa1_2, aa2_2, aa3_2, aa4_2, aa1_1, aa2_1, aa3_1, aa4_1, vv_2, vv_1, bb1_2, bb2_2, bb3_2, bb4_2, bb1_1, bb2_1, bb3_1, bb4_1]
    linear_combination (1/4 : ℂ) * hd31 + (-1/4 : ℂ) * hd32 + (1/4 : ℂ) * hd33 + (-1/4 : ℂ) * hd34
  have fk22 : uu c 2 * star (uu c 2)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 2 2
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 2 2
        + vv d 2 * star (vv d 2) := by
    simp only [Trace5.fr, uu_2, uu_2, aa1_2, aa2_2, aa3_2, aa4_2, aa1_2, aa2_2, aa3_2, aa4_2, vv_2, vv_2, bb1_2, bb2_2, bb3_2, bb4_2, bb1_2, bb2_2, bb3_2, bb4_2]
    have hc : ((Complex.normSq (c y2) + Complex.normSq (c y6) + Complex.normSq (c y10)
        + Complex.normSq (c y14) + Complex.normSq (c y18)
        : Real) : ℂ) = ((Complex.normSq (d z2) + Complex.normSq (d z6) + Complex.normSq (d z10)
        + Complex.normSq (d z14) + Complex.normSq (d z18) : Real) : ℂ) := by
      exact_mod_cast mg2
    push_cast [← SixQubit.star_mul_self] at hc
    linear_combination hc
  have fk23 : uu c 2 * star (uu c 3)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 2 3
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 2 3
        + vv d 2 * star (vv d 3) := by
    simp only [Trace5.fr, uu_2, uu_3, aa1_2, aa2_2, aa3_2, aa4_2, aa1_3, aa2_3, aa3_3, aa4_3, vv_2, vv_3, bb1_2, bb2_2, bb3_2, bb4_2, bb1_3, bb2_3, bb3_3, bb4_3]
    linear_combination (1/4 : ℂ) * hd21 + (-1/4 : ℂ) * hd22 + (1/4 : ℂ) * hd23 + (-1/4 : ℂ) * hd24
  have fk30 : uu c 3 * star (uu c 0)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 3 0
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 3 0
        + vv d 3 * star (vv d 0) := by
    simp only [Trace5.fr, uu_3, uu_0, aa1_3, aa2_3, aa3_3, aa4_3, aa1_0, aa2_0, aa3_0, aa4_0, vv_3, vv_0, bb1_3, bb2_3, bb3_3, bb4_3, bb1_0, bb2_0, bb3_0, bb4_0]
    linear_combination (1/4 : ℂ) * hd31 + (-1/4 : ℂ) * hd32 + (-1/4 : ℂ) * hd33 + (1/4 : ℂ) * hd34
  have fk31 : uu c 3 * star (uu c 1)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 3 1
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 3 1
        + vv d 3 * star (vv d 1) := by
    simp only [Trace5.fr, uu_3, uu_1, aa1_3, aa2_3, aa3_3, aa4_3, aa1_1, aa2_1, aa3_1, aa4_1, vv_3, vv_1, bb1_3, bb2_3, bb3_3, bb4_3, bb1_1, bb2_1, bb3_1, bb4_1]
    linear_combination (1/4 : ℂ) * hd11 + (-1/4 : ℂ) * hd12 + (-1/4 : ℂ) * hd13 + (1/4 : ℂ) * hd14
  have fk32 : uu c 3 * star (uu c 2)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 3 2
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 3 2
        + vv d 3 * star (vv d 2) := by
    simp only [Trace5.fr, uu_3, uu_2, aa1_3, aa2_3, aa3_3, aa4_3, aa1_2, aa2_2, aa3_2, aa4_2, vv_3, vv_2, bb1_3, bb2_3, bb3_3, bb4_3, bb1_2, bb2_2, bb3_2, bb4_2]
    linear_combination (1/4 : ℂ) * hd21 + (-1/4 : ℂ) * hd22 + (-1/4 : ℂ) * hd23 + (1/4 : ℂ) * hd24
  have fk33 : uu c 3 * star (uu c 3)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 3 3
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 3 3
        + vv d 3 * star (vv d 3) := by
    simp only [Trace5.fr, uu_3, uu_3, aa1_3, aa2_3, aa3_3, aa4_3, aa1_3, aa2_3, aa3_3, aa4_3, vv_3, vv_3, bb1_3, bb2_3, bb3_3, bb4_3, bb1_3, bb2_3, bb3_3, bb4_3]
    have hc : ((Complex.normSq (c y3) + Complex.normSq (c y7) + Complex.normSq (c y11)
        + Complex.normSq (c y15) + Complex.normSq (c y19)
        : Real) : ℂ) = ((Complex.normSq (d z3) + Complex.normSq (d z7) + Complex.normSq (d z11)
        + Complex.normSq (d z15) + Complex.normSq (d z19) : Real) : ℂ) := by
      exact_mod_cast mg3
    push_cast [← SixQubit.star_mul_self] at hc
    linear_combination hc
  have hf : ∀ k l : Fin 4, uu c k * star (uu c l)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) k l
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) k l + vv d k * star (vv d l) := by
    intro k l
    fin_cases k <;> fin_cases l
    exacts [fk00 , fk01 , fk02 , fk03 , fk10 , fk11 , fk12 , fk13 , fk20 , fk21 , fk22 , fk23 , fk30
      , fk31 , fk32 , fk33]
  have m100 : star (uu c 0) * bb1 d 0 + star (uu c 1) * bb1 d 1 + star (aa1 c 0) * vv d 0
      + star (aa1 c 1) * vv d 1 = 0 := by
    simp only [uu_0, uu_1, aa1_0, aa1_1, bb1_0, bb1_1, vv_0, vv_1]
    linear_combination (1/2 : ℂ) * ho1a + (1/2 : ℂ) * hz11
  have m101 : star (uu c 2) * bb1 d 0 + star (uu c 3) * bb1 d 1 + star (aa1 c 2) * vv d 0
      + star (aa1 c 3) * vv d 1 = 0 := by
    simp only [uu_2, uu_3, aa1_2, aa1_3, bb1_0, bb1_1, vv_0, vv_1]
    linear_combination (1/2 : ℂ) * hk10 + (1/2 : ℂ) * hk11
  have m110 : star (uu c 0) * bb1 d 2 + star (uu c 1) * bb1 d 3 + star (aa1 c 0) * vv d 2
      + star (aa1 c 1) * vv d 3 = 0 := by
    simp only [uu_0, uu_1, aa1_0, aa1_1, bb1_2, bb1_3, vv_2, vv_3]
    linear_combination (1/2 : ℂ) * hk10 - (1/2 : ℂ) * hk11
  have m111 : star (uu c 2) * bb1 d 2 + star (uu c 3) * bb1 d 3 + star (aa1 c 2) * vv d 2
      + star (aa1 c 3) * vv d 3 = 0 := by
    simp only [uu_2, uu_3, aa1_2, aa1_3, bb1_2, bb1_3, vv_2, vv_3]
    linear_combination (1/2 : ℂ) * ho1a - (1/2 : ℂ) * hz11
  have n100 : star (uu c 0) * bb1 d 0 + star (uu c 2) * bb1 d 2 + star (aa1 c 0) * vv d 0
      + star (aa1 c 2) * vv d 2 = 0 := by
    simp only [uu_0, uu_2, aa1_0, aa1_2, bb1_0, bb1_2, vv_0, vv_2]
    linear_combination (1/2 : ℂ) * ho1a + (1/2 : ℂ) * hz12
  have n101 : star (uu c 1) * bb1 d 0 + star (uu c 3) * bb1 d 2 + star (aa1 c 1) * vv d 0
      + star (aa1 c 3) * vv d 2 = 0 := by
    simp only [uu_1, uu_3, aa1_1, aa1_3, bb1_0, bb1_2, vv_0, vv_2]
    linear_combination (1/2 : ℂ) * hl10 + (1/2 : ℂ) * hl12
  have n110 : star (uu c 0) * bb1 d 1 + star (uu c 2) * bb1 d 3 + star (aa1 c 0) * vv d 1
      + star (aa1 c 2) * vv d 3 = 0 := by
    simp only [uu_0, uu_2, aa1_0, aa1_2, bb1_1, bb1_3, vv_1, vv_3]
    linear_combination (1/2 : ℂ) * hl10 - (1/2 : ℂ) * hl12
  have n111 : star (uu c 1) * bb1 d 1 + star (uu c 3) * bb1 d 3 + star (aa1 c 1) * vv d 1
      + star (aa1 c 3) * vv d 3 = 0 := by
    simp only [uu_1, uu_3, aa1_1, aa1_3, bb1_1, bb1_3, vv_1, vv_3]
    linear_combination (1/2 : ℂ) * ho1a - (1/2 : ℂ) * hz12
  have m200 : star (uu c 0) * bb2 d 0 + star (uu c 1) * bb2 d 1 + star (aa2 c 0) * vv d 0
      + star (aa2 c 1) * vv d 1 = 0 := by
    simp only [uu_0, uu_1, aa2_0, aa2_1, bb2_0, bb2_1, vv_0, vv_1]
    linear_combination (1/2 : ℂ) * ho2a + (1/2 : ℂ) * hz21
  have m201 : star (uu c 2) * bb2 d 0 + star (uu c 3) * bb2 d 1 + star (aa2 c 2) * vv d 0
      + star (aa2 c 3) * vv d 1 = 0 := by
    simp only [uu_2, uu_3, aa2_2, aa2_3, bb2_0, bb2_1, vv_0, vv_1]
    linear_combination (1/2 : ℂ) * hk20 + (1/2 : ℂ) * hk21
  have m210 : star (uu c 0) * bb2 d 2 + star (uu c 1) * bb2 d 3 + star (aa2 c 0) * vv d 2
      + star (aa2 c 1) * vv d 3 = 0 := by
    simp only [uu_0, uu_1, aa2_0, aa2_1, bb2_2, bb2_3, vv_2, vv_3]
    linear_combination (1/2 : ℂ) * hk20 - (1/2 : ℂ) * hk21
  have m211 : star (uu c 2) * bb2 d 2 + star (uu c 3) * bb2 d 3 + star (aa2 c 2) * vv d 2
      + star (aa2 c 3) * vv d 3 = 0 := by
    simp only [uu_2, uu_3, aa2_2, aa2_3, bb2_2, bb2_3, vv_2, vv_3]
    linear_combination (1/2 : ℂ) * ho2a - (1/2 : ℂ) * hz21
  have n200 : star (uu c 0) * bb2 d 0 + star (uu c 2) * bb2 d 2 + star (aa2 c 0) * vv d 0
      + star (aa2 c 2) * vv d 2 = 0 := by
    simp only [uu_0, uu_2, aa2_0, aa2_2, bb2_0, bb2_2, vv_0, vv_2]
    linear_combination (1/2 : ℂ) * ho2a + (1/2 : ℂ) * hz22
  have n201 : star (uu c 1) * bb2 d 0 + star (uu c 3) * bb2 d 2 + star (aa2 c 1) * vv d 0
      + star (aa2 c 3) * vv d 2 = 0 := by
    simp only [uu_1, uu_3, aa2_1, aa2_3, bb2_0, bb2_2, vv_0, vv_2]
    linear_combination (1/2 : ℂ) * hl20 + (1/2 : ℂ) * hl22
  have n210 : star (uu c 0) * bb2 d 1 + star (uu c 2) * bb2 d 3 + star (aa2 c 0) * vv d 1
      + star (aa2 c 2) * vv d 3 = 0 := by
    simp only [uu_0, uu_2, aa2_0, aa2_2, bb2_1, bb2_3, vv_1, vv_3]
    linear_combination (1/2 : ℂ) * hl20 - (1/2 : ℂ) * hl22
  have n211 : star (uu c 1) * bb2 d 1 + star (uu c 3) * bb2 d 3 + star (aa2 c 1) * vv d 1
      + star (aa2 c 3) * vv d 3 = 0 := by
    simp only [uu_1, uu_3, aa2_1, aa2_3, bb2_1, bb2_3, vv_1, vv_3]
    linear_combination (1/2 : ℂ) * ho2a - (1/2 : ℂ) * hz22
  have m300 : star (uu c 0) * bb3 d 0 + star (uu c 1) * bb3 d 1 + star (aa3 c 0) * vv d 0
      + star (aa3 c 1) * vv d 1 = 0 := by
    simp only [uu_0, uu_1, aa3_0, aa3_1, bb3_0, bb3_1, vv_0, vv_1]
    linear_combination (1/2 : ℂ) * ho3a + (1/2 : ℂ) * hz31
  have m301 : star (uu c 2) * bb3 d 0 + star (uu c 3) * bb3 d 1 + star (aa3 c 2) * vv d 0
      + star (aa3 c 3) * vv d 1 = 0 := by
    simp only [uu_2, uu_3, aa3_2, aa3_3, bb3_0, bb3_1, vv_0, vv_1]
    linear_combination (1/2 : ℂ) * hk30 + (1/2 : ℂ) * hk31
  have m310 : star (uu c 0) * bb3 d 2 + star (uu c 1) * bb3 d 3 + star (aa3 c 0) * vv d 2
      + star (aa3 c 1) * vv d 3 = 0 := by
    simp only [uu_0, uu_1, aa3_0, aa3_1, bb3_2, bb3_3, vv_2, vv_3]
    linear_combination (1/2 : ℂ) * hk30 - (1/2 : ℂ) * hk31
  have m311 : star (uu c 2) * bb3 d 2 + star (uu c 3) * bb3 d 3 + star (aa3 c 2) * vv d 2
      + star (aa3 c 3) * vv d 3 = 0 := by
    simp only [uu_2, uu_3, aa3_2, aa3_3, bb3_2, bb3_3, vv_2, vv_3]
    linear_combination (1/2 : ℂ) * ho3a - (1/2 : ℂ) * hz31
  have n300 : star (uu c 0) * bb3 d 0 + star (uu c 2) * bb3 d 2 + star (aa3 c 0) * vv d 0
      + star (aa3 c 2) * vv d 2 = 0 := by
    simp only [uu_0, uu_2, aa3_0, aa3_2, bb3_0, bb3_2, vv_0, vv_2]
    linear_combination (1/2 : ℂ) * ho3a + (1/2 : ℂ) * hz32
  have n301 : star (uu c 1) * bb3 d 0 + star (uu c 3) * bb3 d 2 + star (aa3 c 1) * vv d 0
      + star (aa3 c 3) * vv d 2 = 0 := by
    simp only [uu_1, uu_3, aa3_1, aa3_3, bb3_0, bb3_2, vv_0, vv_2]
    linear_combination (1/2 : ℂ) * hl30 + (1/2 : ℂ) * hl32
  have n310 : star (uu c 0) * bb3 d 1 + star (uu c 2) * bb3 d 3 + star (aa3 c 0) * vv d 1
      + star (aa3 c 2) * vv d 3 = 0 := by
    simp only [uu_0, uu_2, aa3_0, aa3_2, bb3_1, bb3_3, vv_1, vv_3]
    linear_combination (1/2 : ℂ) * hl30 - (1/2 : ℂ) * hl32
  have n311 : star (uu c 1) * bb3 d 1 + star (uu c 3) * bb3 d 3 + star (aa3 c 1) * vv d 1
      + star (aa3 c 3) * vv d 3 = 0 := by
    simp only [uu_1, uu_3, aa3_1, aa3_3, bb3_1, bb3_3, vv_1, vv_3]
    linear_combination (1/2 : ℂ) * ho3a - (1/2 : ℂ) * hz32
  have m400 : star (uu c 0) * bb4 d 0 + star (uu c 1) * bb4 d 1 + star (aa4 c 0) * vv d 0
      + star (aa4 c 1) * vv d 1 = 0 := by
    simp only [uu_0, uu_1, aa4_0, aa4_1, bb4_0, bb4_1, vv_0, vv_1]
    linear_combination (1/2 : ℂ) * ho4a + (1/2 : ℂ) * hz41
  have m401 : star (uu c 2) * bb4 d 0 + star (uu c 3) * bb4 d 1 + star (aa4 c 2) * vv d 0
      + star (aa4 c 3) * vv d 1 = 0 := by
    simp only [uu_2, uu_3, aa4_2, aa4_3, bb4_0, bb4_1, vv_0, vv_1]
    linear_combination (1/2 : ℂ) * hk40 + (1/2 : ℂ) * hk41
  have m410 : star (uu c 0) * bb4 d 2 + star (uu c 1) * bb4 d 3 + star (aa4 c 0) * vv d 2
      + star (aa4 c 1) * vv d 3 = 0 := by
    simp only [uu_0, uu_1, aa4_0, aa4_1, bb4_2, bb4_3, vv_2, vv_3]
    linear_combination (1/2 : ℂ) * hk40 - (1/2 : ℂ) * hk41
  have m411 : star (uu c 2) * bb4 d 2 + star (uu c 3) * bb4 d 3 + star (aa4 c 2) * vv d 2
      + star (aa4 c 3) * vv d 3 = 0 := by
    simp only [uu_2, uu_3, aa4_2, aa4_3, bb4_2, bb4_3, vv_2, vv_3]
    linear_combination (1/2 : ℂ) * ho4a - (1/2 : ℂ) * hz41
  have n400 : star (uu c 0) * bb4 d 0 + star (uu c 2) * bb4 d 2 + star (aa4 c 0) * vv d 0
      + star (aa4 c 2) * vv d 2 = 0 := by
    simp only [uu_0, uu_2, aa4_0, aa4_2, bb4_0, bb4_2, vv_0, vv_2]
    linear_combination (1/2 : ℂ) * ho4a + (1/2 : ℂ) * hz42
  have n401 : star (uu c 1) * bb4 d 0 + star (uu c 3) * bb4 d 2 + star (aa4 c 1) * vv d 0
      + star (aa4 c 3) * vv d 2 = 0 := by
    simp only [uu_1, uu_3, aa4_1, aa4_3, bb4_0, bb4_2, vv_0, vv_2]
    linear_combination (1/2 : ℂ) * hl40 + (1/2 : ℂ) * hl42
  have n410 : star (uu c 0) * bb4 d 1 + star (uu c 2) * bb4 d 3 + star (aa4 c 0) * vv d 1
      + star (aa4 c 2) * vv d 3 = 0 := by
    simp only [uu_0, uu_2, aa4_0, aa4_2, bb4_1, bb4_3, vv_1, vv_3]
    linear_combination (1/2 : ℂ) * hl40 - (1/2 : ℂ) * hl42
  have n411 : star (uu c 1) * bb4 d 1 + star (uu c 3) * bb4 d 3 + star (aa4 c 1) * vv d 1
      + star (aa4 c 3) * vv d 3 = 0 := by
    simp only [uu_1, uu_3, aa4_1, aa4_3, bb4_1, bb4_3, vv_1, vv_3]
    linear_combination (1/2 : ℂ) * ho4a - (1/2 : ℂ) * hz42
  exact Flip5.core (uu c) (vv d) (aa1 c) (aa2 c) (aa3 c) (aa4 c) (bb1 d) (bb2 d) (bb3 d)
    (bb4 d) hnuu hnvv hnaa1 hnaa2 hnaa3 hnaa4 hnbb1 hnbb2 hnbb3 hnbb4 hq1 hq2 hq3 hq4 hf
    x12 x13 x14 x23 x24 x34
    m100 m101 m110 m111 n100 n101 n110 n111
    m200 m201 m210 m211 n200 n201 n210 n211
    m300 m301 m310 m311 n300 n301 n310 n311
    m400 m401 m410 m411 n400 n401 n410 n411

end

end SixQubit.Orbit5
