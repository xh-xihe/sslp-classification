import Mathlib

import SS.FullKL
import SixQubit.Common
import SixQubit.Hafnian

/-!
# Six-qubit no-go for moment orbit 17

Orbit 17 of `six_qubit_sslp.tex`: q = 4, angle vector
a = (1, 1, 1, 1, 1, 1), residues 0 and 2.

The two fibers are the Hamming shells `{wt 0, 4}` and `{wt 2, 6}`.  Index the
weight-two strings by the edges of `K_6`; the weight-four strings are their
complements.  Writing `a` for the bottom anchor amplitude, `b` for the top
anchor amplitude, `c_e` for the bottom edge amplitudes and `d_e` for the top
ones, the moment polytope forces

```
|a|^2 = |b|^2 = 1/4 ,     sum_{e ni v} |c_e|^2 = 1/4   (v = 0, ..., 5) ,
```

a scaled fractional perfect matching of `K_6`.

Every edge mask `f` has exactly eight incidences and exactly two independent
dressings, `z = 0` and `z = e_i` with `i` in `f`.  Their half sum and half
difference are the *pair flip* and the *anchor flip*

```
sum_{g subset V - f} conj(c_{V-f-g}) d_g = 0 ,   conj(a) d_f + conj(c_f) b = 0 .
```

Multiplying the pair flip by `conj(a)` and substituting the anchor flips
eliminates every top amplitude at once and leaves `2 b` times the four-set
hafnian.  Since `|b|^2 = 1/4` the fifteen hafnian equations hold, and
`SixQubit.Hafnian.no_go` shows they are incompatible with the fractional
perfect matching.  No division is used anywhere: the phase ratio
`lambda = -b / conj(a)` of the paper never appears.

Everything computational is decided by the Lean kernel; `native_decide`
is not used.
-/

namespace SixQubit.Orbit17

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

/-! ## The two fibers -/

def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]

def y0 : SS.BitString 6 := bs false false false false false false      -- 000000
def y1 : SS.BitString 6 := bs false false true  true  true  true       -- 001111
def y2 : SS.BitString 6 := bs false true  false true  true  true       -- 010111
def y3 : SS.BitString 6 := bs false true  true  false true  true       -- 011011
def y4 : SS.BitString 6 := bs false true  true  true  false true       -- 011101
def y5 : SS.BitString 6 := bs false true  true  true  true  false      -- 011110
def y6 : SS.BitString 6 := bs true  false false true  true  true       -- 100111
def y7 : SS.BitString 6 := bs true  false true  false true  true       -- 101011
def y8 : SS.BitString 6 := bs true  false true  true  false true       -- 101101
def y9 : SS.BitString 6 := bs true  false true  true  true  false      -- 101110
def y10 : SS.BitString 6 := bs true  true  false false true  true       -- 110011
def y11 : SS.BitString 6 := bs true  true  false true  false true       -- 110101
def y12 : SS.BitString 6 := bs true  true  false true  true  false      -- 110110
def y13 : SS.BitString 6 := bs true  true  true  false false true       -- 111001
def y14 : SS.BitString 6 := bs true  true  true  false true  false      -- 111010
def y15 : SS.BitString 6 := bs true  true  true  true  false false      -- 111100

def z0 : SS.BitString 6 := bs false false false false true  true       -- 000011
def z1 : SS.BitString 6 := bs false false false true  false true       -- 000101
def z2 : SS.BitString 6 := bs false false false true  true  false      -- 000110
def z3 : SS.BitString 6 := bs false false true  false false true       -- 001001
def z4 : SS.BitString 6 := bs false false true  false true  false      -- 001010
def z5 : SS.BitString 6 := bs false false true  true  false false      -- 001100
def z6 : SS.BitString 6 := bs false true  false false false true       -- 010001
def z7 : SS.BitString 6 := bs false true  false false true  false      -- 010010
def z8 : SS.BitString 6 := bs false true  false true  false false      -- 010100
def z9 : SS.BitString 6 := bs false true  true  false false false      -- 011000
def z10 : SS.BitString 6 := bs true  false false false false true       -- 100001
def z11 : SS.BitString 6 := bs true  false false false true  false      -- 100010
def z12 : SS.BitString 6 := bs true  false false true  false false      -- 100100
def z13 : SS.BitString 6 := bs true  false true  false false false      -- 101000
def z14 : SS.BitString 6 := bs true  true  false false false false      -- 110000
def z15 : SS.BitString 6 := bs true  true  true  true  true  true       -- 111111

def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15}
def S1 : Finset (SS.BitString 6) := {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15}

def av : Fin 6 -> ZMod 4 := ![1, 1, 1, 1, 1, 1]

theorem S0_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 0) = S0 := by
  decide

theorem S1_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 2) = S1 := by
  decide

/-! ## The fifteen edge masks and their dressings -/

def e01 : SS.BitString 6 := bs true  true  false false false false      -- 110000
def e02 : SS.BitString 6 := bs true  false true  false false false      -- 101000
def e03 : SS.BitString 6 := bs true  false false true  false false      -- 100100
def e04 : SS.BitString 6 := bs true  false false false true  false      -- 100010
def e05 : SS.BitString 6 := bs true  false false false false true       -- 100001
def e12 : SS.BitString 6 := bs false true  true  false false false      -- 011000
def e13 : SS.BitString 6 := bs false true  false true  false false      -- 010100
def e14 : SS.BitString 6 := bs false true  false false true  false      -- 010010
def e15 : SS.BitString 6 := bs false true  false false false true       -- 010001
def e23 : SS.BitString 6 := bs false false true  true  false false      -- 001100
def e24 : SS.BitString 6 := bs false false true  false true  false      -- 001010
def e25 : SS.BitString 6 := bs false false true  false false true       -- 001001
def e34 : SS.BitString 6 := bs false false false true  true  false      -- 000110
def e35 : SS.BitString 6 := bs false false false true  false true       -- 000101
def e45 : SS.BitString 6 := bs false false false false true  true       -- 000011

def wz : SS.BitString 6 := bs false false false false false false      -- 000000
def wp0 : SS.BitString 6 := bs true  false false false false false      -- 100000
def wp1 : SS.BitString 6 := bs false true  false false false false      -- 010000
def wp2 : SS.BitString 6 := bs false false true  false false false      -- 001000
def wp3 : SS.BitString 6 := bs false false false true  false false      -- 000100
def wp4 : SS.BitString 6 := bs false false false false true  false      -- 000010
def wp5 : SS.BitString 6 := bs false false false false false true       -- 000001

/-! ## The off-diagonal layer -/

def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),
      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

theorem inc_e01 : S1.filter (fun y => SS.bxor y e01 ∈ S0) = {z0, z1, z2, z3, z4, z5, z14, z15} := by decide
theorem flip_e01_0 : SS.bxor z0 e01 = y10 := by decide
theorem flip_e01_1 : SS.bxor z1 e01 = y11 := by decide
theorem flip_e01_2 : SS.bxor z2 e01 = y12 := by decide
theorem flip_e01_3 : SS.bxor z3 e01 = y13 := by decide
theorem flip_e01_4 : SS.bxor z4 e01 = y14 := by decide
theorem flip_e01_5 : SS.bxor z5 e01 = y15 := by decide
theorem flip_e01_6 : SS.bxor z14 e01 = y0 := by decide
theorem flip_e01_7 : SS.bxor z15 e01 = y1 := by decide
theorem sgz_e01_0 : SS.bdot wz z0 = false := by decide
theorem sgz_e01_1 : SS.bdot wz z1 = false := by decide
theorem sgz_e01_2 : SS.bdot wz z2 = false := by decide
theorem sgz_e01_3 : SS.bdot wz z3 = false := by decide
theorem sgz_e01_4 : SS.bdot wz z4 = false := by decide
theorem sgz_e01_5 : SS.bdot wz z5 = false := by decide
theorem sgz_e01_6 : SS.bdot wz z14 = false := by decide
theorem sgz_e01_7 : SS.bdot wz z15 = false := by decide
theorem ex_e01_z (c d : SS.BitString 6 -> ℂ) :
    offSum c d e01 wz = star (c y10) * d z0 + star (c y11) * d z1 + star (c y12) * d z2 + star (c y13) * d z3 + star (c y14) * d z4 + star (c y15) * d z5 + star (c y0) * d z14 + star (c y1) * d z15 := by
  unfold offSum
  rw [inc_e01]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_e01_0, flip_e01_1, flip_e01_2, flip_e01_3, flip_e01_4, flip_e01_5, flip_e01_6, flip_e01_7]
  simp only [sgz_e01_0, sgz_e01_1, sgz_e01_2, sgz_e01_3, sgz_e01_4, sgz_e01_5, sgz_e01_6, sgz_e01_7, SixQubit.signMul_false]
  try ring
theorem sgp_e01_0 : SS.bdot wp0 z0 = false := by decide
theorem sgp_e01_1 : SS.bdot wp0 z1 = false := by decide
theorem sgp_e01_2 : SS.bdot wp0 z2 = false := by decide
theorem sgp_e01_3 : SS.bdot wp0 z3 = false := by decide
theorem sgp_e01_4 : SS.bdot wp0 z4 = false := by decide
theorem sgp_e01_5 : SS.bdot wp0 z5 = false := by decide
theorem sgp_e01_6 : SS.bdot wp0 z14 = true := by decide
theorem sgp_e01_7 : SS.bdot wp0 z15 = true := by decide
theorem ex_e01_p (c d : SS.BitString 6 -> ℂ) :
    offSum c d e01 wp0 = star (c y10) * d z0 + star (c y11) * d z1 + star (c y12) * d z2 + star (c y13) * d z3 + star (c y14) * d z4 + star (c y15) * d z5 - star (c y0) * d z14 - star (c y1) * d z15 := by
  unfold offSum
  rw [inc_e01]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_e01_0, flip_e01_1, flip_e01_2, flip_e01_3, flip_e01_4, flip_e01_5, flip_e01_6, flip_e01_7]
  simp only [sgp_e01_0, sgp_e01_1, sgp_e01_2, sgp_e01_3, sgp_e01_4, sgp_e01_5, sgp_e01_6, sgp_e01_7, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem inc_e02 : S1.filter (fun y => SS.bxor y e02 ∈ S0) = {z0, z1, z2, z6, z7, z8, z13, z15} := by decide
theorem flip_e02_0 : SS.bxor z0 e02 = y7 := by decide
theorem flip_e02_1 : SS.bxor z1 e02 = y8 := by decide
theorem flip_e02_2 : SS.bxor z2 e02 = y9 := by decide
theorem flip_e02_3 : SS.bxor z6 e02 = y13 := by decide
theorem flip_e02_4 : SS.bxor z7 e02 = y14 := by decide
theorem flip_e02_5 : SS.bxor z8 e02 = y15 := by decide
theorem flip_e02_6 : SS.bxor z13 e02 = y0 := by decide
theorem flip_e02_7 : SS.bxor z15 e02 = y2 := by decide
theorem sgz_e02_0 : SS.bdot wz z0 = false := by decide
theorem sgz_e02_1 : SS.bdot wz z1 = false := by decide
theorem sgz_e02_2 : SS.bdot wz z2 = false := by decide
theorem sgz_e02_3 : SS.bdot wz z6 = false := by decide
theorem sgz_e02_4 : SS.bdot wz z7 = false := by decide
theorem sgz_e02_5 : SS.bdot wz z8 = false := by decide
theorem sgz_e02_6 : SS.bdot wz z13 = false := by decide
theorem sgz_e02_7 : SS.bdot wz z15 = false := by decide
theorem ex_e02_z (c d : SS.BitString 6 -> ℂ) :
    offSum c d e02 wz = star (c y7) * d z0 + star (c y8) * d z1 + star (c y9) * d z2 + star (c y13) * d z6 + star (c y14) * d z7 + star (c y15) * d z8 + star (c y0) * d z13 + star (c y2) * d z15 := by
  unfold offSum
  rw [inc_e02]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_e02_0, flip_e02_1, flip_e02_2, flip_e02_3, flip_e02_4, flip_e02_5, flip_e02_6, flip_e02_7]
  simp only [sgz_e02_0, sgz_e02_1, sgz_e02_2, sgz_e02_3, sgz_e02_4, sgz_e02_5, sgz_e02_6, sgz_e02_7, SixQubit.signMul_false]
  try ring
theorem sgp_e02_0 : SS.bdot wp0 z0 = false := by decide
theorem sgp_e02_1 : SS.bdot wp0 z1 = false := by decide
theorem sgp_e02_2 : SS.bdot wp0 z2 = false := by decide
theorem sgp_e02_3 : SS.bdot wp0 z6 = false := by decide
theorem sgp_e02_4 : SS.bdot wp0 z7 = false := by decide
theorem sgp_e02_5 : SS.bdot wp0 z8 = false := by decide
theorem sgp_e02_6 : SS.bdot wp0 z13 = true := by decide
theorem sgp_e02_7 : SS.bdot wp0 z15 = true := by decide
theorem ex_e02_p (c d : SS.BitString 6 -> ℂ) :
    offSum c d e02 wp0 = star (c y7) * d z0 + star (c y8) * d z1 + star (c y9) * d z2 + star (c y13) * d z6 + star (c y14) * d z7 + star (c y15) * d z8 - star (c y0) * d z13 - star (c y2) * d z15 := by
  unfold offSum
  rw [inc_e02]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_e02_0, flip_e02_1, flip_e02_2, flip_e02_3, flip_e02_4, flip_e02_5, flip_e02_6, flip_e02_7]
  simp only [sgp_e02_0, sgp_e02_1, sgp_e02_2, sgp_e02_3, sgp_e02_4, sgp_e02_5, sgp_e02_6, sgp_e02_7, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem inc_e03 : S1.filter (fun y => SS.bxor y e03 ∈ S0) = {z0, z3, z4, z6, z7, z9, z12, z15} := by decide
theorem flip_e03_0 : SS.bxor z0 e03 = y6 := by decide
theorem flip_e03_1 : SS.bxor z3 e03 = y8 := by decide
theorem flip_e03_2 : SS.bxor z4 e03 = y9 := by decide
theorem flip_e03_3 : SS.bxor z6 e03 = y11 := by decide
theorem flip_e03_4 : SS.bxor z7 e03 = y12 := by decide
theorem flip_e03_5 : SS.bxor z9 e03 = y15 := by decide
theorem flip_e03_6 : SS.bxor z12 e03 = y0 := by decide
theorem flip_e03_7 : SS.bxor z15 e03 = y3 := by decide
theorem sgz_e03_0 : SS.bdot wz z0 = false := by decide
theorem sgz_e03_1 : SS.bdot wz z3 = false := by decide
theorem sgz_e03_2 : SS.bdot wz z4 = false := by decide
theorem sgz_e03_3 : SS.bdot wz z6 = false := by decide
theorem sgz_e03_4 : SS.bdot wz z7 = false := by decide
theorem sgz_e03_5 : SS.bdot wz z9 = false := by decide
theorem sgz_e03_6 : SS.bdot wz z12 = false := by decide
theorem sgz_e03_7 : SS.bdot wz z15 = false := by decide
theorem ex_e03_z (c d : SS.BitString 6 -> ℂ) :
    offSum c d e03 wz = star (c y6) * d z0 + star (c y8) * d z3 + star (c y9) * d z4 + star (c y11) * d z6 + star (c y12) * d z7 + star (c y15) * d z9 + star (c y0) * d z12 + star (c y3) * d z15 := by
  unfold offSum
  rw [inc_e03]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_e03_0, flip_e03_1, flip_e03_2, flip_e03_3, flip_e03_4, flip_e03_5, flip_e03_6, flip_e03_7]
  simp only [sgz_e03_0, sgz_e03_1, sgz_e03_2, sgz_e03_3, sgz_e03_4, sgz_e03_5, sgz_e03_6, sgz_e03_7, SixQubit.signMul_false]
  try ring
theorem sgp_e03_0 : SS.bdot wp0 z0 = false := by decide
theorem sgp_e03_1 : SS.bdot wp0 z3 = false := by decide
theorem sgp_e03_2 : SS.bdot wp0 z4 = false := by decide
theorem sgp_e03_3 : SS.bdot wp0 z6 = false := by decide
theorem sgp_e03_4 : SS.bdot wp0 z7 = false := by decide
theorem sgp_e03_5 : SS.bdot wp0 z9 = false := by decide
theorem sgp_e03_6 : SS.bdot wp0 z12 = true := by decide
theorem sgp_e03_7 : SS.bdot wp0 z15 = true := by decide
theorem ex_e03_p (c d : SS.BitString 6 -> ℂ) :
    offSum c d e03 wp0 = star (c y6) * d z0 + star (c y8) * d z3 + star (c y9) * d z4 + star (c y11) * d z6 + star (c y12) * d z7 + star (c y15) * d z9 - star (c y0) * d z12 - star (c y3) * d z15 := by
  unfold offSum
  rw [inc_e03]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_e03_0, flip_e03_1, flip_e03_2, flip_e03_3, flip_e03_4, flip_e03_5, flip_e03_6, flip_e03_7]
  simp only [sgp_e03_0, sgp_e03_1, sgp_e03_2, sgp_e03_3, sgp_e03_4, sgp_e03_5, sgp_e03_6, sgp_e03_7, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem inc_e04 : S1.filter (fun y => SS.bxor y e04 ∈ S0) = {z1, z3, z5, z6, z8, z9, z11, z15} := by decide
theorem flip_e04_0 : SS.bxor z1 e04 = y6 := by decide
theorem flip_e04_1 : SS.bxor z3 e04 = y7 := by decide
theorem flip_e04_2 : SS.bxor z5 e04 = y9 := by decide
theorem flip_e04_3 : SS.bxor z6 e04 = y10 := by decide
theorem flip_e04_4 : SS.bxor z8 e04 = y12 := by decide
theorem flip_e04_5 : SS.bxor z9 e04 = y14 := by decide
theorem flip_e04_6 : SS.bxor z11 e04 = y0 := by decide
theorem flip_e04_7 : SS.bxor z15 e04 = y4 := by decide
theorem sgz_e04_0 : SS.bdot wz z1 = false := by decide
theorem sgz_e04_1 : SS.bdot wz z3 = false := by decide
theorem sgz_e04_2 : SS.bdot wz z5 = false := by decide
theorem sgz_e04_3 : SS.bdot wz z6 = false := by decide
theorem sgz_e04_4 : SS.bdot wz z8 = false := by decide
theorem sgz_e04_5 : SS.bdot wz z9 = false := by decide
theorem sgz_e04_6 : SS.bdot wz z11 = false := by decide
theorem sgz_e04_7 : SS.bdot wz z15 = false := by decide
theorem ex_e04_z (c d : SS.BitString 6 -> ℂ) :
    offSum c d e04 wz = star (c y6) * d z1 + star (c y7) * d z3 + star (c y9) * d z5 + star (c y10) * d z6 + star (c y12) * d z8 + star (c y14) * d z9 + star (c y0) * d z11 + star (c y4) * d z15 := by
  unfold offSum
  rw [inc_e04]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_e04_0, flip_e04_1, flip_e04_2, flip_e04_3, flip_e04_4, flip_e04_5, flip_e04_6, flip_e04_7]
  simp only [sgz_e04_0, sgz_e04_1, sgz_e04_2, sgz_e04_3, sgz_e04_4, sgz_e04_5, sgz_e04_6, sgz_e04_7, SixQubit.signMul_false]
  try ring
theorem sgp_e04_0 : SS.bdot wp0 z1 = false := by decide
theorem sgp_e04_1 : SS.bdot wp0 z3 = false := by decide
theorem sgp_e04_2 : SS.bdot wp0 z5 = false := by decide
theorem sgp_e04_3 : SS.bdot wp0 z6 = false := by decide
theorem sgp_e04_4 : SS.bdot wp0 z8 = false := by decide
theorem sgp_e04_5 : SS.bdot wp0 z9 = false := by decide
theorem sgp_e04_6 : SS.bdot wp0 z11 = true := by decide
theorem sgp_e04_7 : SS.bdot wp0 z15 = true := by decide
theorem ex_e04_p (c d : SS.BitString 6 -> ℂ) :
    offSum c d e04 wp0 = star (c y6) * d z1 + star (c y7) * d z3 + star (c y9) * d z5 + star (c y10) * d z6 + star (c y12) * d z8 + star (c y14) * d z9 - star (c y0) * d z11 - star (c y4) * d z15 := by
  unfold offSum
  rw [inc_e04]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_e04_0, flip_e04_1, flip_e04_2, flip_e04_3, flip_e04_4, flip_e04_5, flip_e04_6, flip_e04_7]
  simp only [sgp_e04_0, sgp_e04_1, sgp_e04_2, sgp_e04_3, sgp_e04_4, sgp_e04_5, sgp_e04_6, sgp_e04_7, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem inc_e05 : S1.filter (fun y => SS.bxor y e05 ∈ S0) = {z2, z4, z5, z7, z8, z9, z10, z15} := by decide
theorem flip_e05_0 : SS.bxor z2 e05 = y6 := by decide
theorem flip_e05_1 : SS.bxor z4 e05 = y7 := by decide
theorem flip_e05_2 : SS.bxor z5 e05 = y8 := by decide
theorem flip_e05_3 : SS.bxor z7 e05 = y10 := by decide
theorem flip_e05_4 : SS.bxor z8 e05 = y11 := by decide
theorem flip_e05_5 : SS.bxor z9 e05 = y13 := by decide
theorem flip_e05_6 : SS.bxor z10 e05 = y0 := by decide
theorem flip_e05_7 : SS.bxor z15 e05 = y5 := by decide
theorem sgz_e05_0 : SS.bdot wz z2 = false := by decide
theorem sgz_e05_1 : SS.bdot wz z4 = false := by decide
theorem sgz_e05_2 : SS.bdot wz z5 = false := by decide
theorem sgz_e05_3 : SS.bdot wz z7 = false := by decide
theorem sgz_e05_4 : SS.bdot wz z8 = false := by decide
theorem sgz_e05_5 : SS.bdot wz z9 = false := by decide
theorem sgz_e05_6 : SS.bdot wz z10 = false := by decide
theorem sgz_e05_7 : SS.bdot wz z15 = false := by decide
theorem ex_e05_z (c d : SS.BitString 6 -> ℂ) :
    offSum c d e05 wz = star (c y6) * d z2 + star (c y7) * d z4 + star (c y8) * d z5 + star (c y10) * d z7 + star (c y11) * d z8 + star (c y13) * d z9 + star (c y0) * d z10 + star (c y5) * d z15 := by
  unfold offSum
  rw [inc_e05]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_e05_0, flip_e05_1, flip_e05_2, flip_e05_3, flip_e05_4, flip_e05_5, flip_e05_6, flip_e05_7]
  simp only [sgz_e05_0, sgz_e05_1, sgz_e05_2, sgz_e05_3, sgz_e05_4, sgz_e05_5, sgz_e05_6, sgz_e05_7, SixQubit.signMul_false]
  try ring
theorem sgp_e05_0 : SS.bdot wp0 z2 = false := by decide
theorem sgp_e05_1 : SS.bdot wp0 z4 = false := by decide
theorem sgp_e05_2 : SS.bdot wp0 z5 = false := by decide
theorem sgp_e05_3 : SS.bdot wp0 z7 = false := by decide
theorem sgp_e05_4 : SS.bdot wp0 z8 = false := by decide
theorem sgp_e05_5 : SS.bdot wp0 z9 = false := by decide
theorem sgp_e05_6 : SS.bdot wp0 z10 = true := by decide
theorem sgp_e05_7 : SS.bdot wp0 z15 = true := by decide
theorem ex_e05_p (c d : SS.BitString 6 -> ℂ) :
    offSum c d e05 wp0 = star (c y6) * d z2 + star (c y7) * d z4 + star (c y8) * d z5 + star (c y10) * d z7 + star (c y11) * d z8 + star (c y13) * d z9 - star (c y0) * d z10 - star (c y5) * d z15 := by
  unfold offSum
  rw [inc_e05]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_e05_0, flip_e05_1, flip_e05_2, flip_e05_3, flip_e05_4, flip_e05_5, flip_e05_6, flip_e05_7]
  simp only [sgp_e05_0, sgp_e05_1, sgp_e05_2, sgp_e05_3, sgp_e05_4, sgp_e05_5, sgp_e05_6, sgp_e05_7, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem inc_e12 : S1.filter (fun y => SS.bxor y e12 ∈ S0) = {z0, z1, z2, z9, z10, z11, z12, z15} := by decide
theorem flip_e12_0 : SS.bxor z0 e12 = y3 := by decide
theorem flip_e12_1 : SS.bxor z1 e12 = y4 := by decide
theorem flip_e12_2 : SS.bxor z2 e12 = y5 := by decide
theorem flip_e12_3 : SS.bxor z9 e12 = y0 := by decide
theorem flip_e12_4 : SS.bxor z10 e12 = y13 := by decide
theorem flip_e12_5 : SS.bxor z11 e12 = y14 := by decide
theorem flip_e12_6 : SS.bxor z12 e12 = y15 := by decide
theorem flip_e12_7 : SS.bxor z15 e12 = y6 := by decide
theorem sgz_e12_0 : SS.bdot wz z0 = false := by decide
theorem sgz_e12_1 : SS.bdot wz z1 = false := by decide
theorem sgz_e12_2 : SS.bdot wz z2 = false := by decide
theorem sgz_e12_3 : SS.bdot wz z9 = false := by decide
theorem sgz_e12_4 : SS.bdot wz z10 = false := by decide
theorem sgz_e12_5 : SS.bdot wz z11 = false := by decide
theorem sgz_e12_6 : SS.bdot wz z12 = false := by decide
theorem sgz_e12_7 : SS.bdot wz z15 = false := by decide
theorem ex_e12_z (c d : SS.BitString 6 -> ℂ) :
    offSum c d e12 wz = star (c y3) * d z0 + star (c y4) * d z1 + star (c y5) * d z2 + star (c y0) * d z9 + star (c y13) * d z10 + star (c y14) * d z11 + star (c y15) * d z12 + star (c y6) * d z15 := by
  unfold offSum
  rw [inc_e12]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_e12_0, flip_e12_1, flip_e12_2, flip_e12_3, flip_e12_4, flip_e12_5, flip_e12_6, flip_e12_7]
  simp only [sgz_e12_0, sgz_e12_1, sgz_e12_2, sgz_e12_3, sgz_e12_4, sgz_e12_5, sgz_e12_6, sgz_e12_7, SixQubit.signMul_false]
  try ring
theorem sgp_e12_0 : SS.bdot wp1 z0 = false := by decide
theorem sgp_e12_1 : SS.bdot wp1 z1 = false := by decide
theorem sgp_e12_2 : SS.bdot wp1 z2 = false := by decide
theorem sgp_e12_3 : SS.bdot wp1 z9 = true := by decide
theorem sgp_e12_4 : SS.bdot wp1 z10 = false := by decide
theorem sgp_e12_5 : SS.bdot wp1 z11 = false := by decide
theorem sgp_e12_6 : SS.bdot wp1 z12 = false := by decide
theorem sgp_e12_7 : SS.bdot wp1 z15 = true := by decide
theorem ex_e12_p (c d : SS.BitString 6 -> ℂ) :
    offSum c d e12 wp1 = star (c y3) * d z0 + star (c y4) * d z1 + star (c y5) * d z2 - star (c y0) * d z9 + star (c y13) * d z10 + star (c y14) * d z11 + star (c y15) * d z12 - star (c y6) * d z15 := by
  unfold offSum
  rw [inc_e12]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_e12_0, flip_e12_1, flip_e12_2, flip_e12_3, flip_e12_4, flip_e12_5, flip_e12_6, flip_e12_7]
  simp only [sgp_e12_0, sgp_e12_1, sgp_e12_2, sgp_e12_3, sgp_e12_4, sgp_e12_5, sgp_e12_6, sgp_e12_7, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem inc_e13 : S1.filter (fun y => SS.bxor y e13 ∈ S0) = {z0, z3, z4, z8, z10, z11, z13, z15} := by decide
theorem flip_e13_0 : SS.bxor z0 e13 = y2 := by decide
theorem flip_e13_1 : SS.bxor z3 e13 = y4 := by decide
theorem flip_e13_2 : SS.bxor z4 e13 = y5 := by decide
theorem flip_e13_3 : SS.bxor z8 e13 = y0 := by decide
theorem flip_e13_4 : SS.bxor z10 e13 = y11 := by decide
theorem flip_e13_5 : SS.bxor z11 e13 = y12 := by decide
theorem flip_e13_6 : SS.bxor z13 e13 = y15 := by decide
theorem flip_e13_7 : SS.bxor z15 e13 = y7 := by decide
theorem sgz_e13_0 : SS.bdot wz z0 = false := by decide
theorem sgz_e13_1 : SS.bdot wz z3 = false := by decide
theorem sgz_e13_2 : SS.bdot wz z4 = false := by decide
theorem sgz_e13_3 : SS.bdot wz z8 = false := by decide
theorem sgz_e13_4 : SS.bdot wz z10 = false := by decide
theorem sgz_e13_5 : SS.bdot wz z11 = false := by decide
theorem sgz_e13_6 : SS.bdot wz z13 = false := by decide
theorem sgz_e13_7 : SS.bdot wz z15 = false := by decide
theorem ex_e13_z (c d : SS.BitString 6 -> ℂ) :
    offSum c d e13 wz = star (c y2) * d z0 + star (c y4) * d z3 + star (c y5) * d z4 + star (c y0) * d z8 + star (c y11) * d z10 + star (c y12) * d z11 + star (c y15) * d z13 + star (c y7) * d z15 := by
  unfold offSum
  rw [inc_e13]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_e13_0, flip_e13_1, flip_e13_2, flip_e13_3, flip_e13_4, flip_e13_5, flip_e13_6, flip_e13_7]
  simp only [sgz_e13_0, sgz_e13_1, sgz_e13_2, sgz_e13_3, sgz_e13_4, sgz_e13_5, sgz_e13_6, sgz_e13_7, SixQubit.signMul_false]
  try ring
theorem sgp_e13_0 : SS.bdot wp1 z0 = false := by decide
theorem sgp_e13_1 : SS.bdot wp1 z3 = false := by decide
theorem sgp_e13_2 : SS.bdot wp1 z4 = false := by decide
theorem sgp_e13_3 : SS.bdot wp1 z8 = true := by decide
theorem sgp_e13_4 : SS.bdot wp1 z10 = false := by decide
theorem sgp_e13_5 : SS.bdot wp1 z11 = false := by decide
theorem sgp_e13_6 : SS.bdot wp1 z13 = false := by decide
theorem sgp_e13_7 : SS.bdot wp1 z15 = true := by decide
theorem ex_e13_p (c d : SS.BitString 6 -> ℂ) :
    offSum c d e13 wp1 = star (c y2) * d z0 + star (c y4) * d z3 + star (c y5) * d z4 - star (c y0) * d z8 + star (c y11) * d z10 + star (c y12) * d z11 + star (c y15) * d z13 - star (c y7) * d z15 := by
  unfold offSum
  rw [inc_e13]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_e13_0, flip_e13_1, flip_e13_2, flip_e13_3, flip_e13_4, flip_e13_5, flip_e13_6, flip_e13_7]
  simp only [sgp_e13_0, sgp_e13_1, sgp_e13_2, sgp_e13_3, sgp_e13_4, sgp_e13_5, sgp_e13_6, sgp_e13_7, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem inc_e14 : S1.filter (fun y => SS.bxor y e14 ∈ S0) = {z1, z3, z5, z7, z10, z12, z13, z15} := by decide
theorem flip_e14_0 : SS.bxor z1 e14 = y2 := by decide
theorem flip_e14_1 : SS.bxor z3 e14 = y3 := by decide
theorem flip_e14_2 : SS.bxor z5 e14 = y5 := by decide
theorem flip_e14_3 : SS.bxor z7 e14 = y0 := by decide
theorem flip_e14_4 : SS.bxor z10 e14 = y10 := by decide
theorem flip_e14_5 : SS.bxor z12 e14 = y12 := by decide
theorem flip_e14_6 : SS.bxor z13 e14 = y14 := by decide
theorem flip_e14_7 : SS.bxor z15 e14 = y8 := by decide
theorem sgz_e14_0 : SS.bdot wz z1 = false := by decide
theorem sgz_e14_1 : SS.bdot wz z3 = false := by decide
theorem sgz_e14_2 : SS.bdot wz z5 = false := by decide
theorem sgz_e14_3 : SS.bdot wz z7 = false := by decide
theorem sgz_e14_4 : SS.bdot wz z10 = false := by decide
theorem sgz_e14_5 : SS.bdot wz z12 = false := by decide
theorem sgz_e14_6 : SS.bdot wz z13 = false := by decide
theorem sgz_e14_7 : SS.bdot wz z15 = false := by decide
theorem ex_e14_z (c d : SS.BitString 6 -> ℂ) :
    offSum c d e14 wz = star (c y2) * d z1 + star (c y3) * d z3 + star (c y5) * d z5 + star (c y0) * d z7 + star (c y10) * d z10 + star (c y12) * d z12 + star (c y14) * d z13 + star (c y8) * d z15 := by
  unfold offSum
  rw [inc_e14]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_e14_0, flip_e14_1, flip_e14_2, flip_e14_3, flip_e14_4, flip_e14_5, flip_e14_6, flip_e14_7]
  simp only [sgz_e14_0, sgz_e14_1, sgz_e14_2, sgz_e14_3, sgz_e14_4, sgz_e14_5, sgz_e14_6, sgz_e14_7, SixQubit.signMul_false]
  try ring
theorem sgp_e14_0 : SS.bdot wp1 z1 = false := by decide
theorem sgp_e14_1 : SS.bdot wp1 z3 = false := by decide
theorem sgp_e14_2 : SS.bdot wp1 z5 = false := by decide
theorem sgp_e14_3 : SS.bdot wp1 z7 = true := by decide
theorem sgp_e14_4 : SS.bdot wp1 z10 = false := by decide
theorem sgp_e14_5 : SS.bdot wp1 z12 = false := by decide
theorem sgp_e14_6 : SS.bdot wp1 z13 = false := by decide
theorem sgp_e14_7 : SS.bdot wp1 z15 = true := by decide
theorem ex_e14_p (c d : SS.BitString 6 -> ℂ) :
    offSum c d e14 wp1 = star (c y2) * d z1 + star (c y3) * d z3 + star (c y5) * d z5 - star (c y0) * d z7 + star (c y10) * d z10 + star (c y12) * d z12 + star (c y14) * d z13 - star (c y8) * d z15 := by
  unfold offSum
  rw [inc_e14]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_e14_0, flip_e14_1, flip_e14_2, flip_e14_3, flip_e14_4, flip_e14_5, flip_e14_6, flip_e14_7]
  simp only [sgp_e14_0, sgp_e14_1, sgp_e14_2, sgp_e14_3, sgp_e14_4, sgp_e14_5, sgp_e14_6, sgp_e14_7, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem inc_e15 : S1.filter (fun y => SS.bxor y e15 ∈ S0) = {z2, z4, z5, z6, z11, z12, z13, z15} := by decide
theorem flip_e15_0 : SS.bxor z2 e15 = y2 := by decide
theorem flip_e15_1 : SS.bxor z4 e15 = y3 := by decide
theorem flip_e15_2 : SS.bxor z5 e15 = y4 := by decide
theorem flip_e15_3 : SS.bxor z6 e15 = y0 := by decide
theorem flip_e15_4 : SS.bxor z11 e15 = y10 := by decide
theorem flip_e15_5 : SS.bxor z12 e15 = y11 := by decide
theorem flip_e15_6 : SS.bxor z13 e15 = y13 := by decide
theorem flip_e15_7 : SS.bxor z15 e15 = y9 := by decide
theorem sgz_e15_0 : SS.bdot wz z2 = false := by decide
theorem sgz_e15_1 : SS.bdot wz z4 = false := by decide
theorem sgz_e15_2 : SS.bdot wz z5 = false := by decide
theorem sgz_e15_3 : SS.bdot wz z6 = false := by decide
theorem sgz_e15_4 : SS.bdot wz z11 = false := by decide
theorem sgz_e15_5 : SS.bdot wz z12 = false := by decide
theorem sgz_e15_6 : SS.bdot wz z13 = false := by decide
theorem sgz_e15_7 : SS.bdot wz z15 = false := by decide
theorem ex_e15_z (c d : SS.BitString 6 -> ℂ) :
    offSum c d e15 wz = star (c y2) * d z2 + star (c y3) * d z4 + star (c y4) * d z5 + star (c y0) * d z6 + star (c y10) * d z11 + star (c y11) * d z12 + star (c y13) * d z13 + star (c y9) * d z15 := by
  unfold offSum
  rw [inc_e15]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_e15_0, flip_e15_1, flip_e15_2, flip_e15_3, flip_e15_4, flip_e15_5, flip_e15_6, flip_e15_7]
  simp only [sgz_e15_0, sgz_e15_1, sgz_e15_2, sgz_e15_3, sgz_e15_4, sgz_e15_5, sgz_e15_6, sgz_e15_7, SixQubit.signMul_false]
  try ring
theorem sgp_e15_0 : SS.bdot wp1 z2 = false := by decide
theorem sgp_e15_1 : SS.bdot wp1 z4 = false := by decide
theorem sgp_e15_2 : SS.bdot wp1 z5 = false := by decide
theorem sgp_e15_3 : SS.bdot wp1 z6 = true := by decide
theorem sgp_e15_4 : SS.bdot wp1 z11 = false := by decide
theorem sgp_e15_5 : SS.bdot wp1 z12 = false := by decide
theorem sgp_e15_6 : SS.bdot wp1 z13 = false := by decide
theorem sgp_e15_7 : SS.bdot wp1 z15 = true := by decide
theorem ex_e15_p (c d : SS.BitString 6 -> ℂ) :
    offSum c d e15 wp1 = star (c y2) * d z2 + star (c y3) * d z4 + star (c y4) * d z5 - star (c y0) * d z6 + star (c y10) * d z11 + star (c y11) * d z12 + star (c y13) * d z13 - star (c y9) * d z15 := by
  unfold offSum
  rw [inc_e15]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_e15_0, flip_e15_1, flip_e15_2, flip_e15_3, flip_e15_4, flip_e15_5, flip_e15_6, flip_e15_7]
  simp only [sgp_e15_0, sgp_e15_1, sgp_e15_2, sgp_e15_3, sgp_e15_4, sgp_e15_5, sgp_e15_6, sgp_e15_7, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem inc_e23 : S1.filter (fun y => SS.bxor y e23 ∈ S0) = {z0, z5, z6, z7, z10, z11, z14, z15} := by decide
theorem flip_e23_0 : SS.bxor z0 e23 = y1 := by decide
theorem flip_e23_1 : SS.bxor z5 e23 = y0 := by decide
theorem flip_e23_2 : SS.bxor z6 e23 = y4 := by decide
theorem flip_e23_3 : SS.bxor z7 e23 = y5 := by decide
theorem flip_e23_4 : SS.bxor z10 e23 = y8 := by decide
theorem flip_e23_5 : SS.bxor z11 e23 = y9 := by decide
theorem flip_e23_6 : SS.bxor z14 e23 = y15 := by decide
theorem flip_e23_7 : SS.bxor z15 e23 = y10 := by decide
theorem sgz_e23_0 : SS.bdot wz z0 = false := by decide
theorem sgz_e23_1 : SS.bdot wz z5 = false := by decide
theorem sgz_e23_2 : SS.bdot wz z6 = false := by decide
theorem sgz_e23_3 : SS.bdot wz z7 = false := by decide
theorem sgz_e23_4 : SS.bdot wz z10 = false := by decide
theorem sgz_e23_5 : SS.bdot wz z11 = false := by decide
theorem sgz_e23_6 : SS.bdot wz z14 = false := by decide
theorem sgz_e23_7 : SS.bdot wz z15 = false := by decide
theorem ex_e23_z (c d : SS.BitString 6 -> ℂ) :
    offSum c d e23 wz = star (c y1) * d z0 + star (c y0) * d z5 + star (c y4) * d z6 + star (c y5) * d z7 + star (c y8) * d z10 + star (c y9) * d z11 + star (c y15) * d z14 + star (c y10) * d z15 := by
  unfold offSum
  rw [inc_e23]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_e23_0, flip_e23_1, flip_e23_2, flip_e23_3, flip_e23_4, flip_e23_5, flip_e23_6, flip_e23_7]
  simp only [sgz_e23_0, sgz_e23_1, sgz_e23_2, sgz_e23_3, sgz_e23_4, sgz_e23_5, sgz_e23_6, sgz_e23_7, SixQubit.signMul_false]
  try ring
theorem sgp_e23_0 : SS.bdot wp2 z0 = false := by decide
theorem sgp_e23_1 : SS.bdot wp2 z5 = true := by decide
theorem sgp_e23_2 : SS.bdot wp2 z6 = false := by decide
theorem sgp_e23_3 : SS.bdot wp2 z7 = false := by decide
theorem sgp_e23_4 : SS.bdot wp2 z10 = false := by decide
theorem sgp_e23_5 : SS.bdot wp2 z11 = false := by decide
theorem sgp_e23_6 : SS.bdot wp2 z14 = false := by decide
theorem sgp_e23_7 : SS.bdot wp2 z15 = true := by decide
theorem ex_e23_p (c d : SS.BitString 6 -> ℂ) :
    offSum c d e23 wp2 = star (c y1) * d z0 - star (c y0) * d z5 + star (c y4) * d z6 + star (c y5) * d z7 + star (c y8) * d z10 + star (c y9) * d z11 + star (c y15) * d z14 - star (c y10) * d z15 := by
  unfold offSum
  rw [inc_e23]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_e23_0, flip_e23_1, flip_e23_2, flip_e23_3, flip_e23_4, flip_e23_5, flip_e23_6, flip_e23_7]
  simp only [sgp_e23_0, sgp_e23_1, sgp_e23_2, sgp_e23_3, sgp_e23_4, sgp_e23_5, sgp_e23_6, sgp_e23_7, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem inc_e24 : S1.filter (fun y => SS.bxor y e24 ∈ S0) = {z1, z4, z6, z8, z10, z12, z14, z15} := by decide
theorem flip_e24_0 : SS.bxor z1 e24 = y1 := by decide
theorem flip_e24_1 : SS.bxor z4 e24 = y0 := by decide
theorem flip_e24_2 : SS.bxor z6 e24 = y3 := by decide
theorem flip_e24_3 : SS.bxor z8 e24 = y5 := by decide
theorem flip_e24_4 : SS.bxor z10 e24 = y7 := by decide
theorem flip_e24_5 : SS.bxor z12 e24 = y9 := by decide
theorem flip_e24_6 : SS.bxor z14 e24 = y14 := by decide
theorem flip_e24_7 : SS.bxor z15 e24 = y11 := by decide
theorem sgz_e24_0 : SS.bdot wz z1 = false := by decide
theorem sgz_e24_1 : SS.bdot wz z4 = false := by decide
theorem sgz_e24_2 : SS.bdot wz z6 = false := by decide
theorem sgz_e24_3 : SS.bdot wz z8 = false := by decide
theorem sgz_e24_4 : SS.bdot wz z10 = false := by decide
theorem sgz_e24_5 : SS.bdot wz z12 = false := by decide
theorem sgz_e24_6 : SS.bdot wz z14 = false := by decide
theorem sgz_e24_7 : SS.bdot wz z15 = false := by decide
theorem ex_e24_z (c d : SS.BitString 6 -> ℂ) :
    offSum c d e24 wz = star (c y1) * d z1 + star (c y0) * d z4 + star (c y3) * d z6 + star (c y5) * d z8 + star (c y7) * d z10 + star (c y9) * d z12 + star (c y14) * d z14 + star (c y11) * d z15 := by
  unfold offSum
  rw [inc_e24]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_e24_0, flip_e24_1, flip_e24_2, flip_e24_3, flip_e24_4, flip_e24_5, flip_e24_6, flip_e24_7]
  simp only [sgz_e24_0, sgz_e24_1, sgz_e24_2, sgz_e24_3, sgz_e24_4, sgz_e24_5, sgz_e24_6, sgz_e24_7, SixQubit.signMul_false]
  try ring
theorem sgp_e24_0 : SS.bdot wp2 z1 = false := by decide
theorem sgp_e24_1 : SS.bdot wp2 z4 = true := by decide
theorem sgp_e24_2 : SS.bdot wp2 z6 = false := by decide
theorem sgp_e24_3 : SS.bdot wp2 z8 = false := by decide
theorem sgp_e24_4 : SS.bdot wp2 z10 = false := by decide
theorem sgp_e24_5 : SS.bdot wp2 z12 = false := by decide
theorem sgp_e24_6 : SS.bdot wp2 z14 = false := by decide
theorem sgp_e24_7 : SS.bdot wp2 z15 = true := by decide
theorem ex_e24_p (c d : SS.BitString 6 -> ℂ) :
    offSum c d e24 wp2 = star (c y1) * d z1 - star (c y0) * d z4 + star (c y3) * d z6 + star (c y5) * d z8 + star (c y7) * d z10 + star (c y9) * d z12 + star (c y14) * d z14 - star (c y11) * d z15 := by
  unfold offSum
  rw [inc_e24]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_e24_0, flip_e24_1, flip_e24_2, flip_e24_3, flip_e24_4, flip_e24_5, flip_e24_6, flip_e24_7]
  simp only [sgp_e24_0, sgp_e24_1, sgp_e24_2, sgp_e24_3, sgp_e24_4, sgp_e24_5, sgp_e24_6, sgp_e24_7, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem inc_e25 : S1.filter (fun y => SS.bxor y e25 ∈ S0) = {z2, z3, z7, z8, z11, z12, z14, z15} := by decide
theorem flip_e25_0 : SS.bxor z2 e25 = y1 := by decide
theorem flip_e25_1 : SS.bxor z3 e25 = y0 := by decide
theorem flip_e25_2 : SS.bxor z7 e25 = y3 := by decide
theorem flip_e25_3 : SS.bxor z8 e25 = y4 := by decide
theorem flip_e25_4 : SS.bxor z11 e25 = y7 := by decide
theorem flip_e25_5 : SS.bxor z12 e25 = y8 := by decide
theorem flip_e25_6 : SS.bxor z14 e25 = y13 := by decide
theorem flip_e25_7 : SS.bxor z15 e25 = y12 := by decide
theorem sgz_e25_0 : SS.bdot wz z2 = false := by decide
theorem sgz_e25_1 : SS.bdot wz z3 = false := by decide
theorem sgz_e25_2 : SS.bdot wz z7 = false := by decide
theorem sgz_e25_3 : SS.bdot wz z8 = false := by decide
theorem sgz_e25_4 : SS.bdot wz z11 = false := by decide
theorem sgz_e25_5 : SS.bdot wz z12 = false := by decide
theorem sgz_e25_6 : SS.bdot wz z14 = false := by decide
theorem sgz_e25_7 : SS.bdot wz z15 = false := by decide
theorem ex_e25_z (c d : SS.BitString 6 -> ℂ) :
    offSum c d e25 wz = star (c y1) * d z2 + star (c y0) * d z3 + star (c y3) * d z7 + star (c y4) * d z8 + star (c y7) * d z11 + star (c y8) * d z12 + star (c y13) * d z14 + star (c y12) * d z15 := by
  unfold offSum
  rw [inc_e25]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_e25_0, flip_e25_1, flip_e25_2, flip_e25_3, flip_e25_4, flip_e25_5, flip_e25_6, flip_e25_7]
  simp only [sgz_e25_0, sgz_e25_1, sgz_e25_2, sgz_e25_3, sgz_e25_4, sgz_e25_5, sgz_e25_6, sgz_e25_7, SixQubit.signMul_false]
  try ring
theorem sgp_e25_0 : SS.bdot wp2 z2 = false := by decide
theorem sgp_e25_1 : SS.bdot wp2 z3 = true := by decide
theorem sgp_e25_2 : SS.bdot wp2 z7 = false := by decide
theorem sgp_e25_3 : SS.bdot wp2 z8 = false := by decide
theorem sgp_e25_4 : SS.bdot wp2 z11 = false := by decide
theorem sgp_e25_5 : SS.bdot wp2 z12 = false := by decide
theorem sgp_e25_6 : SS.bdot wp2 z14 = false := by decide
theorem sgp_e25_7 : SS.bdot wp2 z15 = true := by decide
theorem ex_e25_p (c d : SS.BitString 6 -> ℂ) :
    offSum c d e25 wp2 = star (c y1) * d z2 - star (c y0) * d z3 + star (c y3) * d z7 + star (c y4) * d z8 + star (c y7) * d z11 + star (c y8) * d z12 + star (c y13) * d z14 - star (c y12) * d z15 := by
  unfold offSum
  rw [inc_e25]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_e25_0, flip_e25_1, flip_e25_2, flip_e25_3, flip_e25_4, flip_e25_5, flip_e25_6, flip_e25_7]
  simp only [sgp_e25_0, sgp_e25_1, sgp_e25_2, sgp_e25_3, sgp_e25_4, sgp_e25_5, sgp_e25_6, sgp_e25_7, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem inc_e34 : S1.filter (fun y => SS.bxor y e34 ∈ S0) = {z2, z3, z6, z9, z10, z13, z14, z15} := by decide
theorem flip_e34_0 : SS.bxor z2 e34 = y0 := by decide
theorem flip_e34_1 : SS.bxor z3 e34 = y1 := by decide
theorem flip_e34_2 : SS.bxor z6 e34 = y2 := by decide
theorem flip_e34_3 : SS.bxor z9 e34 = y5 := by decide
theorem flip_e34_4 : SS.bxor z10 e34 = y6 := by decide
theorem flip_e34_5 : SS.bxor z13 e34 = y9 := by decide
theorem flip_e34_6 : SS.bxor z14 e34 = y12 := by decide
theorem flip_e34_7 : SS.bxor z15 e34 = y13 := by decide
theorem sgz_e34_0 : SS.bdot wz z2 = false := by decide
theorem sgz_e34_1 : SS.bdot wz z3 = false := by decide
theorem sgz_e34_2 : SS.bdot wz z6 = false := by decide
theorem sgz_e34_3 : SS.bdot wz z9 = false := by decide
theorem sgz_e34_4 : SS.bdot wz z10 = false := by decide
theorem sgz_e34_5 : SS.bdot wz z13 = false := by decide
theorem sgz_e34_6 : SS.bdot wz z14 = false := by decide
theorem sgz_e34_7 : SS.bdot wz z15 = false := by decide
theorem ex_e34_z (c d : SS.BitString 6 -> ℂ) :
    offSum c d e34 wz = star (c y0) * d z2 + star (c y1) * d z3 + star (c y2) * d z6 + star (c y5) * d z9 + star (c y6) * d z10 + star (c y9) * d z13 + star (c y12) * d z14 + star (c y13) * d z15 := by
  unfold offSum
  rw [inc_e34]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_e34_0, flip_e34_1, flip_e34_2, flip_e34_3, flip_e34_4, flip_e34_5, flip_e34_6, flip_e34_7]
  simp only [sgz_e34_0, sgz_e34_1, sgz_e34_2, sgz_e34_3, sgz_e34_4, sgz_e34_5, sgz_e34_6, sgz_e34_7, SixQubit.signMul_false]
  try ring
theorem sgp_e34_0 : SS.bdot wp3 z2 = true := by decide
theorem sgp_e34_1 : SS.bdot wp3 z3 = false := by decide
theorem sgp_e34_2 : SS.bdot wp3 z6 = false := by decide
theorem sgp_e34_3 : SS.bdot wp3 z9 = false := by decide
theorem sgp_e34_4 : SS.bdot wp3 z10 = false := by decide
theorem sgp_e34_5 : SS.bdot wp3 z13 = false := by decide
theorem sgp_e34_6 : SS.bdot wp3 z14 = false := by decide
theorem sgp_e34_7 : SS.bdot wp3 z15 = true := by decide
theorem ex_e34_p (c d : SS.BitString 6 -> ℂ) :
    offSum c d e34 wp3 = - star (c y0) * d z2 + star (c y1) * d z3 + star (c y2) * d z6 + star (c y5) * d z9 + star (c y6) * d z10 + star (c y9) * d z13 + star (c y12) * d z14 - star (c y13) * d z15 := by
  unfold offSum
  rw [inc_e34]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_e34_0, flip_e34_1, flip_e34_2, flip_e34_3, flip_e34_4, flip_e34_5, flip_e34_6, flip_e34_7]
  simp only [sgp_e34_0, sgp_e34_1, sgp_e34_2, sgp_e34_3, sgp_e34_4, sgp_e34_5, sgp_e34_6, sgp_e34_7, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem inc_e35 : S1.filter (fun y => SS.bxor y e35 ∈ S0) = {z1, z4, z7, z9, z11, z13, z14, z15} := by decide
theorem flip_e35_0 : SS.bxor z1 e35 = y0 := by decide
theorem flip_e35_1 : SS.bxor z4 e35 = y1 := by decide
theorem flip_e35_2 : SS.bxor z7 e35 = y2 := by decide
theorem flip_e35_3 : SS.bxor z9 e35 = y4 := by decide
theorem flip_e35_4 : SS.bxor z11 e35 = y6 := by decide
theorem flip_e35_5 : SS.bxor z13 e35 = y8 := by decide
theorem flip_e35_6 : SS.bxor z14 e35 = y11 := by decide
theorem flip_e35_7 : SS.bxor z15 e35 = y14 := by decide
theorem sgz_e35_0 : SS.bdot wz z1 = false := by decide
theorem sgz_e35_1 : SS.bdot wz z4 = false := by decide
theorem sgz_e35_2 : SS.bdot wz z7 = false := by decide
theorem sgz_e35_3 : SS.bdot wz z9 = false := by decide
theorem sgz_e35_4 : SS.bdot wz z11 = false := by decide
theorem sgz_e35_5 : SS.bdot wz z13 = false := by decide
theorem sgz_e35_6 : SS.bdot wz z14 = false := by decide
theorem sgz_e35_7 : SS.bdot wz z15 = false := by decide
theorem ex_e35_z (c d : SS.BitString 6 -> ℂ) :
    offSum c d e35 wz = star (c y0) * d z1 + star (c y1) * d z4 + star (c y2) * d z7 + star (c y4) * d z9 + star (c y6) * d z11 + star (c y8) * d z13 + star (c y11) * d z14 + star (c y14) * d z15 := by
  unfold offSum
  rw [inc_e35]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_e35_0, flip_e35_1, flip_e35_2, flip_e35_3, flip_e35_4, flip_e35_5, flip_e35_6, flip_e35_7]
  simp only [sgz_e35_0, sgz_e35_1, sgz_e35_2, sgz_e35_3, sgz_e35_4, sgz_e35_5, sgz_e35_6, sgz_e35_7, SixQubit.signMul_false]
  try ring
theorem sgp_e35_0 : SS.bdot wp3 z1 = true := by decide
theorem sgp_e35_1 : SS.bdot wp3 z4 = false := by decide
theorem sgp_e35_2 : SS.bdot wp3 z7 = false := by decide
theorem sgp_e35_3 : SS.bdot wp3 z9 = false := by decide
theorem sgp_e35_4 : SS.bdot wp3 z11 = false := by decide
theorem sgp_e35_5 : SS.bdot wp3 z13 = false := by decide
theorem sgp_e35_6 : SS.bdot wp3 z14 = false := by decide
theorem sgp_e35_7 : SS.bdot wp3 z15 = true := by decide
theorem ex_e35_p (c d : SS.BitString 6 -> ℂ) :
    offSum c d e35 wp3 = - star (c y0) * d z1 + star (c y1) * d z4 + star (c y2) * d z7 + star (c y4) * d z9 + star (c y6) * d z11 + star (c y8) * d z13 + star (c y11) * d z14 - star (c y14) * d z15 := by
  unfold offSum
  rw [inc_e35]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_e35_0, flip_e35_1, flip_e35_2, flip_e35_3, flip_e35_4, flip_e35_5, flip_e35_6, flip_e35_7]
  simp only [sgp_e35_0, sgp_e35_1, sgp_e35_2, sgp_e35_3, sgp_e35_4, sgp_e35_5, sgp_e35_6, sgp_e35_7, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem inc_e45 : S1.filter (fun y => SS.bxor y e45 ∈ S0) = {z0, z5, z8, z9, z12, z13, z14, z15} := by decide
theorem flip_e45_0 : SS.bxor z0 e45 = y0 := by decide
theorem flip_e45_1 : SS.bxor z5 e45 = y1 := by decide
theorem flip_e45_2 : SS.bxor z8 e45 = y2 := by decide
theorem flip_e45_3 : SS.bxor z9 e45 = y3 := by decide
theorem flip_e45_4 : SS.bxor z12 e45 = y6 := by decide
theorem flip_e45_5 : SS.bxor z13 e45 = y7 := by decide
theorem flip_e45_6 : SS.bxor z14 e45 = y10 := by decide
theorem flip_e45_7 : SS.bxor z15 e45 = y15 := by decide
theorem sgz_e45_0 : SS.bdot wz z0 = false := by decide
theorem sgz_e45_1 : SS.bdot wz z5 = false := by decide
theorem sgz_e45_2 : SS.bdot wz z8 = false := by decide
theorem sgz_e45_3 : SS.bdot wz z9 = false := by decide
theorem sgz_e45_4 : SS.bdot wz z12 = false := by decide
theorem sgz_e45_5 : SS.bdot wz z13 = false := by decide
theorem sgz_e45_6 : SS.bdot wz z14 = false := by decide
theorem sgz_e45_7 : SS.bdot wz z15 = false := by decide
theorem ex_e45_z (c d : SS.BitString 6 -> ℂ) :
    offSum c d e45 wz = star (c y0) * d z0 + star (c y1) * d z5 + star (c y2) * d z8 + star (c y3) * d z9 + star (c y6) * d z12 + star (c y7) * d z13 + star (c y10) * d z14 + star (c y15) * d z15 := by
  unfold offSum
  rw [inc_e45]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_e45_0, flip_e45_1, flip_e45_2, flip_e45_3, flip_e45_4, flip_e45_5, flip_e45_6, flip_e45_7]
  simp only [sgz_e45_0, sgz_e45_1, sgz_e45_2, sgz_e45_3, sgz_e45_4, sgz_e45_5, sgz_e45_6, sgz_e45_7, SixQubit.signMul_false]
  try ring
theorem sgp_e45_0 : SS.bdot wp4 z0 = true := by decide
theorem sgp_e45_1 : SS.bdot wp4 z5 = false := by decide
theorem sgp_e45_2 : SS.bdot wp4 z8 = false := by decide
theorem sgp_e45_3 : SS.bdot wp4 z9 = false := by decide
theorem sgp_e45_4 : SS.bdot wp4 z12 = false := by decide
theorem sgp_e45_5 : SS.bdot wp4 z13 = false := by decide
theorem sgp_e45_6 : SS.bdot wp4 z14 = false := by decide
theorem sgp_e45_7 : SS.bdot wp4 z15 = true := by decide
theorem ex_e45_p (c d : SS.BitString 6 -> ℂ) :
    offSum c d e45 wp4 = - star (c y0) * d z0 + star (c y1) * d z5 + star (c y2) * d z8 + star (c y3) * d z9 + star (c y6) * d z12 + star (c y7) * d z13 + star (c y10) * d z14 - star (c y15) * d z15 := by
  unfold offSum
  rw [inc_e45]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_e45_0, flip_e45_1, flip_e45_2, flip_e45_3, flip_e45_4, flip_e45_5, flip_e45_6, flip_e45_7]
  simp only [sgp_e45_0, sgp_e45_1, sgp_e45_2, sgp_e45_3, sgp_e45_4, sgp_e45_5, sgp_e45_6, sgp_e45_7, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

/-! ## The moment system -/

/-- The two normalizations, the twenty-one moment equalities, and the
nonnegativity of every probability. -/
structure MomentSystem (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real) : Prop where
  n0 : q0 + q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 + q9 + q10 + q11 + q12 + q13 + q14 + q15 = 1
  n1 : r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15 = 1
  m1 : q6 + q7 + q8 + q9 + q10 + q11 + q12 + q13 + q14 + q15 = r10 + r11 + r12 + r13 + r14 + r15
  m2 : q2 + q3 + q4 + q5 + q10 + q11 + q12 + q13 + q14 + q15 = r6 + r7 + r8 + r9 + r14 + r15
  m3 : q1 + q3 + q4 + q5 + q7 + q8 + q9 + q13 + q14 + q15 = r3 + r4 + r5 + r9 + r13 + r15
  m4 : q1 + q2 + q4 + q5 + q6 + q8 + q9 + q11 + q12 + q15 = r1 + r2 + r5 + r8 + r12 + r15
  m5 : q1 + q2 + q3 + q5 + q6 + q7 + q9 + q10 + q12 + q14 = r0 + r2 + r4 + r7 + r11 + r15
  m6 : q1 + q2 + q3 + q4 + q6 + q7 + q8 + q10 + q11 + q13 = r0 + r1 + r3 + r6 + r10 + r15
  m12 : q10 + q11 + q12 + q13 + q14 + q15 = r14 + r15
  m13 : q7 + q8 + q9 + q13 + q14 + q15 = r13 + r15
  m14 : q6 + q8 + q9 + q11 + q12 + q15 = r12 + r15
  m15 : q6 + q7 + q9 + q10 + q12 + q14 = r11 + r15
  m16 : q6 + q7 + q8 + q10 + q11 + q13 = r10 + r15
  m23 : q3 + q4 + q5 + q13 + q14 + q15 = r9 + r15
  m24 : q2 + q4 + q5 + q11 + q12 + q15 = r8 + r15
  m25 : q2 + q3 + q5 + q10 + q12 + q14 = r7 + r15
  m26 : q2 + q3 + q4 + q10 + q11 + q13 = r6 + r15
  m34 : q1 + q4 + q5 + q8 + q9 + q15 = r5 + r15
  m35 : q1 + q3 + q5 + q7 + q9 + q14 = r4 + r15
  m36 : q1 + q3 + q4 + q7 + q8 + q13 = r3 + r15
  m45 : q1 + q2 + q5 + q6 + q9 + q12 = r2 + r15
  m46 : q1 + q2 + q4 + q6 + q8 + q11 = r1 + r15
  m56 : q1 + q2 + q3 + q6 + q7 + q10 = r0 + r15

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

/-- The moment normal form: the top anchor carries mass `1/4`, and the
bottom edge masses are a scaled fractional perfect matching of `K_6`. -/
theorem MomentSystem.normalForm {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real}
    (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    r15 = 1/4 ∧ (q1 + q2 + q3 + q4 + q5 = 1/4) ∧ (q1 + q6 + q7 + q8 + q9 = 1/4) ∧ (q2 + q6 + q10 + q11 + q12 = 1/4) ∧ (q3 + q7 + q10 + q13 + q14 = 1/4) ∧ (q4 + q8 + q11 + q13 + q15 = 1/4) ∧ (q5 + q9 + q12 + q14 + q15 = 1/4) := 
  by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, m12, m13, m14, m15, m16, m23, m24, m25, m26, m34, m35, m36, m45, m46, m56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-! ## The no-go -/

/-- Conjugation does not change the squared modulus. -/
theorem nsq_star (z : ℂ) : Complex.normSq (star z) = Complex.normSq z := by
  rw [Complex.star_def, Complex.normSq_conj]

/-- **Orbit 17 is impossible.** -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11)) (Complex.normSq (c y12)) (Complex.normSq (c y13)) (Complex.normSq (c y14)) (Complex.normSq (c y15))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)) (Complex.normSq (d z12)) (Complex.normSq (d z13)) (Complex.normSq (d z14)) (Complex.normSq (d z15)))
    (ho01a : offSum c d e01 wz = 0)
    (ho01b : offSum c d e01 wp0 = 0)
    (ho02a : offSum c d e02 wz = 0)
    (ho02b : offSum c d e02 wp0 = 0)
    (ho03a : offSum c d e03 wz = 0)
    (ho03b : offSum c d e03 wp0 = 0)
    (ho04a : offSum c d e04 wz = 0)
    (ho04b : offSum c d e04 wp0 = 0)
    (ho05a : offSum c d e05 wz = 0)
    (ho05b : offSum c d e05 wp0 = 0)
    (ho12a : offSum c d e12 wz = 0)
    (ho12b : offSum c d e12 wp1 = 0)
    (ho13a : offSum c d e13 wz = 0)
    (ho13b : offSum c d e13 wp1 = 0)
    (ho14a : offSum c d e14 wz = 0)
    (ho14b : offSum c d e14 wp1 = 0)
    (ho15a : offSum c d e15 wz = 0)
    (ho15b : offSum c d e15 wp1 = 0)
    (ho23a : offSum c d e23 wz = 0)
    (ho23b : offSum c d e23 wp2 = 0)
    (ho24a : offSum c d e24 wz = 0)
    (ho24b : offSum c d e24 wp2 = 0)
    (ho25a : offSum c d e25 wz = 0)
    (ho25b : offSum c d e25 wp2 = 0)
    (ho34a : offSum c d e34 wz = 0)
    (ho34b : offSum c d e34 wp3 = 0)
    (ho35a : offSum c d e35 wz = 0)
    (ho35b : offSum c d e35 wp3 = 0)
    (ho45a : offSum c d e45 wz = 0)
    (ho45b : offSum c d e45 wp4 = 0)
    : False := by
  rw [ex_e01_z] at ho01a
  rw [ex_e01_p] at ho01b
  rw [ex_e02_z] at ho02a
  rw [ex_e02_p] at ho02b
  rw [ex_e03_z] at ho03a
  rw [ex_e03_p] at ho03b
  rw [ex_e04_z] at ho04a
  rw [ex_e04_p] at ho04b
  rw [ex_e05_z] at ho05a
  rw [ex_e05_p] at ho05b
  rw [ex_e12_z] at ho12a
  rw [ex_e12_p] at ho12b
  rw [ex_e13_z] at ho13a
  rw [ex_e13_p] at ho13b
  rw [ex_e14_z] at ho14a
  rw [ex_e14_p] at ho14b
  rw [ex_e15_z] at ho15a
  rw [ex_e15_p] at ho15b
  rw [ex_e23_z] at ho23a
  rw [ex_e23_p] at ho23b
  rw [ex_e24_z] at ho24a
  rw [ex_e24_p] at ho24b
  rw [ex_e25_z] at ho25a
  rw [ex_e25_p] at ho25b
  rw [ex_e34_z] at ho34a
  rw [ex_e34_p] at ho34b
  rw [ex_e35_z] at ho35a
  rw [ex_e35_p] at ho35b
  rw [ex_e45_z] at ho45a
  rw [ex_e45_p] at ho45b
  obtain ⟨hr15, hg0, hg1, hg2, hg3, hg4, hg5⟩ := hm.normalForm
  have hz15 : d z15 ≠ 0 := by
    intro hx
    rw [hx] at hr15
    simp at hr15
  have an01 : star (c y0) * d z14 + star (c y1) * d z15 = 0 := by
    linear_combination (1/2 : ℂ) * ho01a - (1/2 : ℂ) * ho01b
  have an02 : star (c y0) * d z13 + star (c y2) * d z15 = 0 := by
    linear_combination (1/2 : ℂ) * ho02a - (1/2 : ℂ) * ho02b
  have an03 : star (c y0) * d z12 + star (c y3) * d z15 = 0 := by
    linear_combination (1/2 : ℂ) * ho03a - (1/2 : ℂ) * ho03b
  have an04 : star (c y0) * d z11 + star (c y4) * d z15 = 0 := by
    linear_combination (1/2 : ℂ) * ho04a - (1/2 : ℂ) * ho04b
  have an05 : star (c y0) * d z10 + star (c y5) * d z15 = 0 := by
    linear_combination (1/2 : ℂ) * ho05a - (1/2 : ℂ) * ho05b
  have an12 : star (c y0) * d z9 + star (c y6) * d z15 = 0 := by
    linear_combination (1/2 : ℂ) * ho12a - (1/2 : ℂ) * ho12b
  have an13 : star (c y0) * d z8 + star (c y7) * d z15 = 0 := by
    linear_combination (1/2 : ℂ) * ho13a - (1/2 : ℂ) * ho13b
  have an14 : star (c y0) * d z7 + star (c y8) * d z15 = 0 := by
    linear_combination (1/2 : ℂ) * ho14a - (1/2 : ℂ) * ho14b
  have an15 : star (c y0) * d z6 + star (c y9) * d z15 = 0 := by
    linear_combination (1/2 : ℂ) * ho15a - (1/2 : ℂ) * ho15b
  have an23 : star (c y0) * d z5 + star (c y10) * d z15 = 0 := by
    linear_combination (1/2 : ℂ) * ho23a - (1/2 : ℂ) * ho23b
  have an24 : star (c y0) * d z4 + star (c y11) * d z15 = 0 := by
    linear_combination (1/2 : ℂ) * ho24a - (1/2 : ℂ) * ho24b
  have an25 : star (c y0) * d z3 + star (c y12) * d z15 = 0 := by
    linear_combination (1/2 : ℂ) * ho25a - (1/2 : ℂ) * ho25b
  have an34 : star (c y0) * d z2 + star (c y13) * d z15 = 0 := by
    linear_combination (1/2 : ℂ) * ho34a - (1/2 : ℂ) * ho34b
  have an35 : star (c y0) * d z1 + star (c y14) * d z15 = 0 := by
    linear_combination (1/2 : ℂ) * ho35a - (1/2 : ℂ) * ho35b
  have an45 : star (c y0) * d z0 + star (c y15) * d z15 = 0 := by
    linear_combination (1/2 : ℂ) * ho45a - (1/2 : ℂ) * ho45b
  have pf01 : star (c y15) * d z5 + star (c y14) * d z4 + star (c y13) * d z3 + star (c y12) * d z2 + star (c y11) * d z1 + star (c y10) * d z0 = 0 := by
    linear_combination (1/2 : ℂ) * ho01a + (1/2 : ℂ) * ho01b
  have pf02 : star (c y15) * d z8 + star (c y14) * d z7 + star (c y13) * d z6 + star (c y9) * d z2 + star (c y8) * d z1 + star (c y7) * d z0 = 0 := by
    linear_combination (1/2 : ℂ) * ho02a + (1/2 : ℂ) * ho02b
  have pf03 : star (c y15) * d z9 + star (c y12) * d z7 + star (c y11) * d z6 + star (c y9) * d z4 + star (c y8) * d z3 + star (c y6) * d z0 = 0 := by
    linear_combination (1/2 : ℂ) * ho03a + (1/2 : ℂ) * ho03b
  have pf04 : star (c y14) * d z9 + star (c y12) * d z8 + star (c y10) * d z6 + star (c y9) * d z5 + star (c y7) * d z3 + star (c y6) * d z1 = 0 := by
    linear_combination (1/2 : ℂ) * ho04a + (1/2 : ℂ) * ho04b
  have pf05 : star (c y13) * d z9 + star (c y11) * d z8 + star (c y10) * d z7 + star (c y8) * d z5 + star (c y7) * d z4 + star (c y6) * d z2 = 0 := by
    linear_combination (1/2 : ℂ) * ho05a + (1/2 : ℂ) * ho05b
  have pf12 : star (c y15) * d z12 + star (c y14) * d z11 + star (c y13) * d z10 + star (c y5) * d z2 + star (c y4) * d z1 + star (c y3) * d z0 = 0 := by
    linear_combination (1/2 : ℂ) * ho12a + (1/2 : ℂ) * ho12b
  have pf13 : star (c y15) * d z13 + star (c y12) * d z11 + star (c y11) * d z10 + star (c y5) * d z4 + star (c y4) * d z3 + star (c y2) * d z0 = 0 := by
    linear_combination (1/2 : ℂ) * ho13a + (1/2 : ℂ) * ho13b
  have pf14 : star (c y14) * d z13 + star (c y12) * d z12 + star (c y10) * d z10 + star (c y5) * d z5 + star (c y3) * d z3 + star (c y2) * d z1 = 0 := by
    linear_combination (1/2 : ℂ) * ho14a + (1/2 : ℂ) * ho14b
  have pf15 : star (c y13) * d z13 + star (c y11) * d z12 + star (c y10) * d z11 + star (c y4) * d z5 + star (c y3) * d z4 + star (c y2) * d z2 = 0 := by
    linear_combination (1/2 : ℂ) * ho15a + (1/2 : ℂ) * ho15b
  have pf23 : star (c y15) * d z14 + star (c y9) * d z11 + star (c y8) * d z10 + star (c y5) * d z7 + star (c y4) * d z6 + star (c y1) * d z0 = 0 := by
    linear_combination (1/2 : ℂ) * ho23a + (1/2 : ℂ) * ho23b
  have pf24 : star (c y14) * d z14 + star (c y9) * d z12 + star (c y7) * d z10 + star (c y5) * d z8 + star (c y3) * d z6 + star (c y1) * d z1 = 0 := by
    linear_combination (1/2 : ℂ) * ho24a + (1/2 : ℂ) * ho24b
  have pf25 : star (c y13) * d z14 + star (c y8) * d z12 + star (c y7) * d z11 + star (c y4) * d z8 + star (c y3) * d z7 + star (c y1) * d z2 = 0 := by
    linear_combination (1/2 : ℂ) * ho25a + (1/2 : ℂ) * ho25b
  have pf34 : star (c y12) * d z14 + star (c y9) * d z13 + star (c y6) * d z10 + star (c y5) * d z9 + star (c y2) * d z6 + star (c y1) * d z3 = 0 := by
    linear_combination (1/2 : ℂ) * ho34a + (1/2 : ℂ) * ho34b
  have pf35 : star (c y11) * d z14 + star (c y8) * d z13 + star (c y6) * d z11 + star (c y4) * d z9 + star (c y2) * d z7 + star (c y1) * d z4 = 0 := by
    linear_combination (1/2 : ℂ) * ho35a + (1/2 : ℂ) * ho35b
  have pf45 : star (c y10) * d z14 + star (c y7) * d z13 + star (c y6) * d z12 + star (c y3) * d z9 + star (c y2) * d z8 + star (c y1) * d z5 = 0 := by
    linear_combination (1/2 : ℂ) * ho45a + (1/2 : ℂ) * ho45b
  have hf0123 : star (c y1) * star (c y10) + star (c y2) * star (c y7) + star (c y3) * star (c y6) = 0 := by
    have hk : (2 : ℂ) * d z15 * (star (c y1) * star (c y10) + star (c y2) * star (c y7) + star (c y3) * star (c y6)) = 0 := by
      linear_combination star (c y10) * an01 + star (c y7) * an02 + star (c y6) * an03 + star (c y3) * an12 + star (c y2) * an13 + star (c y1) * an23 - star (c y0) * pf45
    exact (mul_eq_zero.mp hk).resolve_left (mul_ne_zero two_ne_zero hz15)
  have hf0124 : star (c y1) * star (c y11) + star (c y2) * star (c y8) + star (c y4) * star (c y6) = 0 := by
    have hk : (2 : ℂ) * d z15 * (star (c y1) * star (c y11) + star (c y2) * star (c y8) + star (c y4) * star (c y6)) = 0 := by
      linear_combination star (c y11) * an01 + star (c y8) * an02 + star (c y6) * an04 + star (c y4) * an12 + star (c y2) * an14 + star (c y1) * an24 - star (c y0) * pf35
    exact (mul_eq_zero.mp hk).resolve_left (mul_ne_zero two_ne_zero hz15)
  have hf0125 : star (c y1) * star (c y12) + star (c y2) * star (c y9) + star (c y5) * star (c y6) = 0 := by
    have hk : (2 : ℂ) * d z15 * (star (c y1) * star (c y12) + star (c y2) * star (c y9) + star (c y5) * star (c y6)) = 0 := by
      linear_combination star (c y12) * an01 + star (c y9) * an02 + star (c y6) * an05 + star (c y5) * an12 + star (c y2) * an15 + star (c y1) * an25 - star (c y0) * pf34
    exact (mul_eq_zero.mp hk).resolve_left (mul_ne_zero two_ne_zero hz15)
  have hf0134 : star (c y1) * star (c y13) + star (c y3) * star (c y8) + star (c y4) * star (c y7) = 0 := by
    have hk : (2 : ℂ) * d z15 * (star (c y1) * star (c y13) + star (c y3) * star (c y8) + star (c y4) * star (c y7)) = 0 := by
      linear_combination star (c y13) * an01 + star (c y8) * an03 + star (c y7) * an04 + star (c y4) * an13 + star (c y3) * an14 + star (c y1) * an34 - star (c y0) * pf25
    exact (mul_eq_zero.mp hk).resolve_left (mul_ne_zero two_ne_zero hz15)
  have hf0135 : star (c y1) * star (c y14) + star (c y3) * star (c y9) + star (c y5) * star (c y7) = 0 := by
    have hk : (2 : ℂ) * d z15 * (star (c y1) * star (c y14) + star (c y3) * star (c y9) + star (c y5) * star (c y7)) = 0 := by
      linear_combination star (c y14) * an01 + star (c y9) * an03 + star (c y7) * an05 + star (c y5) * an13 + star (c y3) * an15 + star (c y1) * an35 - star (c y0) * pf24
    exact (mul_eq_zero.mp hk).resolve_left (mul_ne_zero two_ne_zero hz15)
  have hf0145 : star (c y1) * star (c y15) + star (c y4) * star (c y9) + star (c y5) * star (c y8) = 0 := by
    have hk : (2 : ℂ) * d z15 * (star (c y1) * star (c y15) + star (c y4) * star (c y9) + star (c y5) * star (c y8)) = 0 := by
      linear_combination star (c y15) * an01 + star (c y9) * an04 + star (c y8) * an05 + star (c y5) * an14 + star (c y4) * an15 + star (c y1) * an45 - star (c y0) * pf23
    exact (mul_eq_zero.mp hk).resolve_left (mul_ne_zero two_ne_zero hz15)
  have hf0234 : star (c y2) * star (c y13) + star (c y3) * star (c y11) + star (c y4) * star (c y10) = 0 := by
    have hk : (2 : ℂ) * d z15 * (star (c y2) * star (c y13) + star (c y3) * star (c y11) + star (c y4) * star (c y10)) = 0 := by
      linear_combination star (c y13) * an02 + star (c y11) * an03 + star (c y10) * an04 + star (c y4) * an23 + star (c y3) * an24 + star (c y2) * an34 - star (c y0) * pf15
    exact (mul_eq_zero.mp hk).resolve_left (mul_ne_zero two_ne_zero hz15)
  have hf0235 : star (c y2) * star (c y14) + star (c y3) * star (c y12) + star (c y5) * star (c y10) = 0 := by
    have hk : (2 : ℂ) * d z15 * (star (c y2) * star (c y14) + star (c y3) * star (c y12) + star (c y5) * star (c y10)) = 0 := by
      linear_combination star (c y14) * an02 + star (c y12) * an03 + star (c y10) * an05 + star (c y5) * an23 + star (c y3) * an25 + star (c y2) * an35 - star (c y0) * pf14
    exact (mul_eq_zero.mp hk).resolve_left (mul_ne_zero two_ne_zero hz15)
  have hf0245 : star (c y2) * star (c y15) + star (c y4) * star (c y12) + star (c y5) * star (c y11) = 0 := by
    have hk : (2 : ℂ) * d z15 * (star (c y2) * star (c y15) + star (c y4) * star (c y12) + star (c y5) * star (c y11)) = 0 := by
      linear_combination star (c y15) * an02 + star (c y12) * an04 + star (c y11) * an05 + star (c y5) * an24 + star (c y4) * an25 + star (c y2) * an45 - star (c y0) * pf13
    exact (mul_eq_zero.mp hk).resolve_left (mul_ne_zero two_ne_zero hz15)
  have hf0345 : star (c y3) * star (c y15) + star (c y4) * star (c y14) + star (c y5) * star (c y13) = 0 := by
    have hk : (2 : ℂ) * d z15 * (star (c y3) * star (c y15) + star (c y4) * star (c y14) + star (c y5) * star (c y13)) = 0 := by
      linear_combination star (c y15) * an03 + star (c y14) * an04 + star (c y13) * an05 + star (c y5) * an34 + star (c y4) * an35 + star (c y3) * an45 - star (c y0) * pf12
    exact (mul_eq_zero.mp hk).resolve_left (mul_ne_zero two_ne_zero hz15)
  have hf1234 : star (c y6) * star (c y13) + star (c y7) * star (c y11) + star (c y8) * star (c y10) = 0 := by
    have hk : (2 : ℂ) * d z15 * (star (c y6) * star (c y13) + star (c y7) * star (c y11) + star (c y8) * star (c y10)) = 0 := by
      linear_combination star (c y13) * an12 + star (c y11) * an13 + star (c y10) * an14 + star (c y8) * an23 + star (c y7) * an24 + star (c y6) * an34 - star (c y0) * pf05
    exact (mul_eq_zero.mp hk).resolve_left (mul_ne_zero two_ne_zero hz15)
  have hf1235 : star (c y6) * star (c y14) + star (c y7) * star (c y12) + star (c y9) * star (c y10) = 0 := by
    have hk : (2 : ℂ) * d z15 * (star (c y6) * star (c y14) + star (c y7) * star (c y12) + star (c y9) * star (c y10)) = 0 := by
      linear_combination star (c y14) * an12 + star (c y12) * an13 + star (c y10) * an15 + star (c y9) * an23 + star (c y7) * an25 + star (c y6) * an35 - star (c y0) * pf04
    exact (mul_eq_zero.mp hk).resolve_left (mul_ne_zero two_ne_zero hz15)
  have hf1245 : star (c y6) * star (c y15) + star (c y8) * star (c y12) + star (c y9) * star (c y11) = 0 := by
    have hk : (2 : ℂ) * d z15 * (star (c y6) * star (c y15) + star (c y8) * star (c y12) + star (c y9) * star (c y11)) = 0 := by
      linear_combination star (c y15) * an12 + star (c y12) * an14 + star (c y11) * an15 + star (c y9) * an24 + star (c y8) * an25 + star (c y6) * an45 - star (c y0) * pf03
    exact (mul_eq_zero.mp hk).resolve_left (mul_ne_zero two_ne_zero hz15)
  have hf1345 : star (c y7) * star (c y15) + star (c y8) * star (c y14) + star (c y9) * star (c y13) = 0 := by
    have hk : (2 : ℂ) * d z15 * (star (c y7) * star (c y15) + star (c y8) * star (c y14) + star (c y9) * star (c y13)) = 0 := by
      linear_combination star (c y15) * an13 + star (c y14) * an14 + star (c y13) * an15 + star (c y9) * an34 + star (c y8) * an35 + star (c y7) * an45 - star (c y0) * pf02
    exact (mul_eq_zero.mp hk).resolve_left (mul_ne_zero two_ne_zero hz15)
  have hf2345 : star (c y10) * star (c y15) + star (c y11) * star (c y14) + star (c y12) * star (c y13) = 0 := by
    have hk : (2 : ℂ) * d z15 * (star (c y10) * star (c y15) + star (c y11) * star (c y14) + star (c y12) * star (c y13)) = 0 := by
      linear_combination star (c y15) * an23 + star (c y14) * an24 + star (c y13) * an25 + star (c y12) * an34 + star (c y11) * an35 + star (c y10) * an45 - star (c y0) * pf01
    exact (mul_eq_zero.mp hk).resolve_left (mul_ne_zero two_ne_zero hz15)
  have hs0 : Complex.normSq (star (c y1)) + Complex.normSq (star (c y2)) + Complex.normSq (star (c y3)) + Complex.normSq (star (c y4)) + Complex.normSq (star (c y5)) = 1/4 := by
    simp only [nsq_star]
    linarith [hg0]
  have hs1 : Complex.normSq (star (c y1)) + Complex.normSq (star (c y6)) + Complex.normSq (star (c y7)) + Complex.normSq (star (c y8)) + Complex.normSq (star (c y9)) = 1/4 := by
    simp only [nsq_star]
    linarith [hg1]
  have hs2 : Complex.normSq (star (c y2)) + Complex.normSq (star (c y6)) + Complex.normSq (star (c y10)) + Complex.normSq (star (c y11)) + Complex.normSq (star (c y12)) = 1/4 := by
    simp only [nsq_star]
    linarith [hg2]
  have hs3 : Complex.normSq (star (c y3)) + Complex.normSq (star (c y7)) + Complex.normSq (star (c y10)) + Complex.normSq (star (c y13)) + Complex.normSq (star (c y14)) = 1/4 := by
    simp only [nsq_star]
    linarith [hg3]
  have hs4 : Complex.normSq (star (c y4)) + Complex.normSq (star (c y8)) + Complex.normSq (star (c y11)) + Complex.normSq (star (c y13)) + Complex.normSq (star (c y15)) = 1/4 := by
    simp only [nsq_star]
    linarith [hg4]
  have hs5 : Complex.normSq (star (c y5)) + Complex.normSq (star (c y9)) + Complex.normSq (star (c y12)) + Complex.normSq (star (c y14)) + Complex.normSq (star (c y15)) = 1/4 := by
    simp only [nsq_star]
    linarith [hg5]
  have hsys : SixQubit.Hafnian.Sys (star (c y1)) (star (c y2)) (star (c y3)) (star (c y4)) (star (c y5)) (star (c y6)) (star (c y7)) (star (c y8)) (star (c y9)) (star (c y10)) (star (c y11)) (star (c y12)) (star (c y13)) (star (c y14)) (star (c y15)) :=
    ⟨hf0123, hf0124, hf0125, hf0134, hf0135, hf0145, hf0234, hf0235, hf0245, hf0345, hf1234, hf1235, hf1245, hf1345, hf2345,
     hs0, hs1, hs2, hs3, hs4, hs5⟩
  exact SixQubit.Hafnian.no_go hsys

end

end SixQubit.Orbit17
