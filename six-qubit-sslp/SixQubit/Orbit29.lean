import Mathlib

import SS.FullKL
import SixQubit.Common
import SixQubit.Pair29

/-!
# Six-qubit no-go for moment orbit 29

Orbit 29 of `six_qubit_sslp_v7.tex`: q = 4, angle vector a = (1, 1, 1, 1, 2, 2),
residues 0 and 1, fibers of size sixteen each.

Both fibers are closed under `X_5 X_6`, so each splits into eight pairs.  Read
a pair as a vector in `Cx^2`; then every two-term Knill-Laflamme relation is an
orthogonality, and the twelve that survive realise exactly the six edges of
`K_4` on the four top pairs carrying them.  The moment system supplies the
probabilities, including the uniform identity `P_e = Q_n + Q_m - 1/4` for the
bottom pair on edge `{n,m}`.  `SixQubit.Pair29.pair_contradiction` closes it.

Everything computational is decided by the Lean kernel; `native_decide` is
not used.
-/

namespace SixQubit.Orbit29

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
def y8 : SS.BitString 6 := bs true  false false true  false true   -- 100101
def y9 : SS.BitString 6 := bs true  false false true  true  false  -- 100110
def y10 : SS.BitString 6 := bs true  false true  false false true   -- 101001
def y11 : SS.BitString 6 := bs true  false true  false true  false  -- 101010
def y12 : SS.BitString 6 := bs true  true  false false false true   -- 110001
def y13 : SS.BitString 6 := bs true  true  false false true  false  -- 110010
def y14 : SS.BitString 6 := bs true  true  true  true  false false  -- 111100
def y15 : SS.BitString 6 := bs true  true  true  true  true  true   -- 111111

def z0 : SS.BitString 6 := bs false false false true  false false  -- 000100
def z1 : SS.BitString 6 := bs false false false true  true  true   -- 000111
def z2 : SS.BitString 6 := bs false false true  false false false  -- 001000
def z3 : SS.BitString 6 := bs false false true  false true  true   -- 001011
def z4 : SS.BitString 6 := bs false true  false false false false  -- 010000
def z5 : SS.BitString 6 := bs false true  false false true  true   -- 010011
def z6 : SS.BitString 6 := bs false true  true  true  false true   -- 011101
def z7 : SS.BitString 6 := bs false true  true  true  true  false  -- 011110
def z8 : SS.BitString 6 := bs true  false false false false false  -- 100000
def z9 : SS.BitString 6 := bs true  false false false true  true   -- 100011
def z10 : SS.BitString 6 := bs true  false true  true  false true   -- 101101
def z11 : SS.BitString 6 := bs true  false true  true  true  false  -- 101110
def z12 : SS.BitString 6 := bs true  true  false true  false true   -- 110101
def z13 : SS.BitString 6 := bs true  true  false true  true  false  -- 110110
def z14 : SS.BitString 6 := bs true  true  true  false false true   -- 111001
def z15 : SS.BitString 6 := bs true  true  true  false true  false  -- 111010

def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15}
def S1 : Finset (SS.BitString 6) := {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15}

def av : Fin 6 -> ZMod 4 := ![1, 1, 1, 1, 2, 2]

/-- Each support is exactly its residue fiber, decided over all 64 strings. -/
theorem S0_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 0) = S0 := by
  decide

theorem S1_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 1) = S1 := by
  decide

def ef0 : SS.BitString 6 := bs false false false true  false false  -- mask 000100
def ef1 : SS.BitString 6 := bs false false false true  false true   -- mask 000101
def ef2 : SS.BitString 6 := bs false false false true  true  false  -- mask 000110
def ef3 : SS.BitString 6 := bs false false true  false false false  -- mask 001000
def ef4 : SS.BitString 6 := bs false false true  false false true   -- mask 001001
def ef5 : SS.BitString 6 := bs false false true  false true  false  -- mask 001010
def ef6 : SS.BitString 6 := bs false true  false false false false  -- mask 010000
def ef7 : SS.BitString 6 := bs false true  false false false true   -- mask 010001
def ef8 : SS.BitString 6 := bs false true  false false true  false  -- mask 010010
def ef9 : SS.BitString 6 := bs true  false false false false false  -- mask 100000
def ef10 : SS.BitString 6 := bs true  false false false false true   -- mask 100001
def ef11 : SS.BitString 6 := bs true  false false false true  false  -- mask 100010
def w0 : SS.BitString 6 := bs false false false false false false  -- dressing 000000
def w1 : SS.BitString 6 := bs false false false false false true   -- dressing 000001
def w2 : SS.BitString 6 := bs false false false false true  false  -- dressing 000010
def w3 : SS.BitString 6 := bs false false false true  false false  -- dressing 000100
def w4 : SS.BitString 6 := bs false false true  false false false  -- dressing 001000
def w5 : SS.BitString 6 := bs false true  false false false false  -- dressing 010000
def w6 : SS.BitString 6 := bs true  false false false false false  -- dressing 100000

def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),
      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

/-- `z * star z` is the squared modulus. -/
theorem sq (z : ℂ) : z * star z = (Complex.normSq z : ℂ) := by
  rw [mul_comm, Complex.normSq_eq_conj_mul_self]; rfl

theorem incidence0 :
    S1.filter (fun y => SS.bxor y ef0 ∈ S0) = {z0, z1, z6, z7, z10, z11, z12, z13} := by decide
theorem fl0_0 : SS.bxor z0 ef0 = y0 := by decide
theorem fl0_1 : SS.bxor z1 ef0 = y1 := by decide
theorem fl0_6 : SS.bxor z6 ef0 = y6 := by decide
theorem fl0_7 : SS.bxor z7 ef0 = y7 := by decide
theorem fl0_10 : SS.bxor z10 ef0 = y10 := by decide
theorem fl0_11 : SS.bxor z11 ef0 = y11 := by decide
theorem fl0_12 : SS.bxor z12 ef0 = y12 := by decide
theorem fl0_13 : SS.bxor z13 ef0 = y13 := by decide
theorem sg0_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg0_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg0_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg0_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg0_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg0_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg0_w0_12 : SS.bdot w0 z12 = false := by decide
theorem sg0_w0_13 : SS.bdot w0 z13 = false := by decide
theorem sg0_w4_0 : SS.bdot w4 z0 = false := by decide
theorem sg0_w4_1 : SS.bdot w4 z1 = false := by decide
theorem sg0_w4_6 : SS.bdot w4 z6 = true := by decide
theorem sg0_w4_7 : SS.bdot w4 z7 = true := by decide
theorem sg0_w4_10 : SS.bdot w4 z10 = true := by decide
theorem sg0_w4_11 : SS.bdot w4 z11 = true := by decide
theorem sg0_w4_12 : SS.bdot w4 z12 = false := by decide
theorem sg0_w4_13 : SS.bdot w4 z13 = false := by decide
theorem sg0_w5_0 : SS.bdot w5 z0 = false := by decide
theorem sg0_w5_1 : SS.bdot w5 z1 = false := by decide
theorem sg0_w5_6 : SS.bdot w5 z6 = true := by decide
theorem sg0_w5_7 : SS.bdot w5 z7 = true := by decide
theorem sg0_w5_10 : SS.bdot w5 z10 = false := by decide
theorem sg0_w5_11 : SS.bdot w5 z11 = false := by decide
theorem sg0_w5_12 : SS.bdot w5 z12 = true := by decide
theorem sg0_w5_13 : SS.bdot w5 z13 = true := by decide
theorem sg0_w6_0 : SS.bdot w6 z0 = false := by decide
theorem sg0_w6_1 : SS.bdot w6 z1 = false := by decide
theorem sg0_w6_6 : SS.bdot w6 z6 = false := by decide
theorem sg0_w6_7 : SS.bdot w6 z7 = false := by decide
theorem sg0_w6_10 : SS.bdot w6 z10 = true := by decide
theorem sg0_w6_11 : SS.bdot w6 z11 = true := by decide
theorem sg0_w6_12 : SS.bdot w6 z12 = true := by decide
theorem sg0_w6_13 : SS.bdot w6 z13 = true := by decide
theorem incidence1 :
    S1.filter (fun y => SS.bxor y ef1 ∈ S0) = {z2, z3, z4, z5, z8, z9, z14, z15} := by decide
theorem fl1_2 : SS.bxor z2 ef1 = y2 := by decide
theorem fl1_3 : SS.bxor z3 ef1 = y3 := by decide
theorem fl1_4 : SS.bxor z4 ef1 = y4 := by decide
theorem fl1_5 : SS.bxor z5 ef1 = y5 := by decide
theorem fl1_8 : SS.bxor z8 ef1 = y8 := by decide
theorem fl1_9 : SS.bxor z9 ef1 = y9 := by decide
theorem fl1_14 : SS.bxor z14 ef1 = y14 := by decide
theorem fl1_15 : SS.bxor z15 ef1 = y15 := by decide
theorem sg1_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg1_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg1_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg1_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg1_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg1_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg1_w0_14 : SS.bdot w0 z14 = false := by decide
theorem sg1_w0_15 : SS.bdot w0 z15 = false := by decide
theorem sg1_w1_2 : SS.bdot w1 z2 = false := by decide
theorem sg1_w1_3 : SS.bdot w1 z3 = true := by decide
theorem sg1_w1_4 : SS.bdot w1 z4 = false := by decide
theorem sg1_w1_5 : SS.bdot w1 z5 = true := by decide
theorem sg1_w1_8 : SS.bdot w1 z8 = false := by decide
theorem sg1_w1_9 : SS.bdot w1 z9 = true := by decide
theorem sg1_w1_14 : SS.bdot w1 z14 = true := by decide
theorem sg1_w1_15 : SS.bdot w1 z15 = false := by decide
theorem incidence2 :
    S1.filter (fun y => SS.bxor y ef2 ∈ S0) = {z2, z3, z4, z5, z8, z9, z14, z15} := by decide
theorem fl2_2 : SS.bxor z2 ef2 = y3 := by decide
theorem fl2_3 : SS.bxor z3 ef2 = y2 := by decide
theorem fl2_4 : SS.bxor z4 ef2 = y5 := by decide
theorem fl2_5 : SS.bxor z5 ef2 = y4 := by decide
theorem fl2_8 : SS.bxor z8 ef2 = y9 := by decide
theorem fl2_9 : SS.bxor z9 ef2 = y8 := by decide
theorem fl2_14 : SS.bxor z14 ef2 = y15 := by decide
theorem fl2_15 : SS.bxor z15 ef2 = y14 := by decide
theorem sg2_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg2_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg2_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg2_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg2_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg2_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg2_w0_14 : SS.bdot w0 z14 = false := by decide
theorem sg2_w0_15 : SS.bdot w0 z15 = false := by decide
theorem sg2_w2_2 : SS.bdot w2 z2 = false := by decide
theorem sg2_w2_3 : SS.bdot w2 z3 = true := by decide
theorem sg2_w2_4 : SS.bdot w2 z4 = false := by decide
theorem sg2_w2_5 : SS.bdot w2 z5 = true := by decide
theorem sg2_w2_8 : SS.bdot w2 z8 = false := by decide
theorem sg2_w2_9 : SS.bdot w2 z9 = true := by decide
theorem sg2_w2_14 : SS.bdot w2 z14 = false := by decide
theorem sg2_w2_15 : SS.bdot w2 z15 = true := by decide
theorem incidence3 :
    S1.filter (fun y => SS.bxor y ef3 ∈ S0) = {z2, z3, z6, z7, z10, z11, z14, z15} := by decide
theorem fl3_2 : SS.bxor z2 ef3 = y0 := by decide
theorem fl3_3 : SS.bxor z3 ef3 = y1 := by decide
theorem fl3_6 : SS.bxor z6 ef3 = y4 := by decide
theorem fl3_7 : SS.bxor z7 ef3 = y5 := by decide
theorem fl3_10 : SS.bxor z10 ef3 = y8 := by decide
theorem fl3_11 : SS.bxor z11 ef3 = y9 := by decide
theorem fl3_14 : SS.bxor z14 ef3 = y12 := by decide
theorem fl3_15 : SS.bxor z15 ef3 = y13 := by decide
theorem sg3_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg3_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg3_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg3_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg3_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg3_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg3_w0_14 : SS.bdot w0 z14 = false := by decide
theorem sg3_w0_15 : SS.bdot w0 z15 = false := by decide
theorem sg3_w3_2 : SS.bdot w3 z2 = false := by decide
theorem sg3_w3_3 : SS.bdot w3 z3 = false := by decide
theorem sg3_w3_6 : SS.bdot w3 z6 = true := by decide
theorem sg3_w3_7 : SS.bdot w3 z7 = true := by decide
theorem sg3_w3_10 : SS.bdot w3 z10 = true := by decide
theorem sg3_w3_11 : SS.bdot w3 z11 = true := by decide
theorem sg3_w3_14 : SS.bdot w3 z14 = false := by decide
theorem sg3_w3_15 : SS.bdot w3 z15 = false := by decide
theorem sg3_w5_2 : SS.bdot w5 z2 = false := by decide
theorem sg3_w5_3 : SS.bdot w5 z3 = false := by decide
theorem sg3_w5_6 : SS.bdot w5 z6 = true := by decide
theorem sg3_w5_7 : SS.bdot w5 z7 = true := by decide
theorem sg3_w5_10 : SS.bdot w5 z10 = false := by decide
theorem sg3_w5_11 : SS.bdot w5 z11 = false := by decide
theorem sg3_w5_14 : SS.bdot w5 z14 = true := by decide
theorem sg3_w5_15 : SS.bdot w5 z15 = true := by decide
theorem sg3_w6_2 : SS.bdot w6 z2 = false := by decide
theorem sg3_w6_3 : SS.bdot w6 z3 = false := by decide
theorem sg3_w6_6 : SS.bdot w6 z6 = false := by decide
theorem sg3_w6_7 : SS.bdot w6 z7 = false := by decide
theorem sg3_w6_10 : SS.bdot w6 z10 = true := by decide
theorem sg3_w6_11 : SS.bdot w6 z11 = true := by decide
theorem sg3_w6_14 : SS.bdot w6 z14 = true := by decide
theorem sg3_w6_15 : SS.bdot w6 z15 = true := by decide
theorem incidence4 :
    S1.filter (fun y => SS.bxor y ef4 ∈ S0) = {z0, z1, z4, z5, z8, z9, z12, z13} := by decide
theorem fl4_0 : SS.bxor z0 ef4 = y2 := by decide
theorem fl4_1 : SS.bxor z1 ef4 = y3 := by decide
theorem fl4_4 : SS.bxor z4 ef4 = y6 := by decide
theorem fl4_5 : SS.bxor z5 ef4 = y7 := by decide
theorem fl4_8 : SS.bxor z8 ef4 = y10 := by decide
theorem fl4_9 : SS.bxor z9 ef4 = y11 := by decide
theorem fl4_12 : SS.bxor z12 ef4 = y14 := by decide
theorem fl4_13 : SS.bxor z13 ef4 = y15 := by decide
theorem sg4_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg4_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg4_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg4_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg4_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg4_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg4_w0_12 : SS.bdot w0 z12 = false := by decide
theorem sg4_w0_13 : SS.bdot w0 z13 = false := by decide
theorem sg4_w1_0 : SS.bdot w1 z0 = false := by decide
theorem sg4_w1_1 : SS.bdot w1 z1 = true := by decide
theorem sg4_w1_4 : SS.bdot w1 z4 = false := by decide
theorem sg4_w1_5 : SS.bdot w1 z5 = true := by decide
theorem sg4_w1_8 : SS.bdot w1 z8 = false := by decide
theorem sg4_w1_9 : SS.bdot w1 z9 = true := by decide
theorem sg4_w1_12 : SS.bdot w1 z12 = true := by decide
theorem sg4_w1_13 : SS.bdot w1 z13 = false := by decide
theorem incidence5 :
    S1.filter (fun y => SS.bxor y ef5 ∈ S0) = {z0, z1, z4, z5, z8, z9, z12, z13} := by decide
theorem fl5_0 : SS.bxor z0 ef5 = y3 := by decide
theorem fl5_1 : SS.bxor z1 ef5 = y2 := by decide
theorem fl5_4 : SS.bxor z4 ef5 = y7 := by decide
theorem fl5_5 : SS.bxor z5 ef5 = y6 := by decide
theorem fl5_8 : SS.bxor z8 ef5 = y11 := by decide
theorem fl5_9 : SS.bxor z9 ef5 = y10 := by decide
theorem fl5_12 : SS.bxor z12 ef5 = y15 := by decide
theorem fl5_13 : SS.bxor z13 ef5 = y14 := by decide
theorem sg5_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg5_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg5_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg5_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg5_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg5_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg5_w0_12 : SS.bdot w0 z12 = false := by decide
theorem sg5_w0_13 : SS.bdot w0 z13 = false := by decide
theorem sg5_w2_0 : SS.bdot w2 z0 = false := by decide
theorem sg5_w2_1 : SS.bdot w2 z1 = true := by decide
theorem sg5_w2_4 : SS.bdot w2 z4 = false := by decide
theorem sg5_w2_5 : SS.bdot w2 z5 = true := by decide
theorem sg5_w2_8 : SS.bdot w2 z8 = false := by decide
theorem sg5_w2_9 : SS.bdot w2 z9 = true := by decide
theorem sg5_w2_12 : SS.bdot w2 z12 = false := by decide
theorem sg5_w2_13 : SS.bdot w2 z13 = true := by decide
theorem incidence6 :
    S1.filter (fun y => SS.bxor y ef6 ∈ S0) = {z4, z5, z6, z7, z12, z13, z14, z15} := by decide
theorem fl6_4 : SS.bxor z4 ef6 = y0 := by decide
theorem fl6_5 : SS.bxor z5 ef6 = y1 := by decide
theorem fl6_6 : SS.bxor z6 ef6 = y2 := by decide
theorem fl6_7 : SS.bxor z7 ef6 = y3 := by decide
theorem fl6_12 : SS.bxor z12 ef6 = y8 := by decide
theorem fl6_13 : SS.bxor z13 ef6 = y9 := by decide
theorem fl6_14 : SS.bxor z14 ef6 = y10 := by decide
theorem fl6_15 : SS.bxor z15 ef6 = y11 := by decide
theorem sg6_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg6_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg6_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg6_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg6_w0_12 : SS.bdot w0 z12 = false := by decide
theorem sg6_w0_13 : SS.bdot w0 z13 = false := by decide
theorem sg6_w0_14 : SS.bdot w0 z14 = false := by decide
theorem sg6_w0_15 : SS.bdot w0 z15 = false := by decide
theorem sg6_w3_4 : SS.bdot w3 z4 = false := by decide
theorem sg6_w3_5 : SS.bdot w3 z5 = false := by decide
theorem sg6_w3_6 : SS.bdot w3 z6 = true := by decide
theorem sg6_w3_7 : SS.bdot w3 z7 = true := by decide
theorem sg6_w3_12 : SS.bdot w3 z12 = true := by decide
theorem sg6_w3_13 : SS.bdot w3 z13 = true := by decide
theorem sg6_w3_14 : SS.bdot w3 z14 = false := by decide
theorem sg6_w3_15 : SS.bdot w3 z15 = false := by decide
theorem sg6_w4_4 : SS.bdot w4 z4 = false := by decide
theorem sg6_w4_5 : SS.bdot w4 z5 = false := by decide
theorem sg6_w4_6 : SS.bdot w4 z6 = true := by decide
theorem sg6_w4_7 : SS.bdot w4 z7 = true := by decide
theorem sg6_w4_12 : SS.bdot w4 z12 = false := by decide
theorem sg6_w4_13 : SS.bdot w4 z13 = false := by decide
theorem sg6_w4_14 : SS.bdot w4 z14 = true := by decide
theorem sg6_w4_15 : SS.bdot w4 z15 = true := by decide
theorem sg6_w6_4 : SS.bdot w6 z4 = false := by decide
theorem sg6_w6_5 : SS.bdot w6 z5 = false := by decide
theorem sg6_w6_6 : SS.bdot w6 z6 = false := by decide
theorem sg6_w6_7 : SS.bdot w6 z7 = false := by decide
theorem sg6_w6_12 : SS.bdot w6 z12 = true := by decide
theorem sg6_w6_13 : SS.bdot w6 z13 = true := by decide
theorem sg6_w6_14 : SS.bdot w6 z14 = true := by decide
theorem sg6_w6_15 : SS.bdot w6 z15 = true := by decide
theorem incidence7 :
    S1.filter (fun y => SS.bxor y ef7 ∈ S0) = {z0, z1, z2, z3, z8, z9, z10, z11} := by decide
theorem fl7_0 : SS.bxor z0 ef7 = y4 := by decide
theorem fl7_1 : SS.bxor z1 ef7 = y5 := by decide
theorem fl7_2 : SS.bxor z2 ef7 = y6 := by decide
theorem fl7_3 : SS.bxor z3 ef7 = y7 := by decide
theorem fl7_8 : SS.bxor z8 ef7 = y12 := by decide
theorem fl7_9 : SS.bxor z9 ef7 = y13 := by decide
theorem fl7_10 : SS.bxor z10 ef7 = y14 := by decide
theorem fl7_11 : SS.bxor z11 ef7 = y15 := by decide
theorem sg7_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg7_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg7_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg7_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg7_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg7_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg7_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg7_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg7_w1_0 : SS.bdot w1 z0 = false := by decide
theorem sg7_w1_1 : SS.bdot w1 z1 = true := by decide
theorem sg7_w1_2 : SS.bdot w1 z2 = false := by decide
theorem sg7_w1_3 : SS.bdot w1 z3 = true := by decide
theorem sg7_w1_8 : SS.bdot w1 z8 = false := by decide
theorem sg7_w1_9 : SS.bdot w1 z9 = true := by decide
theorem sg7_w1_10 : SS.bdot w1 z10 = true := by decide
theorem sg7_w1_11 : SS.bdot w1 z11 = false := by decide
theorem incidence8 :
    S1.filter (fun y => SS.bxor y ef8 ∈ S0) = {z0, z1, z2, z3, z8, z9, z10, z11} := by decide
theorem fl8_0 : SS.bxor z0 ef8 = y5 := by decide
theorem fl8_1 : SS.bxor z1 ef8 = y4 := by decide
theorem fl8_2 : SS.bxor z2 ef8 = y7 := by decide
theorem fl8_3 : SS.bxor z3 ef8 = y6 := by decide
theorem fl8_8 : SS.bxor z8 ef8 = y13 := by decide
theorem fl8_9 : SS.bxor z9 ef8 = y12 := by decide
theorem fl8_10 : SS.bxor z10 ef8 = y15 := by decide
theorem fl8_11 : SS.bxor z11 ef8 = y14 := by decide
theorem sg8_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg8_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg8_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg8_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg8_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg8_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg8_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg8_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg8_w2_0 : SS.bdot w2 z0 = false := by decide
theorem sg8_w2_1 : SS.bdot w2 z1 = true := by decide
theorem sg8_w2_2 : SS.bdot w2 z2 = false := by decide
theorem sg8_w2_3 : SS.bdot w2 z3 = true := by decide
theorem sg8_w2_8 : SS.bdot w2 z8 = false := by decide
theorem sg8_w2_9 : SS.bdot w2 z9 = true := by decide
theorem sg8_w2_10 : SS.bdot w2 z10 = false := by decide
theorem sg8_w2_11 : SS.bdot w2 z11 = true := by decide
theorem incidence9 :
    S1.filter (fun y => SS.bxor y ef9 ∈ S0) = {z8, z9, z10, z11, z12, z13, z14, z15} := by decide
theorem fl9_8 : SS.bxor z8 ef9 = y0 := by decide
theorem fl9_9 : SS.bxor z9 ef9 = y1 := by decide
theorem fl9_10 : SS.bxor z10 ef9 = y2 := by decide
theorem fl9_11 : SS.bxor z11 ef9 = y3 := by decide
theorem fl9_12 : SS.bxor z12 ef9 = y4 := by decide
theorem fl9_13 : SS.bxor z13 ef9 = y5 := by decide
theorem fl9_14 : SS.bxor z14 ef9 = y6 := by decide
theorem fl9_15 : SS.bxor z15 ef9 = y7 := by decide
theorem sg9_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg9_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg9_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg9_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg9_w0_12 : SS.bdot w0 z12 = false := by decide
theorem sg9_w0_13 : SS.bdot w0 z13 = false := by decide
theorem sg9_w0_14 : SS.bdot w0 z14 = false := by decide
theorem sg9_w0_15 : SS.bdot w0 z15 = false := by decide
theorem sg9_w3_8 : SS.bdot w3 z8 = false := by decide
theorem sg9_w3_9 : SS.bdot w3 z9 = false := by decide
theorem sg9_w3_10 : SS.bdot w3 z10 = true := by decide
theorem sg9_w3_11 : SS.bdot w3 z11 = true := by decide
theorem sg9_w3_12 : SS.bdot w3 z12 = true := by decide
theorem sg9_w3_13 : SS.bdot w3 z13 = true := by decide
theorem sg9_w3_14 : SS.bdot w3 z14 = false := by decide
theorem sg9_w3_15 : SS.bdot w3 z15 = false := by decide
theorem sg9_w4_8 : SS.bdot w4 z8 = false := by decide
theorem sg9_w4_9 : SS.bdot w4 z9 = false := by decide
theorem sg9_w4_10 : SS.bdot w4 z10 = true := by decide
theorem sg9_w4_11 : SS.bdot w4 z11 = true := by decide
theorem sg9_w4_12 : SS.bdot w4 z12 = false := by decide
theorem sg9_w4_13 : SS.bdot w4 z13 = false := by decide
theorem sg9_w4_14 : SS.bdot w4 z14 = true := by decide
theorem sg9_w4_15 : SS.bdot w4 z15 = true := by decide
theorem sg9_w5_8 : SS.bdot w5 z8 = false := by decide
theorem sg9_w5_9 : SS.bdot w5 z9 = false := by decide
theorem sg9_w5_10 : SS.bdot w5 z10 = false := by decide
theorem sg9_w5_11 : SS.bdot w5 z11 = false := by decide
theorem sg9_w5_12 : SS.bdot w5 z12 = true := by decide
theorem sg9_w5_13 : SS.bdot w5 z13 = true := by decide
theorem sg9_w5_14 : SS.bdot w5 z14 = true := by decide
theorem sg9_w5_15 : SS.bdot w5 z15 = true := by decide
theorem incidence10 :
    S1.filter (fun y => SS.bxor y ef10 ∈ S0) = {z0, z1, z2, z3, z4, z5, z6, z7} := by decide
theorem fl10_0 : SS.bxor z0 ef10 = y8 := by decide
theorem fl10_1 : SS.bxor z1 ef10 = y9 := by decide
theorem fl10_2 : SS.bxor z2 ef10 = y10 := by decide
theorem fl10_3 : SS.bxor z3 ef10 = y11 := by decide
theorem fl10_4 : SS.bxor z4 ef10 = y12 := by decide
theorem fl10_5 : SS.bxor z5 ef10 = y13 := by decide
theorem fl10_6 : SS.bxor z6 ef10 = y14 := by decide
theorem fl10_7 : SS.bxor z7 ef10 = y15 := by decide
theorem sg10_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg10_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg10_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg10_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg10_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg10_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg10_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg10_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg10_w1_0 : SS.bdot w1 z0 = false := by decide
theorem sg10_w1_1 : SS.bdot w1 z1 = true := by decide
theorem sg10_w1_2 : SS.bdot w1 z2 = false := by decide
theorem sg10_w1_3 : SS.bdot w1 z3 = true := by decide
theorem sg10_w1_4 : SS.bdot w1 z4 = false := by decide
theorem sg10_w1_5 : SS.bdot w1 z5 = true := by decide
theorem sg10_w1_6 : SS.bdot w1 z6 = true := by decide
theorem sg10_w1_7 : SS.bdot w1 z7 = false := by decide
theorem incidence11 :
    S1.filter (fun y => SS.bxor y ef11 ∈ S0) = {z0, z1, z2, z3, z4, z5, z6, z7} := by decide
theorem fl11_0 : SS.bxor z0 ef11 = y9 := by decide
theorem fl11_1 : SS.bxor z1 ef11 = y8 := by decide
theorem fl11_2 : SS.bxor z2 ef11 = y11 := by decide
theorem fl11_3 : SS.bxor z3 ef11 = y10 := by decide
theorem fl11_4 : SS.bxor z4 ef11 = y13 := by decide
theorem fl11_5 : SS.bxor z5 ef11 = y12 := by decide
theorem fl11_6 : SS.bxor z6 ef11 = y15 := by decide
theorem fl11_7 : SS.bxor z7 ef11 = y14 := by decide
theorem sg11_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg11_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg11_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg11_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg11_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg11_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg11_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg11_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg11_w2_0 : SS.bdot w2 z0 = false := by decide
theorem sg11_w2_1 : SS.bdot w2 z1 = true := by decide
theorem sg11_w2_2 : SS.bdot w2 z2 = false := by decide
theorem sg11_w2_3 : SS.bdot w2 z3 = true := by decide
theorem sg11_w2_4 : SS.bdot w2 z4 = false := by decide
theorem sg11_w2_5 : SS.bdot w2 z5 = true := by decide
theorem sg11_w2_6 : SS.bdot w2 z6 = false := by decide
theorem sg11_w2_7 : SS.bdot w2 z7 = true := by decide

theorem ex0_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w0 = star (c y0) * d z0 + star (c y1) * d z1 + star (c y6) * d z6 + star (c y7) * d z7 + star (c y10) * d z10 + star (c y11) * d z11 + star (c y12) * d z12 + star (c y13) * d z13 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_0, fl0_1, fl0_6, fl0_7, fl0_10, fl0_11, fl0_12, fl0_13]
  simp only [sg0_w0_0, sg0_w0_1, sg0_w0_6, sg0_w0_7, sg0_w0_10, sg0_w0_11, sg0_w0_12, sg0_w0_13, SixQubit.signMul_false]
  try ring

theorem ex0_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w4 = star (c y0) * d z0 + star (c y1) * d z1 - star (c y6) * d z6 - star (c y7) * d z7 - star (c y10) * d z10 - star (c y11) * d z11 + star (c y12) * d z12 + star (c y13) * d z13 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_0, fl0_1, fl0_6, fl0_7, fl0_10, fl0_11, fl0_12, fl0_13]
  simp only [sg0_w4_0, sg0_w4_1, sg0_w4_6, sg0_w4_7, sg0_w4_10, sg0_w4_11, sg0_w4_12, sg0_w4_13, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex0_w5 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w5 = star (c y0) * d z0 + star (c y1) * d z1 - star (c y6) * d z6 - star (c y7) * d z7 + star (c y10) * d z10 + star (c y11) * d z11 - star (c y12) * d z12 - star (c y13) * d z13 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_0, fl0_1, fl0_6, fl0_7, fl0_10, fl0_11, fl0_12, fl0_13]
  simp only [sg0_w5_0, sg0_w5_1, sg0_w5_6, sg0_w5_7, sg0_w5_10, sg0_w5_11, sg0_w5_12, sg0_w5_13, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex0_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w6 = star (c y0) * d z0 + star (c y1) * d z1 + star (c y6) * d z6 + star (c y7) * d z7 - star (c y10) * d z10 - star (c y11) * d z11 - star (c y12) * d z12 - star (c y13) * d z13 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_0, fl0_1, fl0_6, fl0_7, fl0_10, fl0_11, fl0_12, fl0_13]
  simp only [sg0_w6_0, sg0_w6_1, sg0_w6_6, sg0_w6_7, sg0_w6_10, sg0_w6_11, sg0_w6_12, sg0_w6_13, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex1_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w0 = star (c y2) * d z2 + star (c y3) * d z3 + star (c y4) * d z4 + star (c y5) * d z5 + star (c y8) * d z8 + star (c y9) * d z9 + star (c y14) * d z14 + star (c y15) * d z15 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_2, fl1_3, fl1_4, fl1_5, fl1_8, fl1_9, fl1_14, fl1_15]
  simp only [sg1_w0_2, sg1_w0_3, sg1_w0_4, sg1_w0_5, sg1_w0_8, sg1_w0_9, sg1_w0_14, sg1_w0_15, SixQubit.signMul_false]
  try ring

theorem ex1_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w1 = star (c y2) * d z2 - star (c y3) * d z3 + star (c y4) * d z4 - star (c y5) * d z5 + star (c y8) * d z8 - star (c y9) * d z9 - star (c y14) * d z14 + star (c y15) * d z15 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_2, fl1_3, fl1_4, fl1_5, fl1_8, fl1_9, fl1_14, fl1_15]
  simp only [sg1_w1_2, sg1_w1_3, sg1_w1_4, sg1_w1_5, sg1_w1_8, sg1_w1_9, sg1_w1_14, sg1_w1_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex2_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w0 = star (c y3) * d z2 + star (c y2) * d z3 + star (c y5) * d z4 + star (c y4) * d z5 + star (c y9) * d z8 + star (c y8) * d z9 + star (c y15) * d z14 + star (c y14) * d z15 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_2, fl2_3, fl2_4, fl2_5, fl2_8, fl2_9, fl2_14, fl2_15]
  simp only [sg2_w0_2, sg2_w0_3, sg2_w0_4, sg2_w0_5, sg2_w0_8, sg2_w0_9, sg2_w0_14, sg2_w0_15, SixQubit.signMul_false]
  try ring

theorem ex2_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w2 = star (c y3) * d z2 - star (c y2) * d z3 + star (c y5) * d z4 - star (c y4) * d z5 + star (c y9) * d z8 - star (c y8) * d z9 + star (c y15) * d z14 - star (c y14) * d z15 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_2, fl2_3, fl2_4, fl2_5, fl2_8, fl2_9, fl2_14, fl2_15]
  simp only [sg2_w2_2, sg2_w2_3, sg2_w2_4, sg2_w2_5, sg2_w2_8, sg2_w2_9, sg2_w2_14, sg2_w2_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex3_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w0 = star (c y0) * d z2 + star (c y1) * d z3 + star (c y4) * d z6 + star (c y5) * d z7 + star (c y8) * d z10 + star (c y9) * d z11 + star (c y12) * d z14 + star (c y13) * d z15 := by
  unfold offSum
  rw [incidence3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl3_2, fl3_3, fl3_6, fl3_7, fl3_10, fl3_11, fl3_14, fl3_15]
  simp only [sg3_w0_2, sg3_w0_3, sg3_w0_6, sg3_w0_7, sg3_w0_10, sg3_w0_11, sg3_w0_14, sg3_w0_15, SixQubit.signMul_false]
  try ring

theorem ex3_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w3 = star (c y0) * d z2 + star (c y1) * d z3 - star (c y4) * d z6 - star (c y5) * d z7 - star (c y8) * d z10 - star (c y9) * d z11 + star (c y12) * d z14 + star (c y13) * d z15 := by
  unfold offSum
  rw [incidence3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl3_2, fl3_3, fl3_6, fl3_7, fl3_10, fl3_11, fl3_14, fl3_15]
  simp only [sg3_w3_2, sg3_w3_3, sg3_w3_6, sg3_w3_7, sg3_w3_10, sg3_w3_11, sg3_w3_14, sg3_w3_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex3_w5 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w5 = star (c y0) * d z2 + star (c y1) * d z3 - star (c y4) * d z6 - star (c y5) * d z7 + star (c y8) * d z10 + star (c y9) * d z11 - star (c y12) * d z14 - star (c y13) * d z15 := by
  unfold offSum
  rw [incidence3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl3_2, fl3_3, fl3_6, fl3_7, fl3_10, fl3_11, fl3_14, fl3_15]
  simp only [sg3_w5_2, sg3_w5_3, sg3_w5_6, sg3_w5_7, sg3_w5_10, sg3_w5_11, sg3_w5_14, sg3_w5_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex3_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w6 = star (c y0) * d z2 + star (c y1) * d z3 + star (c y4) * d z6 + star (c y5) * d z7 - star (c y8) * d z10 - star (c y9) * d z11 - star (c y12) * d z14 - star (c y13) * d z15 := by
  unfold offSum
  rw [incidence3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl3_2, fl3_3, fl3_6, fl3_7, fl3_10, fl3_11, fl3_14, fl3_15]
  simp only [sg3_w6_2, sg3_w6_3, sg3_w6_6, sg3_w6_7, sg3_w6_10, sg3_w6_11, sg3_w6_14, sg3_w6_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex4_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w0 = star (c y2) * d z0 + star (c y3) * d z1 + star (c y6) * d z4 + star (c y7) * d z5 + star (c y10) * d z8 + star (c y11) * d z9 + star (c y14) * d z12 + star (c y15) * d z13 := by
  unfold offSum
  rw [incidence4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl4_0, fl4_1, fl4_4, fl4_5, fl4_8, fl4_9, fl4_12, fl4_13]
  simp only [sg4_w0_0, sg4_w0_1, sg4_w0_4, sg4_w0_5, sg4_w0_8, sg4_w0_9, sg4_w0_12, sg4_w0_13, SixQubit.signMul_false]
  try ring

theorem ex4_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w1 = star (c y2) * d z0 - star (c y3) * d z1 + star (c y6) * d z4 - star (c y7) * d z5 + star (c y10) * d z8 - star (c y11) * d z9 - star (c y14) * d z12 + star (c y15) * d z13 := by
  unfold offSum
  rw [incidence4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl4_0, fl4_1, fl4_4, fl4_5, fl4_8, fl4_9, fl4_12, fl4_13]
  simp only [sg4_w1_0, sg4_w1_1, sg4_w1_4, sg4_w1_5, sg4_w1_8, sg4_w1_9, sg4_w1_12, sg4_w1_13, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex5_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef5 w0 = star (c y3) * d z0 + star (c y2) * d z1 + star (c y7) * d z4 + star (c y6) * d z5 + star (c y11) * d z8 + star (c y10) * d z9 + star (c y15) * d z12 + star (c y14) * d z13 := by
  unfold offSum
  rw [incidence5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl5_0, fl5_1, fl5_4, fl5_5, fl5_8, fl5_9, fl5_12, fl5_13]
  simp only [sg5_w0_0, sg5_w0_1, sg5_w0_4, sg5_w0_5, sg5_w0_8, sg5_w0_9, sg5_w0_12, sg5_w0_13, SixQubit.signMul_false]
  try ring

theorem ex5_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef5 w2 = star (c y3) * d z0 - star (c y2) * d z1 + star (c y7) * d z4 - star (c y6) * d z5 + star (c y11) * d z8 - star (c y10) * d z9 + star (c y15) * d z12 - star (c y14) * d z13 := by
  unfold offSum
  rw [incidence5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl5_0, fl5_1, fl5_4, fl5_5, fl5_8, fl5_9, fl5_12, fl5_13]
  simp only [sg5_w2_0, sg5_w2_1, sg5_w2_4, sg5_w2_5, sg5_w2_8, sg5_w2_9, sg5_w2_12, sg5_w2_13, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex6_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w0 = star (c y0) * d z4 + star (c y1) * d z5 + star (c y2) * d z6 + star (c y3) * d z7 + star (c y8) * d z12 + star (c y9) * d z13 + star (c y10) * d z14 + star (c y11) * d z15 := by
  unfold offSum
  rw [incidence6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl6_4, fl6_5, fl6_6, fl6_7, fl6_12, fl6_13, fl6_14, fl6_15]
  simp only [sg6_w0_4, sg6_w0_5, sg6_w0_6, sg6_w0_7, sg6_w0_12, sg6_w0_13, sg6_w0_14, sg6_w0_15, SixQubit.signMul_false]
  try ring

theorem ex6_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w3 = star (c y0) * d z4 + star (c y1) * d z5 - star (c y2) * d z6 - star (c y3) * d z7 - star (c y8) * d z12 - star (c y9) * d z13 + star (c y10) * d z14 + star (c y11) * d z15 := by
  unfold offSum
  rw [incidence6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl6_4, fl6_5, fl6_6, fl6_7, fl6_12, fl6_13, fl6_14, fl6_15]
  simp only [sg6_w3_4, sg6_w3_5, sg6_w3_6, sg6_w3_7, sg6_w3_12, sg6_w3_13, sg6_w3_14, sg6_w3_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex6_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w4 = star (c y0) * d z4 + star (c y1) * d z5 - star (c y2) * d z6 - star (c y3) * d z7 + star (c y8) * d z12 + star (c y9) * d z13 - star (c y10) * d z14 - star (c y11) * d z15 := by
  unfold offSum
  rw [incidence6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl6_4, fl6_5, fl6_6, fl6_7, fl6_12, fl6_13, fl6_14, fl6_15]
  simp only [sg6_w4_4, sg6_w4_5, sg6_w4_6, sg6_w4_7, sg6_w4_12, sg6_w4_13, sg6_w4_14, sg6_w4_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex6_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w6 = star (c y0) * d z4 + star (c y1) * d z5 + star (c y2) * d z6 + star (c y3) * d z7 - star (c y8) * d z12 - star (c y9) * d z13 - star (c y10) * d z14 - star (c y11) * d z15 := by
  unfold offSum
  rw [incidence6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl6_4, fl6_5, fl6_6, fl6_7, fl6_12, fl6_13, fl6_14, fl6_15]
  simp only [sg6_w6_4, sg6_w6_5, sg6_w6_6, sg6_w6_7, sg6_w6_12, sg6_w6_13, sg6_w6_14, sg6_w6_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex7_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef7 w0 = star (c y4) * d z0 + star (c y5) * d z1 + star (c y6) * d z2 + star (c y7) * d z3 + star (c y12) * d z8 + star (c y13) * d z9 + star (c y14) * d z10 + star (c y15) * d z11 := by
  unfold offSum
  rw [incidence7]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl7_0, fl7_1, fl7_2, fl7_3, fl7_8, fl7_9, fl7_10, fl7_11]
  simp only [sg7_w0_0, sg7_w0_1, sg7_w0_2, sg7_w0_3, sg7_w0_8, sg7_w0_9, sg7_w0_10, sg7_w0_11, SixQubit.signMul_false]
  try ring

theorem ex7_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef7 w1 = star (c y4) * d z0 - star (c y5) * d z1 + star (c y6) * d z2 - star (c y7) * d z3 + star (c y12) * d z8 - star (c y13) * d z9 - star (c y14) * d z10 + star (c y15) * d z11 := by
  unfold offSum
  rw [incidence7]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl7_0, fl7_1, fl7_2, fl7_3, fl7_8, fl7_9, fl7_10, fl7_11]
  simp only [sg7_w1_0, sg7_w1_1, sg7_w1_2, sg7_w1_3, sg7_w1_8, sg7_w1_9, sg7_w1_10, sg7_w1_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex8_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef8 w0 = star (c y5) * d z0 + star (c y4) * d z1 + star (c y7) * d z2 + star (c y6) * d z3 + star (c y13) * d z8 + star (c y12) * d z9 + star (c y15) * d z10 + star (c y14) * d z11 := by
  unfold offSum
  rw [incidence8]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl8_0, fl8_1, fl8_2, fl8_3, fl8_8, fl8_9, fl8_10, fl8_11]
  simp only [sg8_w0_0, sg8_w0_1, sg8_w0_2, sg8_w0_3, sg8_w0_8, sg8_w0_9, sg8_w0_10, sg8_w0_11, SixQubit.signMul_false]
  try ring

theorem ex8_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef8 w2 = star (c y5) * d z0 - star (c y4) * d z1 + star (c y7) * d z2 - star (c y6) * d z3 + star (c y13) * d z8 - star (c y12) * d z9 + star (c y15) * d z10 - star (c y14) * d z11 := by
  unfold offSum
  rw [incidence8]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl8_0, fl8_1, fl8_2, fl8_3, fl8_8, fl8_9, fl8_10, fl8_11]
  simp only [sg8_w2_0, sg8_w2_1, sg8_w2_2, sg8_w2_3, sg8_w2_8, sg8_w2_9, sg8_w2_10, sg8_w2_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex9_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef9 w0 = star (c y0) * d z8 + star (c y1) * d z9 + star (c y2) * d z10 + star (c y3) * d z11 + star (c y4) * d z12 + star (c y5) * d z13 + star (c y6) * d z14 + star (c y7) * d z15 := by
  unfold offSum
  rw [incidence9]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl9_8, fl9_9, fl9_10, fl9_11, fl9_12, fl9_13, fl9_14, fl9_15]
  simp only [sg9_w0_8, sg9_w0_9, sg9_w0_10, sg9_w0_11, sg9_w0_12, sg9_w0_13, sg9_w0_14, sg9_w0_15, SixQubit.signMul_false]
  try ring

theorem ex9_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef9 w3 = star (c y0) * d z8 + star (c y1) * d z9 - star (c y2) * d z10 - star (c y3) * d z11 - star (c y4) * d z12 - star (c y5) * d z13 + star (c y6) * d z14 + star (c y7) * d z15 := by
  unfold offSum
  rw [incidence9]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl9_8, fl9_9, fl9_10, fl9_11, fl9_12, fl9_13, fl9_14, fl9_15]
  simp only [sg9_w3_8, sg9_w3_9, sg9_w3_10, sg9_w3_11, sg9_w3_12, sg9_w3_13, sg9_w3_14, sg9_w3_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex9_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef9 w4 = star (c y0) * d z8 + star (c y1) * d z9 - star (c y2) * d z10 - star (c y3) * d z11 + star (c y4) * d z12 + star (c y5) * d z13 - star (c y6) * d z14 - star (c y7) * d z15 := by
  unfold offSum
  rw [incidence9]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl9_8, fl9_9, fl9_10, fl9_11, fl9_12, fl9_13, fl9_14, fl9_15]
  simp only [sg9_w4_8, sg9_w4_9, sg9_w4_10, sg9_w4_11, sg9_w4_12, sg9_w4_13, sg9_w4_14, sg9_w4_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex9_w5 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef9 w5 = star (c y0) * d z8 + star (c y1) * d z9 + star (c y2) * d z10 + star (c y3) * d z11 - star (c y4) * d z12 - star (c y5) * d z13 - star (c y6) * d z14 - star (c y7) * d z15 := by
  unfold offSum
  rw [incidence9]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl9_8, fl9_9, fl9_10, fl9_11, fl9_12, fl9_13, fl9_14, fl9_15]
  simp only [sg9_w5_8, sg9_w5_9, sg9_w5_10, sg9_w5_11, sg9_w5_12, sg9_w5_13, sg9_w5_14, sg9_w5_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex10_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef10 w0 = star (c y8) * d z0 + star (c y9) * d z1 + star (c y10) * d z2 + star (c y11) * d z3 + star (c y12) * d z4 + star (c y13) * d z5 + star (c y14) * d z6 + star (c y15) * d z7 := by
  unfold offSum
  rw [incidence10]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl10_0, fl10_1, fl10_2, fl10_3, fl10_4, fl10_5, fl10_6, fl10_7]
  simp only [sg10_w0_0, sg10_w0_1, sg10_w0_2, sg10_w0_3, sg10_w0_4, sg10_w0_5, sg10_w0_6, sg10_w0_7, SixQubit.signMul_false]
  try ring

theorem ex10_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef10 w1 = star (c y8) * d z0 - star (c y9) * d z1 + star (c y10) * d z2 - star (c y11) * d z3 + star (c y12) * d z4 - star (c y13) * d z5 - star (c y14) * d z6 + star (c y15) * d z7 := by
  unfold offSum
  rw [incidence10]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl10_0, fl10_1, fl10_2, fl10_3, fl10_4, fl10_5, fl10_6, fl10_7]
  simp only [sg10_w1_0, sg10_w1_1, sg10_w1_2, sg10_w1_3, sg10_w1_4, sg10_w1_5, sg10_w1_6, sg10_w1_7, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex11_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef11 w0 = star (c y9) * d z0 + star (c y8) * d z1 + star (c y11) * d z2 + star (c y10) * d z3 + star (c y13) * d z4 + star (c y12) * d z5 + star (c y15) * d z6 + star (c y14) * d z7 := by
  unfold offSum
  rw [incidence11]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl11_0, fl11_1, fl11_2, fl11_3, fl11_4, fl11_5, fl11_6, fl11_7]
  simp only [sg11_w0_0, sg11_w0_1, sg11_w0_2, sg11_w0_3, sg11_w0_4, sg11_w0_5, sg11_w0_6, sg11_w0_7, SixQubit.signMul_false]
  try ring

theorem ex11_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef11 w2 = star (c y9) * d z0 - star (c y8) * d z1 + star (c y11) * d z2 - star (c y10) * d z3 + star (c y13) * d z4 - star (c y12) * d z5 + star (c y15) * d z6 - star (c y14) * d z7 := by
  unfold offSum
  rw [incidence11]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl11_0, fl11_1, fl11_2, fl11_3, fl11_4, fl11_5, fl11_6, fl11_7]
  simp only [sg11_w2_0, sg11_w2_1, sg11_w2_2, sg11_w2_3, sg11_w2_4, sg11_w2_5, sg11_w2_6, sg11_w2_7, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring


/-! ## The moment system -/

/-- The two normalizations and the moment equalities, with every probability
nonnegative. -/
structure MomentSystem (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real) : Prop where
  n0 : q0 + q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 + q9 + q10 + q11 + q12 + q13 + q14 + q15 = 1
  n1 : r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15 = 1
  m1 : q8 + q9 + q10 + q11 + q12 + q13 + q14 + q15 = r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15
  m2 : q4 + q5 + q6 + q7 + q12 + q13 + q14 + q15 = r4 + r5 + r6 + r7 + r12 + r13 + r14 + r15
  m3 : q2 + q3 + q6 + q7 + q10 + q11 + q14 + q15 = r2 + r3 + r6 + r7 + r10 + r11 + r14 + r15
  m4 : q2 + q3 + q4 + q5 + q8 + q9 + q14 + q15 = r0 + r1 + r6 + r7 + r10 + r11 + r12 + r13
  m5 : q1 + q3 + q5 + q7 + q9 + q11 + q13 + q15 = r1 + r3 + r5 + r7 + r9 + r11 + r13 + r15
  m6 : q1 + q2 + q4 + q6 + q8 + q10 + q12 + q15 = r1 + r3 + r5 + r6 + r9 + r10 + r12 + r14
  c12 : q12 + q13 + q14 + q15 = r12 + r13 + r14 + r15
  c13 : q10 + q11 + q14 + q15 = r10 + r11 + r14 + r15
  c14 : q8 + q9 + q14 + q15 = r10 + r11 + r12 + r13
  c15 : q9 + q11 + q13 + q15 = r9 + r11 + r13 + r15
  c16 : q8 + q10 + q12 + q15 = r9 + r10 + r12 + r14
  c23 : q6 + q7 + q14 + q15 = r6 + r7 + r14 + r15
  c24 : q4 + q5 + q14 + q15 = r6 + r7 + r12 + r13
  c25 : q5 + q7 + q13 + q15 = r5 + r7 + r13 + r15
  c26 : q4 + q6 + q12 + q15 = r5 + r6 + r12 + r14
  c34 : q2 + q3 + q14 + q15 = r6 + r7 + r10 + r11
  c35 : q3 + q7 + q11 + q15 = r3 + r7 + r11 + r15
  c36 : q2 + q6 + q10 + q15 = r3 + r6 + r10 + r14
  c45 : q3 + q5 + q9 + q15 = r1 + r7 + r11 + r13
  c46 : q2 + q4 + q8 + q15 = r1 + r6 + r10 + r12
  c56 : q1 + q15 = r1 + r3 + r5 + r9

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

/-- The four top pairs carrying edges hold three quarters of the weight. -/
theorem mq {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    r10 + r11 + r12 + r13 + r14 + r15 + r6 + r7 - 3/4 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  linear_combination (3/4) * n1 + (3/4) * m1 + (3/4) * m2 + (3/4) * m3 + (3/4) * m4 + (-1) * m5 + (-1) * m6 + (-1/2) * c12 + (-1/2) * c13 + (-1/2) * c14 + (-1/2) * c23 + (-1/2) * c24 + (-1/2) * c34 + (2) * c56

/-- Their pair differences cancel. -/
theorem me {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    r10 - r11 + r12 - r13 + r14 - r15 + r6 - r7 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  linear_combination (-2) * m5 + (2) * m6 + (1) * c15 + (-1) * c16 + (1) * c25 + (-1) * c26 + (1) * c35 + (-1) * c36 + (1) * c45 + (-1) * c46

/-- The pinned bottom pair holds a quarter. -/
theorem mn7 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    q14 + q15 - 1/4 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  linear_combination (1/4) * n1 + (1/4) * m1 + (1/4) * m2 + (1/4) * m3 + (1/4) * m4 + (-1/2) * m5 + (-1/2) * m6 + (1) * c56

/-- Bottom pair 1 sits on edge {3,5}. -/
theorem mc1 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    q2 + q3 - r10 - r11 - r6 - r7 + 1/4 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  linear_combination (-1/4) * n1 + (-1/4) * m1 + (-1/4) * m2 + (-1/4) * m3 + (-1/4) * m4 + (1/2) * m5 + (1/2) * m6 + (1) * c34 + (-1) * c56

/-- Bottom pair 2 sits on edge {3,6}. -/
theorem mc2 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    q4 + q5 - r12 - r13 - r6 - r7 + 1/4 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  linear_combination (-1/4) * n1 + (-1/4) * m1 + (-1/4) * m2 + (-1/4) * m3 + (-1/4) * m4 + (1/2) * m5 + (1/2) * m6 + (1) * c24 + (-1) * c56

/-- Bottom pair 3 sits on edge {3,7}. -/
theorem mc3 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    q6 + q7 - r14 - r15 - r6 - r7 + 1/4 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  linear_combination (-1/4) * n1 + (-1/4) * m1 + (-1/4) * m2 + (-1/4) * m3 + (-1/4) * m4 + (1/2) * m5 + (1/2) * m6 + (1) * c23 + (-1) * c56

/-- Bottom pair 4 sits on edge {5,6}. -/
theorem mc4 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    q8 + q9 - r10 - r11 - r12 - r13 + 1/4 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  linear_combination (-1/4) * n1 + (-1/4) * m1 + (-1/4) * m2 + (-1/4) * m3 + (-1/4) * m4 + (1/2) * m5 + (1/2) * m6 + (1) * c14 + (-1) * c56

/-- Bottom pair 5 sits on edge {5,7}. -/
theorem mc5 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    q10 + q11 - r10 - r11 - r14 - r15 + 1/4 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  linear_combination (-1/4) * n1 + (-1/4) * m1 + (-1/4) * m2 + (-1/4) * m3 + (-1/4) * m4 + (1/2) * m5 + (1/2) * m6 + (1) * c13 + (-1) * c56

/-- Bottom pair 6 sits on edge {6,7}. -/
theorem mc6 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    q12 + q13 - r12 - r13 - r14 - r15 + 1/4 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  linear_combination (-1/4) * n1 + (-1/4) * m1 + (-1/4) * m2 + (-1/4) * m3 + (-1/4) * m4 + (1/2) * m5 + (1/2) * m6 + (1) * c12 + (-1) * c56

/-- Top pair 3 and its partner 4 hold a quarter. -/
theorem mp3 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    r6 + r7 + r8 + r9 - 1/4 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  linear_combination (1/4) * n1 + (-3/4) * m1 + (1/4) * m2 + (1/4) * m3 + (1/4) * m4 + (1/2) * c12 + (1/2) * c13 + (1/2) * c14 + (-1/2) * c23 + (-1/2) * c24 + (-1/2) * c34

/-- Top pair 5 and its partner 2 hold a quarter. -/
theorem mp5 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    r10 + r11 + r4 + r5 - 1/4 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  linear_combination (1/4) * n1 + (1/4) * m1 + (-3/4) * m2 + (1/4) * m3 + (1/4) * m4 + (1/2) * c12 + (-1/2) * c13 + (-1/2) * c14 + (1/2) * c23 + (1/2) * c24 + (-1/2) * c34

/-- Top pair 6 and its partner 1 hold a quarter. -/
theorem mp6 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    r12 + r13 + r2 + r3 - 1/4 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  linear_combination (1/4) * n1 + (1/4) * m1 + (1/4) * m2 + (-3/4) * m3 + (1/4) * m4 + (-1/2) * c12 + (1/2) * c13 + (-1/2) * c14 + (1/2) * c23 + (-1/2) * c24 + (1/2) * c34

/-- Top pair 7 and its partner 0 hold a quarter. -/
theorem mp7 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    r0 + r1 + r14 + r15 - 1/4 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  linear_combination (1/4) * n1 + (1/4) * m1 + (1/4) * m2 + (1/4) * m3 + (-3/4) * m4 + (-1/2) * c12 + (-1/2) * c13 + (1/2) * c14 + (-1/2) * c23 + (1/2) * c24 + (1/2) * c34

/-! ## The orthogonality relations -/

/-- Bottom pair 1 is orthogonal to top pair 3. -/
theorem orth1_3 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef6 w0 = 0)
    (h1 : offSum c d ef6 w6 = 0)
    (h2 : offSum c d ef6 w4 = 0)
    (h3 : offSum c d ef6 w3 = 0)
    : star (c y2) * d z6 + star (c y3) * d z7 = 0 := by
  rw [ex6_w0] at h0
  rw [ex6_w6] at h1
  rw [ex6_w4] at h2
  rw [ex6_w3] at h3
  linear_combination (1/4 : ℂ) * h0 + (1/4 : ℂ) * h1 + (-1/4 : ℂ) * h2 + (-1/4 : ℂ) * h3

/-- Bottom pair 1 is orthogonal to top pair 5. -/
theorem orth1_5 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef9 w0 = 0)
    (h1 : offSum c d ef9 w5 = 0)
    (h2 : offSum c d ef9 w4 = 0)
    (h3 : offSum c d ef9 w3 = 0)
    : star (c y2) * d z10 + star (c y3) * d z11 = 0 := by
  rw [ex9_w0] at h0
  rw [ex9_w5] at h1
  rw [ex9_w4] at h2
  rw [ex9_w3] at h3
  linear_combination (1/4 : ℂ) * h0 + (1/4 : ℂ) * h1 + (-1/4 : ℂ) * h2 + (-1/4 : ℂ) * h3

/-- Bottom pair 2 is orthogonal to top pair 3. -/
theorem orth2_3 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef3 w0 = 0)
    (h1 : offSum c d ef3 w6 = 0)
    (h2 : offSum c d ef3 w5 = 0)
    (h3 : offSum c d ef3 w3 = 0)
    : star (c y4) * d z6 + star (c y5) * d z7 = 0 := by
  rw [ex3_w0] at h0
  rw [ex3_w6] at h1
  rw [ex3_w5] at h2
  rw [ex3_w3] at h3
  linear_combination (1/4 : ℂ) * h0 + (1/4 : ℂ) * h1 + (-1/4 : ℂ) * h2 + (-1/4 : ℂ) * h3

/-- Bottom pair 2 is orthogonal to top pair 6. -/
theorem orth2_6 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef9 w0 = 0)
    (h1 : offSum c d ef9 w5 = 0)
    (h2 : offSum c d ef9 w4 = 0)
    (h3 : offSum c d ef9 w3 = 0)
    : star (c y4) * d z12 + star (c y5) * d z13 = 0 := by
  rw [ex9_w0] at h0
  rw [ex9_w5] at h1
  rw [ex9_w4] at h2
  rw [ex9_w3] at h3
  linear_combination (1/4 : ℂ) * h0 + (-1/4 : ℂ) * h1 + (1/4 : ℂ) * h2 + (-1/4 : ℂ) * h3

/-- Bottom pair 3 is orthogonal to top pair 3. -/
theorem orth3_3 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef0 w0 = 0)
    (h1 : offSum c d ef0 w6 = 0)
    (h2 : offSum c d ef0 w5 = 0)
    (h3 : offSum c d ef0 w4 = 0)
    : star (c y6) * d z6 + star (c y7) * d z7 = 0 := by
  rw [ex0_w0] at h0
  rw [ex0_w6] at h1
  rw [ex0_w5] at h2
  rw [ex0_w4] at h3
  linear_combination (1/4 : ℂ) * h0 + (1/4 : ℂ) * h1 + (-1/4 : ℂ) * h2 + (-1/4 : ℂ) * h3

/-- Bottom pair 3 is orthogonal to top pair 7. -/
theorem orth3_7 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef9 w0 = 0)
    (h1 : offSum c d ef9 w5 = 0)
    (h2 : offSum c d ef9 w4 = 0)
    (h3 : offSum c d ef9 w3 = 0)
    : star (c y6) * d z14 + star (c y7) * d z15 = 0 := by
  rw [ex9_w0] at h0
  rw [ex9_w5] at h1
  rw [ex9_w4] at h2
  rw [ex9_w3] at h3
  linear_combination (1/4 : ℂ) * h0 + (-1/4 : ℂ) * h1 + (-1/4 : ℂ) * h2 + (1/4 : ℂ) * h3

/-- Bottom pair 4 is orthogonal to top pair 5. -/
theorem orth4_5 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef3 w0 = 0)
    (h1 : offSum c d ef3 w6 = 0)
    (h2 : offSum c d ef3 w5 = 0)
    (h3 : offSum c d ef3 w3 = 0)
    : star (c y8) * d z10 + star (c y9) * d z11 = 0 := by
  rw [ex3_w0] at h0
  rw [ex3_w6] at h1
  rw [ex3_w5] at h2
  rw [ex3_w3] at h3
  linear_combination (1/4 : ℂ) * h0 + (-1/4 : ℂ) * h1 + (1/4 : ℂ) * h2 + (-1/4 : ℂ) * h3

/-- Bottom pair 4 is orthogonal to top pair 6. -/
theorem orth4_6 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef6 w0 = 0)
    (h1 : offSum c d ef6 w6 = 0)
    (h2 : offSum c d ef6 w4 = 0)
    (h3 : offSum c d ef6 w3 = 0)
    : star (c y8) * d z12 + star (c y9) * d z13 = 0 := by
  rw [ex6_w0] at h0
  rw [ex6_w6] at h1
  rw [ex6_w4] at h2
  rw [ex6_w3] at h3
  linear_combination (1/4 : ℂ) * h0 + (-1/4 : ℂ) * h1 + (1/4 : ℂ) * h2 + (-1/4 : ℂ) * h3

/-- Bottom pair 5 is orthogonal to top pair 5. -/
theorem orth5_5 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef0 w0 = 0)
    (h1 : offSum c d ef0 w6 = 0)
    (h2 : offSum c d ef0 w5 = 0)
    (h3 : offSum c d ef0 w4 = 0)
    : star (c y10) * d z10 + star (c y11) * d z11 = 0 := by
  rw [ex0_w0] at h0
  rw [ex0_w6] at h1
  rw [ex0_w5] at h2
  rw [ex0_w4] at h3
  linear_combination (1/4 : ℂ) * h0 + (-1/4 : ℂ) * h1 + (1/4 : ℂ) * h2 + (-1/4 : ℂ) * h3

/-- Bottom pair 5 is orthogonal to top pair 7. -/
theorem orth5_7 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef6 w0 = 0)
    (h1 : offSum c d ef6 w6 = 0)
    (h2 : offSum c d ef6 w4 = 0)
    (h3 : offSum c d ef6 w3 = 0)
    : star (c y10) * d z14 + star (c y11) * d z15 = 0 := by
  rw [ex6_w0] at h0
  rw [ex6_w6] at h1
  rw [ex6_w4] at h2
  rw [ex6_w3] at h3
  linear_combination (1/4 : ℂ) * h0 + (-1/4 : ℂ) * h1 + (-1/4 : ℂ) * h2 + (1/4 : ℂ) * h3

/-- Bottom pair 6 is orthogonal to top pair 6. -/
theorem orth6_6 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef0 w0 = 0)
    (h1 : offSum c d ef0 w6 = 0)
    (h2 : offSum c d ef0 w5 = 0)
    (h3 : offSum c d ef0 w4 = 0)
    : star (c y12) * d z12 + star (c y13) * d z13 = 0 := by
  rw [ex0_w0] at h0
  rw [ex0_w6] at h1
  rw [ex0_w5] at h2
  rw [ex0_w4] at h3
  linear_combination (1/4 : ℂ) * h0 + (-1/4 : ℂ) * h1 + (-1/4 : ℂ) * h2 + (1/4 : ℂ) * h3

/-- Bottom pair 6 is orthogonal to top pair 7. -/
theorem orth6_7 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef3 w0 = 0)
    (h1 : offSum c d ef3 w6 = 0)
    (h2 : offSum c d ef3 w5 = 0)
    (h3 : offSum c d ef3 w3 = 0)
    : star (c y12) * d z14 + star (c y13) * d z15 = 0 := by
  rw [ex3_w0] at h0
  rw [ex3_w6] at h1
  rw [ex3_w5] at h2
  rw [ex3_w3] at h3
  linear_combination (1/4 : ℂ) * h0 + (-1/4 : ℂ) * h1 + (-1/4 : ℂ) * h2 + (1/4 : ℂ) * h3

/-! ## The Walsh combinations at the pinned pair -/

theorem wc3A (c d : SS.BitString 6 -> ℂ)
    (hA : offSum c d ef10 w0 = 0)
    (hB : offSum c d ef10 w1 = 0)
    : star (c y8) * d z0 + star (c y10) * d z2 + star (c y12) * d z4 + star (c y15) * d z7 = 0 := by
  rw [ex10_w0] at hA
  rw [ex10_w1] at hB
  linear_combination (1/2 : ℂ) * hA + (1/2 : ℂ) * hB

theorem wc3B (c d : SS.BitString 6 -> ℂ)
    (hA : offSum c d ef10 w0 = 0)
    (hB : offSum c d ef10 w1 = 0)
    : star (c y9) * d z1 + star (c y11) * d z3 + star (c y13) * d z5 + star (c y14) * d z6 = 0 := by
  rw [ex10_w0] at hA
  rw [ex10_w1] at hB
  linear_combination (1/2 : ℂ) * hA - (1/2 : ℂ) * hB

theorem wc3C (c d : SS.BitString 6 -> ℂ)
    (hA : offSum c d ef11 w0 = 0)
    (hB : offSum c d ef11 w2 = 0)
    : star (c y9) * d z0 + star (c y11) * d z2 + star (c y13) * d z4 + star (c y15) * d z6 = 0 := by
  rw [ex11_w0] at hA
  rw [ex11_w2] at hB
  linear_combination (1/2 : ℂ) * hA + (1/2 : ℂ) * hB

theorem wc3D (c d : SS.BitString 6 -> ℂ)
    (hA : offSum c d ef11 w0 = 0)
    (hB : offSum c d ef11 w2 = 0)
    : star (c y8) * d z1 + star (c y10) * d z3 + star (c y12) * d z5 + star (c y14) * d z7 = 0 := by
  rw [ex11_w0] at hA
  rw [ex11_w2] at hB
  linear_combination (1/2 : ℂ) * hA - (1/2 : ℂ) * hB

theorem wc5A (c d : SS.BitString 6 -> ℂ)
    (hA : offSum c d ef7 w0 = 0)
    (hB : offSum c d ef7 w1 = 0)
    : star (c y4) * d z0 + star (c y6) * d z2 + star (c y12) * d z8 + star (c y15) * d z11 = 0 := by
  rw [ex7_w0] at hA
  rw [ex7_w1] at hB
  linear_combination (1/2 : ℂ) * hA + (1/2 : ℂ) * hB

theorem wc5B (c d : SS.BitString 6 -> ℂ)
    (hA : offSum c d ef7 w0 = 0)
    (hB : offSum c d ef7 w1 = 0)
    : star (c y5) * d z1 + star (c y7) * d z3 + star (c y13) * d z9 + star (c y14) * d z10 = 0 := by
  rw [ex7_w0] at hA
  rw [ex7_w1] at hB
  linear_combination (1/2 : ℂ) * hA - (1/2 : ℂ) * hB

theorem wc5C (c d : SS.BitString 6 -> ℂ)
    (hA : offSum c d ef8 w0 = 0)
    (hB : offSum c d ef8 w2 = 0)
    : star (c y5) * d z0 + star (c y7) * d z2 + star (c y13) * d z8 + star (c y15) * d z10 = 0 := by
  rw [ex8_w0] at hA
  rw [ex8_w2] at hB
  linear_combination (1/2 : ℂ) * hA + (1/2 : ℂ) * hB

theorem wc5D (c d : SS.BitString 6 -> ℂ)
    (hA : offSum c d ef8 w0 = 0)
    (hB : offSum c d ef8 w2 = 0)
    : star (c y4) * d z1 + star (c y6) * d z3 + star (c y12) * d z9 + star (c y14) * d z11 = 0 := by
  rw [ex8_w0] at hA
  rw [ex8_w2] at hB
  linear_combination (1/2 : ℂ) * hA - (1/2 : ℂ) * hB

theorem wc6A (c d : SS.BitString 6 -> ℂ)
    (hA : offSum c d ef4 w0 = 0)
    (hB : offSum c d ef4 w1 = 0)
    : star (c y2) * d z0 + star (c y6) * d z4 + star (c y10) * d z8 + star (c y15) * d z13 = 0 := by
  rw [ex4_w0] at hA
  rw [ex4_w1] at hB
  linear_combination (1/2 : ℂ) * hA + (1/2 : ℂ) * hB

theorem wc6B (c d : SS.BitString 6 -> ℂ)
    (hA : offSum c d ef4 w0 = 0)
    (hB : offSum c d ef4 w1 = 0)
    : star (c y3) * d z1 + star (c y7) * d z5 + star (c y11) * d z9 + star (c y14) * d z12 = 0 := by
  rw [ex4_w0] at hA
  rw [ex4_w1] at hB
  linear_combination (1/2 : ℂ) * hA - (1/2 : ℂ) * hB

theorem wc6C (c d : SS.BitString 6 -> ℂ)
    (hA : offSum c d ef5 w0 = 0)
    (hB : offSum c d ef5 w2 = 0)
    : star (c y3) * d z0 + star (c y7) * d z4 + star (c y11) * d z8 + star (c y15) * d z12 = 0 := by
  rw [ex5_w0] at hA
  rw [ex5_w2] at hB
  linear_combination (1/2 : ℂ) * hA + (1/2 : ℂ) * hB

theorem wc6D (c d : SS.BitString 6 -> ℂ)
    (hA : offSum c d ef5 w0 = 0)
    (hB : offSum c d ef5 w2 = 0)
    : star (c y2) * d z1 + star (c y6) * d z5 + star (c y10) * d z9 + star (c y14) * d z13 = 0 := by
  rw [ex5_w0] at hA
  rw [ex5_w2] at hB
  linear_combination (1/2 : ℂ) * hA - (1/2 : ℂ) * hB

theorem wc7A (c d : SS.BitString 6 -> ℂ)
    (hA : offSum c d ef1 w0 = 0)
    (hB : offSum c d ef1 w1 = 0)
    : star (c y2) * d z2 + star (c y4) * d z4 + star (c y8) * d z8 + star (c y15) * d z15 = 0 := by
  rw [ex1_w0] at hA
  rw [ex1_w1] at hB
  linear_combination (1/2 : ℂ) * hA + (1/2 : ℂ) * hB

theorem wc7B (c d : SS.BitString 6 -> ℂ)
    (hA : offSum c d ef1 w0 = 0)
    (hB : offSum c d ef1 w1 = 0)
    : star (c y3) * d z3 + star (c y5) * d z5 + star (c y9) * d z9 + star (c y14) * d z14 = 0 := by
  rw [ex1_w0] at hA
  rw [ex1_w1] at hB
  linear_combination (1/2 : ℂ) * hA - (1/2 : ℂ) * hB

theorem wc7C (c d : SS.BitString 6 -> ℂ)
    (hA : offSum c d ef2 w0 = 0)
    (hB : offSum c d ef2 w2 = 0)
    : star (c y3) * d z2 + star (c y5) * d z4 + star (c y9) * d z8 + star (c y15) * d z14 = 0 := by
  rw [ex2_w0] at hA
  rw [ex2_w2] at hB
  linear_combination (1/2 : ℂ) * hA + (1/2 : ℂ) * hB

theorem wc7D (c d : SS.BitString 6 -> ℂ)
    (hA : offSum c d ef2 w0 = 0)
    (hB : offSum c d ef2 w2 = 0)
    : star (c y2) * d z3 + star (c y4) * d z5 + star (c y8) * d z9 + star (c y14) * d z15 = 0 := by
  rw [ex2_w0] at hA
  rw [ex2_w2] at hB
  linear_combination (1/2 : ℂ) * hA - (1/2 : ℂ) * hB


/-! ## The no-go -/

set_option maxHeartbeats 2000000 in
/-- Orbit 29 admits no six-qubit `((6,2,3))` code. -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11)) (Complex.normSq (c y12)) (Complex.normSq (c y13)) (Complex.normSq (c y14)) (Complex.normSq (c y15))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)) (Complex.normSq (d z12)) (Complex.normSq (d z13)) (Complex.normSq (d z14)) (Complex.normSq (d z15)))
    (E0_w0 : offSum c d ef0 w0 = 0)
    (E0_w4 : offSum c d ef0 w4 = 0)
    (E0_w5 : offSum c d ef0 w5 = 0)
    (E0_w6 : offSum c d ef0 w6 = 0)
    (E1_w0 : offSum c d ef1 w0 = 0)
    (E1_w1 : offSum c d ef1 w1 = 0)
    (E2_w0 : offSum c d ef2 w0 = 0)
    (E2_w2 : offSum c d ef2 w2 = 0)
    (E3_w0 : offSum c d ef3 w0 = 0)
    (E3_w3 : offSum c d ef3 w3 = 0)
    (E3_w5 : offSum c d ef3 w5 = 0)
    (E3_w6 : offSum c d ef3 w6 = 0)
    (E4_w0 : offSum c d ef4 w0 = 0)
    (E4_w1 : offSum c d ef4 w1 = 0)
    (E5_w0 : offSum c d ef5 w0 = 0)
    (E5_w2 : offSum c d ef5 w2 = 0)
    (E6_w0 : offSum c d ef6 w0 = 0)
    (E6_w3 : offSum c d ef6 w3 = 0)
    (E6_w4 : offSum c d ef6 w4 = 0)
    (E6_w6 : offSum c d ef6 w6 = 0)
    (E7_w0 : offSum c d ef7 w0 = 0)
    (E7_w1 : offSum c d ef7 w1 = 0)
    (E8_w0 : offSum c d ef8 w0 = 0)
    (E8_w2 : offSum c d ef8 w2 = 0)
    (E9_w0 : offSum c d ef9 w0 = 0)
    (E9_w3 : offSum c d ef9 w3 = 0)
    (E9_w4 : offSum c d ef9 w4 = 0)
    (E9_w5 : offSum c d ef9 w5 = 0)
    (E10_w0 : offSum c d ef10 w0 = 0)
    (E10_w1 : offSum c d ef10 w1 = 0)
    (E11_w0 : offSum c d ef11 w0 = 0)
    (E11_w2 : offSum c d ef11 w2 = 0)
    : False := by
  have n7 : c y14 * star (c y14) + c y15 * star (c y15) = 1/4 := by
    have hr : Complex.normSq (c y14) + Complex.normSq (c y15) = 1/4 := by have h := mn7 hm; linarith
    have hc := congrArg (fun x : Real => (x : ℂ)) hr
    push_cast at hc
    simp only [sq]
    linear_combination hc
  have nq3 : d z6 * star (d z6) + d z7 * star (d z7) = ((Complex.normSq (d z6) + Complex.normSq (d z7) : Real) : ℂ) := by
    simp only [sq]; push_cast; ring
  have nq5 : d z10 * star (d z10) + d z11 * star (d z11) = ((Complex.normSq (d z10) + Complex.normSq (d z11) : Real) : ℂ) := by
    simp only [sq]; push_cast; ring
  have nq6 : d z12 * star (d z12) + d z13 * star (d z13) = ((Complex.normSq (d z12) + Complex.normSq (d z13) : Real) : ℂ) := by
    simp only [sq]; push_cast; ring
  have nq7 : d z14 * star (d z14) + d z15 * star (d z15) = ((Complex.normSq (d z14) + Complex.normSq (d z15) : Real) : ℂ) := by
    simp only [sq]; push_cast; ring
  have nc1 : c y2 * star (c y2) + c y3 * star (c y3)
      = (((Complex.normSq (d z6) + Complex.normSq (d z7)) + (Complex.normSq (d z10) + Complex.normSq (d z11)) - 1/4 : Real) : ℂ) := by
    have hr : Complex.normSq (c y2) + Complex.normSq (c y3) = (Complex.normSq (d z6) + Complex.normSq (d z7)) + (Complex.normSq (d z10) + Complex.normSq (d z11)) - 1/4 := by
      have h := mc1 hm; linarith
    have hc := congrArg (fun x : Real => (x : ℂ)) hr
    push_cast at hc
    simp only [sq]
    push_cast
    linear_combination hc
  have nc2 : c y4 * star (c y4) + c y5 * star (c y5)
      = (((Complex.normSq (d z6) + Complex.normSq (d z7)) + (Complex.normSq (d z12) + Complex.normSq (d z13)) - 1/4 : Real) : ℂ) := by
    have hr : Complex.normSq (c y4) + Complex.normSq (c y5) = (Complex.normSq (d z6) + Complex.normSq (d z7)) + (Complex.normSq (d z12) + Complex.normSq (d z13)) - 1/4 := by
      have h := mc2 hm; linarith
    have hc := congrArg (fun x : Real => (x : ℂ)) hr
    push_cast at hc
    simp only [sq]
    push_cast
    linear_combination hc
  have nc3 : c y6 * star (c y6) + c y7 * star (c y7)
      = (((Complex.normSq (d z6) + Complex.normSq (d z7)) + (Complex.normSq (d z14) + Complex.normSq (d z15)) - 1/4 : Real) : ℂ) := by
    have hr : Complex.normSq (c y6) + Complex.normSq (c y7) = (Complex.normSq (d z6) + Complex.normSq (d z7)) + (Complex.normSq (d z14) + Complex.normSq (d z15)) - 1/4 := by
      have h := mc3 hm; linarith
    have hc := congrArg (fun x : Real => (x : ℂ)) hr
    push_cast at hc
    simp only [sq]
    push_cast
    linear_combination hc
  have nc4 : c y8 * star (c y8) + c y9 * star (c y9)
      = (((Complex.normSq (d z10) + Complex.normSq (d z11)) + (Complex.normSq (d z12) + Complex.normSq (d z13)) - 1/4 : Real) : ℂ) := by
    have hr : Complex.normSq (c y8) + Complex.normSq (c y9) = (Complex.normSq (d z10) + Complex.normSq (d z11)) + (Complex.normSq (d z12) + Complex.normSq (d z13)) - 1/4 := by
      have h := mc4 hm; linarith
    have hc := congrArg (fun x : Real => (x : ℂ)) hr
    push_cast at hc
    simp only [sq]
    push_cast
    linear_combination hc
  have nc5 : c y10 * star (c y10) + c y11 * star (c y11)
      = (((Complex.normSq (d z10) + Complex.normSq (d z11)) + (Complex.normSq (d z14) + Complex.normSq (d z15)) - 1/4 : Real) : ℂ) := by
    have hr : Complex.normSq (c y10) + Complex.normSq (c y11) = (Complex.normSq (d z10) + Complex.normSq (d z11)) + (Complex.normSq (d z14) + Complex.normSq (d z15)) - 1/4 := by
      have h := mc5 hm; linarith
    have hc := congrArg (fun x : Real => (x : ℂ)) hr
    push_cast at hc
    simp only [sq]
    push_cast
    linear_combination hc
  have nc6 : c y12 * star (c y12) + c y13 * star (c y13)
      = (((Complex.normSq (d z12) + Complex.normSq (d z13)) + (Complex.normSq (d z14) + Complex.normSq (d z15)) - 1/4 : Real) : ℂ) := by
    have hr : Complex.normSq (c y12) + Complex.normSq (c y13) = (Complex.normSq (d z12) + Complex.normSq (d z13)) + (Complex.normSq (d z14) + Complex.normSq (d z15)) - 1/4 := by
      have h := mc6 hm; linarith
    have hc := congrArg (fun x : Real => (x : ℂ)) hr
    push_cast at hc
    simp only [sq]
    push_cast
    linear_combination hc
  have qsum : (Complex.normSq (d z6) + Complex.normSq (d z7)) + (Complex.normSq (d z10) + Complex.normSq (d z11)) + (Complex.normSq (d z12) + Complex.normSq (d z13)) + (Complex.normSq (d z14) + Complex.normSq (d z15)) = 3/4 := by
    have h := mq hm; linarith
  have esum : (d z6 * star (d z6) - d z7 * star (d z7))
      + (d z10 * star (d z10) - d z11 * star (d z11))
      + (d z12 * star (d z12) - d z13 * star (d z13))
      + (d z14 * star (d z14) - d z15 * star (d z15))
      = 0 := by
    have hr : (Complex.normSq (d z6) - Complex.normSq (d z7)) + (Complex.normSq (d z10) - Complex.normSq (d z11)) + (Complex.normSq (d z12) - Complex.normSq (d z13)) + (Complex.normSq (d z14) - Complex.normSq (d z15)) = 0 := by have h := me hm; linarith
    have hc := congrArg (fun x : Real => (x : ℂ)) hr
    push_cast at hc
    simp only [sq]
    linear_combination hc
  have qle3 : (Complex.normSq (d z6) + Complex.normSq (d z7)) ≤ 1/4 := by
    have h := mp3 hm
    have h1 := Complex.normSq_nonneg (d z8)
    have h2 := Complex.normSq_nonneg (d z9)
    linarith
  have qle5 : (Complex.normSq (d z10) + Complex.normSq (d z11)) ≤ 1/4 := by
    have h := mp5 hm
    have h1 := Complex.normSq_nonneg (d z4)
    have h2 := Complex.normSq_nonneg (d z5)
    linarith
  have qle6 : (Complex.normSq (d z12) + Complex.normSq (d z13)) ≤ 1/4 := by
    have h := mp6 hm
    have h1 := Complex.normSq_nonneg (d z2)
    have h2 := Complex.normSq_nonneg (d z3)
    linarith
  have qle7 : (Complex.normSq (d z14) + Complex.normSq (d z15)) ≤ 1/4 := by
    have h := mp7 hm
    have h1 := Complex.normSq_nonneg (d z0)
    have h2 := Complex.normSq_nonneg (d z1)
    linarith
  exact SixQubit.Pair29.pair_contradiction
    (c y2) (c y3) (c y4) (c y5) (c y6) (c y7) (c y8) (c y9) (c y10) (c y11) (c y12) (c y13) (c y14) (c y15)
    (d z6) (d z7) ((Complex.normSq (d z6) + Complex.normSq (d z7))) (d z10) (d z11) ((Complex.normSq (d z10) + Complex.normSq (d z11))) (d z12) (d z13) ((Complex.normSq (d z12) + Complex.normSq (d z13))) (d z14) (d z15) ((Complex.normSq (d z14) + Complex.normSq (d z15)))
    (d z0) (d z1) (d z2) (d z3) (d z4) (d z5) (d z8) (d z9)
    n7 nq3 nq5 nq6 nq7
    nc1 nc2 nc3 nc4 nc5 nc6 qsum esum
    (orth1_3 c d E6_w0 E6_w6 E6_w4 E6_w3)
    (orth1_5 c d E9_w0 E9_w5 E9_w4 E9_w3)
    (orth2_3 c d E3_w0 E3_w6 E3_w5 E3_w3)
    (orth2_6 c d E9_w0 E9_w5 E9_w4 E9_w3)
    (orth3_3 c d E0_w0 E0_w6 E0_w5 E0_w4)
    (orth3_7 c d E9_w0 E9_w5 E9_w4 E9_w3)
    (orth4_5 c d E3_w0 E3_w6 E3_w5 E3_w3)
    (orth4_6 c d E6_w0 E6_w6 E6_w4 E6_w3)
    (orth5_5 c d E0_w0 E0_w6 E0_w5 E0_w4)
    (orth5_7 c d E6_w0 E6_w6 E6_w4 E6_w3)
    (orth6_6 c d E0_w0 E0_w6 E0_w5 E0_w4)
    (orth6_7 c d E3_w0 E3_w6 E3_w5 E3_w3)
    (wc3A c d E10_w0 E10_w1)
    (wc3B c d E10_w0 E10_w1)
    (wc3C c d E11_w0 E11_w2)
    (wc3D c d E11_w0 E11_w2)
    (wc5A c d E7_w0 E7_w1)
    (wc5B c d E7_w0 E7_w1)
    (wc5C c d E8_w0 E8_w2)
    (wc5D c d E8_w0 E8_w2)
    (wc6A c d E4_w0 E4_w1)
    (wc6B c d E4_w0 E4_w1)
    (wc6C c d E5_w0 E5_w2)
    (wc6D c d E5_w0 E5_w2)
    (wc7A c d E1_w0 E1_w1)
    (wc7B c d E1_w0 E1_w1)
    (wc7C c d E2_w0 E2_w2)
    (wc7D c d E2_w0 E2_w2)
    qle3 qle5 qle6 qle7

end

end SixQubit.Orbit29
