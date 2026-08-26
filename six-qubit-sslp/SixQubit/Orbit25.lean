import Mathlib

import SS.FullKL
import SixQubit.Common

/-!
# Six-qubit no-go for moment orbit 25: the diagonal layer

Orbit 25 of `six_qubit_sslp_v7.tex`: q = 4, angle vector
a = (0, 1, 1, 1, 1, 1), residues 0 and 1, closed in Section 15.

Every earlier orbit was closed with off-diagonal Knill-Laflamme conditions
alone.  This one cannot be: its phase ratios are globally consistent, but all
twenty-five cross relations carry sign `+1`, so no odd cycle exists.  What
closes it is the DIAGONAL condition, introduced here:

    <0_L| X^e Z^z |0_L>  =  <1_L| X^e Z^z |1_L>.

The bottom fiber is closed under flipping qubit one, so `X_1` has twelve
diagonal incidences on each side, pairing into six coherences per fiber.  With
`A` the anchor coherence `conj(c_0) c_6`, the off-diagonal relations give
`q_0 D_k = q_k A`, and the probabilities are pinned to `3/16` and `1/16`, so
`sum_k D_k = (8/3) A`; the phase-ratio links carry each top coherence back to a
bottom one with an overall minus sign.  The two surviving dressings of `X_1`
then force `A = 0`, against `normSq A = q_0 q_6 = 9/256`.

Everything computational is decided by the Lean kernel; `native_decide` is
not used.
-/

namespace SixQubit.Orbit25

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]

def y0 : SS.BitString 6 := bs false false false false false false  -- 000000
def y1 : SS.BitString 6 := bs false false true  true  true  true   -- 001111
def y2 : SS.BitString 6 := bs false true  false true  true  true   -- 010111
def y3 : SS.BitString 6 := bs false true  true  false true  true   -- 011011
def y4 : SS.BitString 6 := bs false true  true  true  false true   -- 011101
def y5 : SS.BitString 6 := bs false true  true  true  true  false  -- 011110
def y6 : SS.BitString 6 := bs true  false false false false false  -- 100000
def y7 : SS.BitString 6 := bs true  false true  true  true  true   -- 101111
def y8 : SS.BitString 6 := bs true  true  false true  true  true   -- 110111
def y9 : SS.BitString 6 := bs true  true  true  false true  true   -- 111011
def y10 : SS.BitString 6 := bs true  true  true  true  false true   -- 111101
def y11 : SS.BitString 6 := bs true  true  true  true  true  false  -- 111110

def z0 : SS.BitString 6 := bs false false false false false true   -- 000001
def z1 : SS.BitString 6 := bs false false false false true  false  -- 000010
def z2 : SS.BitString 6 := bs false false false true  false false  -- 000100
def z3 : SS.BitString 6 := bs false false true  false false false  -- 001000
def z4 : SS.BitString 6 := bs false true  false false false false  -- 010000
def z5 : SS.BitString 6 := bs false true  true  true  true  true   -- 011111
def z6 : SS.BitString 6 := bs true  false false false false true   -- 100001
def z7 : SS.BitString 6 := bs true  false false false true  false  -- 100010
def z8 : SS.BitString 6 := bs true  false false true  false false  -- 100100
def z9 : SS.BitString 6 := bs true  false true  false false false  -- 101000
def z10 : SS.BitString 6 := bs true  true  false false false false  -- 110000
def z11 : SS.BitString 6 := bs true  true  true  true  true  true   -- 111111

def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11}
def S1 : Finset (SS.BitString 6) := {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11}

def av : Fin 6 -> ZMod 4 := ![0, 1, 1, 1, 1, 1]

/-- Each support is exactly its residue fiber, decided over all 64 strings. -/
theorem S0_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 0) = S0 := by
  decide

theorem S1_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 1) = S1 := by
  decide

def ef0 : SS.BitString 6 := bs false false false false false true   -- mask 000001
def ef1 : SS.BitString 6 := bs false false false false true  false  -- mask 000010
def ef2 : SS.BitString 6 := bs false false false true  false false  -- mask 000100
def ef3 : SS.BitString 6 := bs false false true  false false false  -- mask 001000
def ef4 : SS.BitString 6 := bs false true  false false false false  -- mask 010000
def ef5 : SS.BitString 6 := bs true  false false false false false  -- mask 100000
def ef6 : SS.BitString 6 := bs true  false false false false true   -- mask 100001
def ef7 : SS.BitString 6 := bs true  false false false true  false  -- mask 100010
def ef8 : SS.BitString 6 := bs true  false false true  false false  -- mask 100100
def ef9 : SS.BitString 6 := bs true  false true  false false false  -- mask 101000
def ef10 : SS.BitString 6 := bs true  true  false false false false  -- mask 110000
def w0 : SS.BitString 6 := bs false false false false false false  -- dressing 000000
def w1 : SS.BitString 6 := bs false false false false false true   -- dressing 000001
def w2 : SS.BitString 6 := bs false false false false true  false  -- dressing 000010
def w3 : SS.BitString 6 := bs false false false true  false false  -- dressing 000100
def w4 : SS.BitString 6 := bs false false true  false false false  -- dressing 001000
def w5 : SS.BitString 6 := bs false true  false false false false  -- dressing 010000
def w6 : SS.BitString 6 := bs true  false false false false false  -- dressing 100000
def w7 : SS.BitString 6 := bs true  false false false false true   -- dressing 100001
def w8 : SS.BitString 6 := bs true  false false false true  false  -- dressing 100010
def w9 : SS.BitString 6 := bs true  false false true  false false  -- dressing 100100
def w10 : SS.BitString 6 := bs true  false true  false false false  -- dressing 101000
def w11 : SS.BitString 6 := bs true  true  false false false false  -- dressing 110000

theorem incidence0 :
    S1.filter (fun y => SS.bxor y ef0 ∈ S0) = {z0, z5, z6, z11} := by decide
theorem fl0_0 : SS.bxor z0 ef0 = y0 := by decide
theorem fl0_5 : SS.bxor z5 ef0 = y5 := by decide
theorem fl0_6 : SS.bxor z6 ef0 = y6 := by decide
theorem fl0_11 : SS.bxor z11 ef0 = y11 := by decide
theorem sg0_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg0_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg0_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg0_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg0_w6_0 : SS.bdot w6 z0 = false := by decide
theorem sg0_w6_5 : SS.bdot w6 z5 = false := by decide
theorem sg0_w6_6 : SS.bdot w6 z6 = true := by decide
theorem sg0_w6_11 : SS.bdot w6 z11 = true := by decide
theorem sg0_w5_0 : SS.bdot w5 z0 = false := by decide
theorem sg0_w5_5 : SS.bdot w5 z5 = true := by decide
theorem sg0_w5_6 : SS.bdot w5 z6 = false := by decide
theorem sg0_w5_11 : SS.bdot w5 z11 = true := by decide
theorem sg0_w4_0 : SS.bdot w4 z0 = false := by decide
theorem sg0_w4_5 : SS.bdot w4 z5 = true := by decide
theorem sg0_w4_6 : SS.bdot w4 z6 = false := by decide
theorem sg0_w4_11 : SS.bdot w4 z11 = true := by decide
theorem sg0_w3_0 : SS.bdot w3 z0 = false := by decide
theorem sg0_w3_5 : SS.bdot w3 z5 = true := by decide
theorem sg0_w3_6 : SS.bdot w3 z6 = false := by decide
theorem sg0_w3_11 : SS.bdot w3 z11 = true := by decide
theorem sg0_w2_0 : SS.bdot w2 z0 = false := by decide
theorem sg0_w2_5 : SS.bdot w2 z5 = true := by decide
theorem sg0_w2_6 : SS.bdot w2 z6 = false := by decide
theorem sg0_w2_11 : SS.bdot w2 z11 = true := by decide
theorem sg0_w1_0 : SS.bdot w1 z0 = true := by decide
theorem sg0_w1_5 : SS.bdot w1 z5 = true := by decide
theorem sg0_w1_6 : SS.bdot w1 z6 = true := by decide
theorem sg0_w1_11 : SS.bdot w1 z11 = true := by decide
theorem incidence1 :
    S1.filter (fun y => SS.bxor y ef1 ∈ S0) = {z1, z5, z7, z11} := by decide
theorem fl1_1 : SS.bxor z1 ef1 = y0 := by decide
theorem fl1_5 : SS.bxor z5 ef1 = y4 := by decide
theorem fl1_7 : SS.bxor z7 ef1 = y6 := by decide
theorem fl1_11 : SS.bxor z11 ef1 = y10 := by decide
theorem sg1_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg1_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg1_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg1_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg1_w6_1 : SS.bdot w6 z1 = false := by decide
theorem sg1_w6_5 : SS.bdot w6 z5 = false := by decide
theorem sg1_w6_7 : SS.bdot w6 z7 = true := by decide
theorem sg1_w6_11 : SS.bdot w6 z11 = true := by decide
theorem sg1_w5_1 : SS.bdot w5 z1 = false := by decide
theorem sg1_w5_5 : SS.bdot w5 z5 = true := by decide
theorem sg1_w5_7 : SS.bdot w5 z7 = false := by decide
theorem sg1_w5_11 : SS.bdot w5 z11 = true := by decide
theorem sg1_w4_1 : SS.bdot w4 z1 = false := by decide
theorem sg1_w4_5 : SS.bdot w4 z5 = true := by decide
theorem sg1_w4_7 : SS.bdot w4 z7 = false := by decide
theorem sg1_w4_11 : SS.bdot w4 z11 = true := by decide
theorem sg1_w3_1 : SS.bdot w3 z1 = false := by decide
theorem sg1_w3_5 : SS.bdot w3 z5 = true := by decide
theorem sg1_w3_7 : SS.bdot w3 z7 = false := by decide
theorem sg1_w3_11 : SS.bdot w3 z11 = true := by decide
theorem sg1_w2_1 : SS.bdot w2 z1 = true := by decide
theorem sg1_w2_5 : SS.bdot w2 z5 = true := by decide
theorem sg1_w2_7 : SS.bdot w2 z7 = true := by decide
theorem sg1_w2_11 : SS.bdot w2 z11 = true := by decide
theorem sg1_w1_1 : SS.bdot w1 z1 = false := by decide
theorem sg1_w1_5 : SS.bdot w1 z5 = true := by decide
theorem sg1_w1_7 : SS.bdot w1 z7 = false := by decide
theorem sg1_w1_11 : SS.bdot w1 z11 = true := by decide
theorem incidence2 :
    S1.filter (fun y => SS.bxor y ef2 ∈ S0) = {z2, z5, z8, z11} := by decide
theorem fl2_2 : SS.bxor z2 ef2 = y0 := by decide
theorem fl2_5 : SS.bxor z5 ef2 = y3 := by decide
theorem fl2_8 : SS.bxor z8 ef2 = y6 := by decide
theorem fl2_11 : SS.bxor z11 ef2 = y9 := by decide
theorem sg2_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg2_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg2_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg2_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg2_w6_2 : SS.bdot w6 z2 = false := by decide
theorem sg2_w6_5 : SS.bdot w6 z5 = false := by decide
theorem sg2_w6_8 : SS.bdot w6 z8 = true := by decide
theorem sg2_w6_11 : SS.bdot w6 z11 = true := by decide
theorem sg2_w5_2 : SS.bdot w5 z2 = false := by decide
theorem sg2_w5_5 : SS.bdot w5 z5 = true := by decide
theorem sg2_w5_8 : SS.bdot w5 z8 = false := by decide
theorem sg2_w5_11 : SS.bdot w5 z11 = true := by decide
theorem sg2_w4_2 : SS.bdot w4 z2 = false := by decide
theorem sg2_w4_5 : SS.bdot w4 z5 = true := by decide
theorem sg2_w4_8 : SS.bdot w4 z8 = false := by decide
theorem sg2_w4_11 : SS.bdot w4 z11 = true := by decide
theorem sg2_w3_2 : SS.bdot w3 z2 = true := by decide
theorem sg2_w3_5 : SS.bdot w3 z5 = true := by decide
theorem sg2_w3_8 : SS.bdot w3 z8 = true := by decide
theorem sg2_w3_11 : SS.bdot w3 z11 = true := by decide
theorem sg2_w2_2 : SS.bdot w2 z2 = false := by decide
theorem sg2_w2_5 : SS.bdot w2 z5 = true := by decide
theorem sg2_w2_8 : SS.bdot w2 z8 = false := by decide
theorem sg2_w2_11 : SS.bdot w2 z11 = true := by decide
theorem sg2_w1_2 : SS.bdot w1 z2 = false := by decide
theorem sg2_w1_5 : SS.bdot w1 z5 = true := by decide
theorem sg2_w1_8 : SS.bdot w1 z8 = false := by decide
theorem sg2_w1_11 : SS.bdot w1 z11 = true := by decide
theorem incidence3 :
    S1.filter (fun y => SS.bxor y ef3 ∈ S0) = {z3, z5, z9, z11} := by decide
theorem fl3_3 : SS.bxor z3 ef3 = y0 := by decide
theorem fl3_5 : SS.bxor z5 ef3 = y2 := by decide
theorem fl3_9 : SS.bxor z9 ef3 = y6 := by decide
theorem fl3_11 : SS.bxor z11 ef3 = y8 := by decide
theorem sg3_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg3_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg3_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg3_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg3_w6_3 : SS.bdot w6 z3 = false := by decide
theorem sg3_w6_5 : SS.bdot w6 z5 = false := by decide
theorem sg3_w6_9 : SS.bdot w6 z9 = true := by decide
theorem sg3_w6_11 : SS.bdot w6 z11 = true := by decide
theorem sg3_w5_3 : SS.bdot w5 z3 = false := by decide
theorem sg3_w5_5 : SS.bdot w5 z5 = true := by decide
theorem sg3_w5_9 : SS.bdot w5 z9 = false := by decide
theorem sg3_w5_11 : SS.bdot w5 z11 = true := by decide
theorem sg3_w4_3 : SS.bdot w4 z3 = true := by decide
theorem sg3_w4_5 : SS.bdot w4 z5 = true := by decide
theorem sg3_w4_9 : SS.bdot w4 z9 = true := by decide
theorem sg3_w4_11 : SS.bdot w4 z11 = true := by decide
theorem sg3_w3_3 : SS.bdot w3 z3 = false := by decide
theorem sg3_w3_5 : SS.bdot w3 z5 = true := by decide
theorem sg3_w3_9 : SS.bdot w3 z9 = false := by decide
theorem sg3_w3_11 : SS.bdot w3 z11 = true := by decide
theorem sg3_w2_3 : SS.bdot w2 z3 = false := by decide
theorem sg3_w2_5 : SS.bdot w2 z5 = true := by decide
theorem sg3_w2_9 : SS.bdot w2 z9 = false := by decide
theorem sg3_w2_11 : SS.bdot w2 z11 = true := by decide
theorem sg3_w1_3 : SS.bdot w1 z3 = false := by decide
theorem sg3_w1_5 : SS.bdot w1 z5 = true := by decide
theorem sg3_w1_9 : SS.bdot w1 z9 = false := by decide
theorem sg3_w1_11 : SS.bdot w1 z11 = true := by decide
theorem incidence4 :
    S1.filter (fun y => SS.bxor y ef4 ∈ S0) = {z4, z5, z10, z11} := by decide
theorem fl4_4 : SS.bxor z4 ef4 = y0 := by decide
theorem fl4_5 : SS.bxor z5 ef4 = y1 := by decide
theorem fl4_10 : SS.bxor z10 ef4 = y6 := by decide
theorem fl4_11 : SS.bxor z11 ef4 = y7 := by decide
theorem sg4_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg4_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg4_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg4_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg4_w6_4 : SS.bdot w6 z4 = false := by decide
theorem sg4_w6_5 : SS.bdot w6 z5 = false := by decide
theorem sg4_w6_10 : SS.bdot w6 z10 = true := by decide
theorem sg4_w6_11 : SS.bdot w6 z11 = true := by decide
theorem sg4_w5_4 : SS.bdot w5 z4 = true := by decide
theorem sg4_w5_5 : SS.bdot w5 z5 = true := by decide
theorem sg4_w5_10 : SS.bdot w5 z10 = true := by decide
theorem sg4_w5_11 : SS.bdot w5 z11 = true := by decide
theorem sg4_w4_4 : SS.bdot w4 z4 = false := by decide
theorem sg4_w4_5 : SS.bdot w4 z5 = true := by decide
theorem sg4_w4_10 : SS.bdot w4 z10 = false := by decide
theorem sg4_w4_11 : SS.bdot w4 z11 = true := by decide
theorem sg4_w3_4 : SS.bdot w3 z4 = false := by decide
theorem sg4_w3_5 : SS.bdot w3 z5 = true := by decide
theorem sg4_w3_10 : SS.bdot w3 z10 = false := by decide
theorem sg4_w3_11 : SS.bdot w3 z11 = true := by decide
theorem sg4_w2_4 : SS.bdot w2 z4 = false := by decide
theorem sg4_w2_5 : SS.bdot w2 z5 = true := by decide
theorem sg4_w2_10 : SS.bdot w2 z10 = false := by decide
theorem sg4_w2_11 : SS.bdot w2 z11 = true := by decide
theorem sg4_w1_4 : SS.bdot w1 z4 = false := by decide
theorem sg4_w1_5 : SS.bdot w1 z5 = true := by decide
theorem sg4_w1_10 : SS.bdot w1 z10 = false := by decide
theorem sg4_w1_11 : SS.bdot w1 z11 = true := by decide
theorem incidence6 :
    S1.filter (fun y => SS.bxor y ef6 ∈ S0) = {z0, z5, z6, z11} := by decide
theorem fl6_0 : SS.bxor z0 ef6 = y6 := by decide
theorem fl6_5 : SS.bxor z5 ef6 = y11 := by decide
theorem fl6_6 : SS.bxor z6 ef6 = y0 := by decide
theorem fl6_11 : SS.bxor z11 ef6 = y5 := by decide
theorem sg6_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg6_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg6_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg6_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg6_w6_0 : SS.bdot w6 z0 = false := by decide
theorem sg6_w6_5 : SS.bdot w6 z5 = false := by decide
theorem sg6_w6_6 : SS.bdot w6 z6 = true := by decide
theorem sg6_w6_11 : SS.bdot w6 z11 = true := by decide
theorem sg6_w1_0 : SS.bdot w1 z0 = true := by decide
theorem sg6_w1_5 : SS.bdot w1 z5 = true := by decide
theorem sg6_w1_6 : SS.bdot w1 z6 = true := by decide
theorem sg6_w1_11 : SS.bdot w1 z11 = true := by decide
theorem sg6_w7_0 : SS.bdot w7 z0 = true := by decide
theorem sg6_w7_5 : SS.bdot w7 z5 = true := by decide
theorem sg6_w7_6 : SS.bdot w7 z6 = false := by decide
theorem sg6_w7_11 : SS.bdot w7 z11 = false := by decide
theorem incidence7 :
    S1.filter (fun y => SS.bxor y ef7 ∈ S0) = {z1, z5, z7, z11} := by decide
theorem fl7_1 : SS.bxor z1 ef7 = y6 := by decide
theorem fl7_5 : SS.bxor z5 ef7 = y10 := by decide
theorem fl7_7 : SS.bxor z7 ef7 = y0 := by decide
theorem fl7_11 : SS.bxor z11 ef7 = y4 := by decide
theorem sg7_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg7_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg7_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg7_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg7_w6_1 : SS.bdot w6 z1 = false := by decide
theorem sg7_w6_5 : SS.bdot w6 z5 = false := by decide
theorem sg7_w6_7 : SS.bdot w6 z7 = true := by decide
theorem sg7_w6_11 : SS.bdot w6 z11 = true := by decide
theorem sg7_w2_1 : SS.bdot w2 z1 = true := by decide
theorem sg7_w2_5 : SS.bdot w2 z5 = true := by decide
theorem sg7_w2_7 : SS.bdot w2 z7 = true := by decide
theorem sg7_w2_11 : SS.bdot w2 z11 = true := by decide
theorem sg7_w8_1 : SS.bdot w8 z1 = true := by decide
theorem sg7_w8_5 : SS.bdot w8 z5 = true := by decide
theorem sg7_w8_7 : SS.bdot w8 z7 = false := by decide
theorem sg7_w8_11 : SS.bdot w8 z11 = false := by decide
theorem incidence8 :
    S1.filter (fun y => SS.bxor y ef8 ∈ S0) = {z2, z5, z8, z11} := by decide
theorem fl8_2 : SS.bxor z2 ef8 = y6 := by decide
theorem fl8_5 : SS.bxor z5 ef8 = y9 := by decide
theorem fl8_8 : SS.bxor z8 ef8 = y0 := by decide
theorem fl8_11 : SS.bxor z11 ef8 = y3 := by decide
theorem sg8_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg8_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg8_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg8_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg8_w6_2 : SS.bdot w6 z2 = false := by decide
theorem sg8_w6_5 : SS.bdot w6 z5 = false := by decide
theorem sg8_w6_8 : SS.bdot w6 z8 = true := by decide
theorem sg8_w6_11 : SS.bdot w6 z11 = true := by decide
theorem sg8_w3_2 : SS.bdot w3 z2 = true := by decide
theorem sg8_w3_5 : SS.bdot w3 z5 = true := by decide
theorem sg8_w3_8 : SS.bdot w3 z8 = true := by decide
theorem sg8_w3_11 : SS.bdot w3 z11 = true := by decide
theorem sg8_w9_2 : SS.bdot w9 z2 = true := by decide
theorem sg8_w9_5 : SS.bdot w9 z5 = true := by decide
theorem sg8_w9_8 : SS.bdot w9 z8 = false := by decide
theorem sg8_w9_11 : SS.bdot w9 z11 = false := by decide
theorem incidence9 :
    S1.filter (fun y => SS.bxor y ef9 ∈ S0) = {z3, z5, z9, z11} := by decide
theorem fl9_3 : SS.bxor z3 ef9 = y6 := by decide
theorem fl9_5 : SS.bxor z5 ef9 = y8 := by decide
theorem fl9_9 : SS.bxor z9 ef9 = y0 := by decide
theorem fl9_11 : SS.bxor z11 ef9 = y2 := by decide
theorem sg9_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg9_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg9_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg9_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg9_w6_3 : SS.bdot w6 z3 = false := by decide
theorem sg9_w6_5 : SS.bdot w6 z5 = false := by decide
theorem sg9_w6_9 : SS.bdot w6 z9 = true := by decide
theorem sg9_w6_11 : SS.bdot w6 z11 = true := by decide
theorem sg9_w4_3 : SS.bdot w4 z3 = true := by decide
theorem sg9_w4_5 : SS.bdot w4 z5 = true := by decide
theorem sg9_w4_9 : SS.bdot w4 z9 = true := by decide
theorem sg9_w4_11 : SS.bdot w4 z11 = true := by decide
theorem sg9_w10_3 : SS.bdot w10 z3 = true := by decide
theorem sg9_w10_5 : SS.bdot w10 z5 = true := by decide
theorem sg9_w10_9 : SS.bdot w10 z9 = false := by decide
theorem sg9_w10_11 : SS.bdot w10 z11 = false := by decide
theorem incidence10 :
    S1.filter (fun y => SS.bxor y ef10 ∈ S0) = {z4, z5, z10, z11} := by decide
theorem fl10_4 : SS.bxor z4 ef10 = y6 := by decide
theorem fl10_5 : SS.bxor z5 ef10 = y7 := by decide
theorem fl10_10 : SS.bxor z10 ef10 = y0 := by decide
theorem fl10_11 : SS.bxor z11 ef10 = y1 := by decide
theorem sg10_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg10_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg10_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg10_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg10_w6_4 : SS.bdot w6 z4 = false := by decide
theorem sg10_w6_5 : SS.bdot w6 z5 = false := by decide
theorem sg10_w6_10 : SS.bdot w6 z10 = true := by decide
theorem sg10_w6_11 : SS.bdot w6 z11 = true := by decide
theorem sg10_w5_4 : SS.bdot w5 z4 = true := by decide
theorem sg10_w5_5 : SS.bdot w5 z5 = true := by decide
theorem sg10_w5_10 : SS.bdot w5 z10 = true := by decide
theorem sg10_w5_11 : SS.bdot w5 z11 = true := by decide
theorem sg10_w11_4 : SS.bdot w11 z4 = true := by decide
theorem sg10_w11_5 : SS.bdot w11 z5 = true := by decide
theorem sg10_w11_10 : SS.bdot w11 z10 = false := by decide
theorem sg10_w11_11 : SS.bdot w11 z11 = false := by decide

/-! ## The diagonal matrix elements -/

/-- `<0_L| X^e Z^z |0_L>` with the global prefactor omitted. -/
def diagBot (c : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ x ∈ S0.filter (fun x => SS.bxor x e ∈ S0),
      SixQubit.signMul (SS.bdot z x) (star (c (SS.bxor x e)) * c x)

/-- `<1_L| X^e Z^z |1_L>`. -/
def diagTop (d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S1),
      SixQubit.signMul (SS.bdot z y) (star (d (SS.bxor y e)) * d y)

def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),
      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

theorem diagB_inc :
    S0.filter (fun x => SS.bxor x ef5 ∈ S0) = {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11} := by decide
theorem diagT_inc :
    S1.filter (fun y => SS.bxor y ef5 ∈ S1) = {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11} := by decide
theorem dfb0 : SS.bxor y0 ef5 = y6 := by decide
theorem dfb1 : SS.bxor y1 ef5 = y7 := by decide
theorem dfb2 : SS.bxor y2 ef5 = y8 := by decide
theorem dfb3 : SS.bxor y3 ef5 = y9 := by decide
theorem dfb4 : SS.bxor y4 ef5 = y10 := by decide
theorem dfb5 : SS.bxor y5 ef5 = y11 := by decide
theorem dfb6 : SS.bxor y6 ef5 = y0 := by decide
theorem dfb7 : SS.bxor y7 ef5 = y1 := by decide
theorem dfb8 : SS.bxor y8 ef5 = y2 := by decide
theorem dfb9 : SS.bxor y9 ef5 = y3 := by decide
theorem dfb10 : SS.bxor y10 ef5 = y4 := by decide
theorem dfb11 : SS.bxor y11 ef5 = y5 := by decide
theorem dft0 : SS.bxor z0 ef5 = z6 := by decide
theorem dft1 : SS.bxor z1 ef5 = z7 := by decide
theorem dft2 : SS.bxor z2 ef5 = z8 := by decide
theorem dft3 : SS.bxor z3 ef5 = z9 := by decide
theorem dft4 : SS.bxor z4 ef5 = z10 := by decide
theorem dft5 : SS.bxor z5 ef5 = z11 := by decide
theorem dft6 : SS.bxor z6 ef5 = z0 := by decide
theorem dft7 : SS.bxor z7 ef5 = z1 := by decide
theorem dft8 : SS.bxor z8 ef5 = z2 := by decide
theorem dft9 : SS.bxor z9 ef5 = z3 := by decide
theorem dft10 : SS.bxor z10 ef5 = z4 := by decide
theorem dft11 : SS.bxor z11 ef5 = z5 := by decide
theorem dsbw0_0 : SS.bdot w0 y0 = false := by decide
theorem dsbw0_1 : SS.bdot w0 y1 = false := by decide
theorem dsbw0_2 : SS.bdot w0 y2 = false := by decide
theorem dsbw0_3 : SS.bdot w0 y3 = false := by decide
theorem dsbw0_4 : SS.bdot w0 y4 = false := by decide
theorem dsbw0_5 : SS.bdot w0 y5 = false := by decide
theorem dsbw0_6 : SS.bdot w0 y6 = false := by decide
theorem dsbw0_7 : SS.bdot w0 y7 = false := by decide
theorem dsbw0_8 : SS.bdot w0 y8 = false := by decide
theorem dsbw0_9 : SS.bdot w0 y9 = false := by decide
theorem dsbw0_10 : SS.bdot w0 y10 = false := by decide
theorem dsbw0_11 : SS.bdot w0 y11 = false := by decide
theorem dstw0_0 : SS.bdot w0 z0 = false := by decide
theorem dstw0_1 : SS.bdot w0 z1 = false := by decide
theorem dstw0_2 : SS.bdot w0 z2 = false := by decide
theorem dstw0_3 : SS.bdot w0 z3 = false := by decide
theorem dstw0_4 : SS.bdot w0 z4 = false := by decide
theorem dstw0_5 : SS.bdot w0 z5 = false := by decide
theorem dstw0_6 : SS.bdot w0 z6 = false := by decide
theorem dstw0_7 : SS.bdot w0 z7 = false := by decide
theorem dstw0_8 : SS.bdot w0 z8 = false := by decide
theorem dstw0_9 : SS.bdot w0 z9 = false := by decide
theorem dstw0_10 : SS.bdot w0 z10 = false := by decide
theorem dstw0_11 : SS.bdot w0 z11 = false := by decide
theorem dsbw6_0 : SS.bdot w6 y0 = false := by decide
theorem dsbw6_1 : SS.bdot w6 y1 = false := by decide
theorem dsbw6_2 : SS.bdot w6 y2 = false := by decide
theorem dsbw6_3 : SS.bdot w6 y3 = false := by decide
theorem dsbw6_4 : SS.bdot w6 y4 = false := by decide
theorem dsbw6_5 : SS.bdot w6 y5 = false := by decide
theorem dsbw6_6 : SS.bdot w6 y6 = true := by decide
theorem dsbw6_7 : SS.bdot w6 y7 = true := by decide
theorem dsbw6_8 : SS.bdot w6 y8 = true := by decide
theorem dsbw6_9 : SS.bdot w6 y9 = true := by decide
theorem dsbw6_10 : SS.bdot w6 y10 = true := by decide
theorem dsbw6_11 : SS.bdot w6 y11 = true := by decide
theorem dstw6_0 : SS.bdot w6 z0 = false := by decide
theorem dstw6_1 : SS.bdot w6 z1 = false := by decide
theorem dstw6_2 : SS.bdot w6 z2 = false := by decide
theorem dstw6_3 : SS.bdot w6 z3 = false := by decide
theorem dstw6_4 : SS.bdot w6 z4 = false := by decide
theorem dstw6_5 : SS.bdot w6 z5 = false := by decide
theorem dstw6_6 : SS.bdot w6 z6 = true := by decide
theorem dstw6_7 : SS.bdot w6 z7 = true := by decide
theorem dstw6_8 : SS.bdot w6 z8 = true := by decide
theorem dstw6_9 : SS.bdot w6 z9 = true := by decide
theorem dstw6_10 : SS.bdot w6 z10 = true := by decide
theorem dstw6_11 : SS.bdot w6 z11 = true := by decide

/-! ## The moment system -/

/-- The two normalizations, the twenty-one moment equalities, and the
nonnegativity of every probability. -/
structure MomentSystem (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 : Real) : Prop where
  n0 : q0 + q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 + q9 + q10 + q11 = 1
  n1 : r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 = 1
  m1 : q6 + q7 + q8 + q9 + q10 + q11 = r6 + r7 + r8 + r9 + r10 + r11
  m2 : q2 + q3 + q4 + q5 + q8 + q9 + q10 + q11 = r4 + r5 + r10 + r11
  m3 : q1 + q3 + q4 + q5 + q7 + q9 + q10 + q11 = r3 + r5 + r9 + r11
  m4 : q1 + q2 + q4 + q5 + q7 + q8 + q10 + q11 = r2 + r5 + r8 + r11
  m5 : q1 + q2 + q3 + q5 + q7 + q8 + q9 + q11 = r1 + r5 + r7 + r11
  m6 : q1 + q2 + q3 + q4 + q7 + q8 + q9 + q10 = r0 + r5 + r6 + r11
  c12 : q8 + q9 + q10 + q11 = r10 + r11
  c13 : q7 + q9 + q10 + q11 = r9 + r11
  c14 : q7 + q8 + q10 + q11 = r8 + r11
  c15 : q7 + q8 + q9 + q11 = r7 + r11
  c16 : q7 + q8 + q9 + q10 = r6 + r11
  c23 : q3 + q4 + q5 + q9 + q10 + q11 = r5 + r11
  c24 : q2 + q4 + q5 + q8 + q10 + q11 = r5 + r11
  c25 : q2 + q3 + q5 + q8 + q9 + q11 = r5 + r11
  c26 : q2 + q3 + q4 + q8 + q9 + q10 = r5 + r11
  c34 : q1 + q4 + q5 + q7 + q10 + q11 = r5 + r11
  c35 : q1 + q3 + q5 + q7 + q9 + q11 = r5 + r11
  c36 : q1 + q3 + q4 + q7 + q9 + q10 = r5 + r11
  c45 : q1 + q2 + q5 + q7 + q8 + q11 = r5 + r11
  c46 : q1 + q2 + q4 + q7 + q8 + q10 = r5 + r11
  c56 : q1 + q2 + q3 + q7 + q8 + q9 = r5 + r11

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

set_option maxHeartbeats 2000000 in
/-- Squared-modulus consequence 0, reduced against the moment system. -/
theorem lin0 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11)
    (hq : q0 * r4 = q6 * r10) :
    -15*r10/32 + r11/32 - 3*r6/32 - 3*r7/32 - 3*r8/32 - 3*r9/32 + 3/64 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11⟩ := h
  linear_combination hq + (-r4) * n0 + (3*r10/32 - r11/32 + 5*r4/8 + 3*r6/32 + 3*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * n1 + (r10 + r4) * m1 + (-21*r10/32 + 7*r11/32 + 5*r4/8 - 21*r6/32 - 21*r7/32 - 21*r8/32 - 21*r9/32 + 21/64) * m2 + (3*r10/32 - r11/32 + 5*r4/8 + 3*r6/32 + 3*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * m3 + (3*r10/32 - r11/32 + 5*r4/8 + 3*r6/32 + 3*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * m4 + (3*r10/32 - r11/32 + 5*r4/8 + 3*r6/32 + 3*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * m5 + (3*r10/32 - r11/32 + 5*r4/8 + 3*r6/32 + 3*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * m6 + (-r10/4 - r4/4) * c12 + (-r10/4 - r4/4) * c13 + (-r10/4 - r4/4) * c14 + (-r10/4 - r4/4) * c15 + (-r10/4 - r4/4) * c16 + (3*r10/4 - r11/4 - r4 + 3*r6/4 + 3*r7/4 + 3*r8/4 + 3*r9/4 - 3/8) * c26 + (-r4) * c36 + (3*r10/8 - r11/8 - 3*r4/2 + 3*r6/8 + 3*r7/8 + 3*r8/8 + 3*r9/8 - 3/16) * c45 + (-3*r10/8 + r11/8 + r4/2 - 3*r6/8 - 3*r7/8 - 3*r8/8 - 3*r9/8 + 3/16) * c46 + (-3*r10/8 + r11/8 + r4/2 - 3*r6/8 - 3*r7/8 - 3*r8/8 - 3*r9/8 + 3/16) * c56

set_option maxHeartbeats 2000000 in
/-- Squared-modulus consequence 1, reduced against the moment system. -/
theorem lin1 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11)
    (hq : q1 * r5 = q7 * r11) :
    9*r10/32 - 7*r11/32 - 3*r6/32 - 3*r7/32 - 3*r8/32 - 3*r9/32 + 3/64 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11⟩ := h
  linear_combination hq + (-9*r10/32 + 3*r11/32 - r5/8 + 3*r6/32 + 3*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * n1 + (-9*r10/32 + 3*r11/32 - r5/8 + 3*r6/32 + 3*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * m2 + (-9*r10/32 + 3*r11/32 - r5/8 + 3*r6/32 + 3*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * m3 + (-9*r10/32 + 3*r11/32 - r5/8 + 3*r6/32 + 3*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * m4 + (-9*r10/32 + 3*r11/32 - r5/8 + 3*r6/32 + 3*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * m5 + (-9*r10/32 + 3*r11/32 - r5/8 + 3*r6/32 + 3*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * m6 + (-3*r11/4 - 3*r5/4) * c12 + (r11/4 + r5/4) * c13 + (r11/4 + r5/4) * c14 + (r11/4 + r5/4) * c15 + (r11/4 + r5/4) * c16 + (3*r10/4 - r11/4 + r5 - r6/4 - r7/4 - r8/4 - r9/4 + 1/8) * c26 + (3*r10/4 - r11/4 - r6/4 - r7/4 - r8/4 - r9/4 + 1/8) * c36 + (9*r10/8 - 3*r11/8 + r5/2 - 3*r6/8 - 3*r7/8 - 3*r8/8 - 3*r9/8 + 3/16) * c45 + (-3*r10/8 + r11/8 - r5/2 + r6/8 + r7/8 + r8/8 + r9/8 - 1/16) * c46 + (-3*r10/8 + r11/8 - r5/2 + r6/8 + r7/8 + r8/8 + r9/8 - 1/16) * c56

set_option maxHeartbeats 2000000 in
/-- Squared-modulus consequence 2, reduced against the moment system. -/
theorem lin2 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11)
    (hq : q0 * r3 = q6 * r9) :
    -3*r10/32 + r11/32 - 3*r6/32 - 3*r7/32 - 3*r8/32 - 15*r9/32 + 3/64 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11⟩ := h
  linear_combination hq + (-r3) * n0 + (3*r10/32 - r11/32 + 5*r3/8 + 3*r6/32 + 3*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * n1 + (r3 + r9) * m1 + (3*r10/32 - r11/32 + 5*r3/8 + 3*r6/32 + 3*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * m2 + (-21*r10/32 + 7*r11/32 + 5*r3/8 - 21*r6/32 - 21*r7/32 - 21*r8/32 - 21*r9/32 + 21/64) * m3 + (3*r10/32 - r11/32 + 5*r3/8 + 3*r6/32 + 3*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * m4 + (3*r10/32 - r11/32 + 5*r3/8 + 3*r6/32 + 3*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * m5 + (3*r10/32 - r11/32 + 5*r3/8 + 3*r6/32 + 3*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * m6 + (-r3/4 - r9/4) * c12 + (-r3/4 - r9/4) * c13 + (-r3/4 - r9/4) * c14 + (-r3/4 - r9/4) * c15 + (-r3/4 - r9/4) * c16 + (-r3) * c26 + (3*r10/4 - r11/4 - r3 + 3*r6/4 + 3*r7/4 + 3*r8/4 + 3*r9/4 - 3/8) * c36 + (3*r10/8 - r11/8 - 3*r3/2 + 3*r6/8 + 3*r7/8 + 3*r8/8 + 3*r9/8 - 3/16) * c45 + (-3*r10/8 + r11/8 + r3/2 - 3*r6/8 - 3*r7/8 - 3*r8/8 - 3*r9/8 + 3/16) * c46 + (-3*r10/8 + r11/8 + r3/2 - 3*r6/8 - 3*r7/8 - 3*r8/8 - 3*r9/8 + 3/16) * c56

set_option maxHeartbeats 2000000 in
/-- Squared-modulus consequence 3, reduced against the moment system. -/
theorem lin3 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11)
    (hq : q2 * r5 = q8 * r11) :
    -3*r10/32 - 7*r11/32 - 3*r6/32 - 3*r7/32 - 3*r8/32 + 9*r9/32 + 3/64 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11⟩ := h
  linear_combination hq + (3*r10/32 + 3*r11/32 - r5/8 + 3*r6/32 + 3*r7/32 + 3*r8/32 - 9*r9/32 - 3/64) * n1 + (3*r10/32 + 3*r11/32 - r5/8 + 3*r6/32 + 3*r7/32 + 3*r8/32 - 9*r9/32 - 3/64) * m2 + (3*r10/32 + 3*r11/32 - r5/8 + 3*r6/32 + 3*r7/32 + 3*r8/32 - 9*r9/32 - 3/64) * m3 + (3*r10/32 + 3*r11/32 - r5/8 + 3*r6/32 + 3*r7/32 + 3*r8/32 - 9*r9/32 - 3/64) * m4 + (3*r10/32 + 3*r11/32 - r5/8 + 3*r6/32 + 3*r7/32 + 3*r8/32 - 9*r9/32 - 3/64) * m5 + (3*r10/32 + 3*r11/32 - r5/8 + 3*r6/32 + 3*r7/32 + 3*r8/32 - 9*r9/32 - 3/64) * m6 + (r11/4 + r5/4) * c12 + (-3*r11/4 - 3*r5/4) * c13 + (r11/4 + r5/4) * c14 + (r11/4 + r5/4) * c15 + (r11/4 + r5/4) * c16 + (-r10/4 - r11/4 - r6/4 - r7/4 - r8/4 + 3*r9/4 + 1/8) * c26 + (-r10/4 - r11/4 + r5 - r6/4 - r7/4 - r8/4 + 3*r9/4 + 1/8) * c36 + (-3*r10/8 - 3*r11/8 + r5/2 - 3*r6/8 - 3*r7/8 - 3*r8/8 + 9*r9/8 + 3/16) * c45 + (r10/8 + r11/8 - r5/2 + r6/8 + r7/8 + r8/8 - 3*r9/8 - 1/16) * c46 + (r10/8 + r11/8 - r5/2 + r6/8 + r7/8 + r8/8 - 3*r9/8 - 1/16) * c56

set_option maxHeartbeats 2000000 in
/-- Squared-modulus consequence 4, reduced against the moment system. -/
theorem lin4 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11)
    (hq : q0 * r2 = q6 * r8) :
    -3*r10/32 + r11/32 - 3*r6/32 - 3*r7/32 - 15*r8/32 - 3*r9/32 + 3/64 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11⟩ := h
  linear_combination hq + (-r2) * n0 + (3*r10/32 - r11/32 + 5*r2/8 + 3*r6/32 + 3*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * n1 + (r2 + r8) * m1 + (3*r10/32 - r11/32 + 5*r2/8 + 3*r6/32 + 3*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * m2 + (3*r10/32 - r11/32 + 5*r2/8 + 3*r6/32 + 3*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * m3 + (-21*r10/32 + 7*r11/32 + 5*r2/8 - 21*r6/32 - 21*r7/32 - 21*r8/32 - 21*r9/32 + 21/64) * m4 + (3*r10/32 - r11/32 + 5*r2/8 + 3*r6/32 + 3*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * m5 + (3*r10/32 - r11/32 + 5*r2/8 + 3*r6/32 + 3*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * m6 + (-r2/4 - r8/4) * c12 + (-r2/4 - r8/4) * c13 + (-r2/4 - r8/4) * c14 + (-r2/4 - r8/4) * c15 + (-r2/4 - r8/4) * c16 + (-r2) * c26 + (-r2) * c36 + (3*r10/8 - r11/8 - 3*r2/2 + 3*r6/8 + 3*r7/8 + 3*r8/8 + 3*r9/8 - 3/16) * c45 + (3*r10/8 - r11/8 + r2/2 + 3*r6/8 + 3*r7/8 + 3*r8/8 + 3*r9/8 - 3/16) * c46 + (-3*r10/8 + r11/8 + r2/2 - 3*r6/8 - 3*r7/8 - 3*r8/8 - 3*r9/8 + 3/16) * c56

set_option maxHeartbeats 2000000 in
/-- Squared-modulus consequence 5, reduced against the moment system. -/
theorem lin5 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11)
    (hq : q3 * r5 = q9 * r11) :
    -3*r10/32 - 7*r11/32 - 3*r6/32 - 3*r7/32 + 9*r8/32 - 3*r9/32 + 3/64 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11⟩ := h
  linear_combination hq + (3*r10/32 + 3*r11/32 - r5/8 + 3*r6/32 + 3*r7/32 - 9*r8/32 + 3*r9/32 - 3/64) * n1 + (3*r10/32 + 3*r11/32 - r5/8 + 3*r6/32 + 3*r7/32 - 9*r8/32 + 3*r9/32 - 3/64) * m2 + (3*r10/32 + 3*r11/32 - r5/8 + 3*r6/32 + 3*r7/32 - 9*r8/32 + 3*r9/32 - 3/64) * m3 + (3*r10/32 + 3*r11/32 - r5/8 + 3*r6/32 + 3*r7/32 - 9*r8/32 + 3*r9/32 - 3/64) * m4 + (3*r10/32 + 3*r11/32 - r5/8 + 3*r6/32 + 3*r7/32 - 9*r8/32 + 3*r9/32 - 3/64) * m5 + (3*r10/32 + 3*r11/32 - r5/8 + 3*r6/32 + 3*r7/32 - 9*r8/32 + 3*r9/32 - 3/64) * m6 + (r11/4 + r5/4) * c12 + (r11/4 + r5/4) * c13 + (-3*r11/4 - 3*r5/4) * c14 + (r11/4 + r5/4) * c15 + (r11/4 + r5/4) * c16 + (-r10/4 - r11/4 - r6/4 - r7/4 + 3*r8/4 - r9/4 + 1/8) * c26 + (-r10/4 - r11/4 - r6/4 - r7/4 + 3*r8/4 - r9/4 + 1/8) * c36 + (-3*r10/8 - 3*r11/8 + r5/2 - 3*r6/8 - 3*r7/8 + 9*r8/8 - 3*r9/8 + 3/16) * c45 + (r10/8 + r11/8 + r5/2 + r6/8 + r7/8 - 3*r8/8 + r9/8 - 1/16) * c46 + (r10/8 + r11/8 - r5/2 + r6/8 + r7/8 - 3*r8/8 + r9/8 - 1/16) * c56

set_option maxHeartbeats 2000000 in
/-- Squared-modulus consequence 6, reduced against the moment system. -/
theorem lin6 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11)
    (hq : q0 * r1 = q6 * r7) :
    -3*r10/32 + r11/32 - 3*r6/32 - 15*r7/32 - 3*r8/32 - 3*r9/32 + 3/64 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11⟩ := h
  linear_combination hq + (-r1) * n0 + (5*r1/8 + 3*r10/32 - r11/32 + 3*r6/32 + 3*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * n1 + (r1 + r7) * m1 + (5*r1/8 + 3*r10/32 - r11/32 + 3*r6/32 + 3*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * m2 + (5*r1/8 + 3*r10/32 - r11/32 + 3*r6/32 + 3*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * m3 + (5*r1/8 + 3*r10/32 - r11/32 + 3*r6/32 + 3*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * m4 + (5*r1/8 - 21*r10/32 + 7*r11/32 - 21*r6/32 - 21*r7/32 - 21*r8/32 - 21*r9/32 + 21/64) * m5 + (5*r1/8 + 3*r10/32 - r11/32 + 3*r6/32 + 3*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * m6 + (-r1/4 - r7/4) * c12 + (-r1/4 - r7/4) * c13 + (-r1/4 - r7/4) * c14 + (-r1/4 - r7/4) * c15 + (-r1/4 - r7/4) * c16 + (-r1) * c26 + (-r1) * c36 + (-3*r1/2 + 3*r10/8 - r11/8 + 3*r6/8 + 3*r7/8 + 3*r8/8 + 3*r9/8 - 3/16) * c45 + (r1/2 - 3*r10/8 + r11/8 - 3*r6/8 - 3*r7/8 - 3*r8/8 - 3*r9/8 + 3/16) * c46 + (r1/2 + 3*r10/8 - r11/8 + 3*r6/8 + 3*r7/8 + 3*r8/8 + 3*r9/8 - 3/16) * c56

set_option maxHeartbeats 2000000 in
/-- Squared-modulus consequence 7, reduced against the moment system. -/
theorem lin7 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11)
    (hq : q4 * r5 = q10 * r11) :
    -3*r10/32 - 7*r11/32 - 3*r6/32 + 9*r7/32 - 3*r8/32 - 3*r9/32 + 3/64 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11⟩ := h
  linear_combination hq + (3*r10/32 + 3*r11/32 - r5/8 + 3*r6/32 - 9*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * n1 + (3*r10/32 + 3*r11/32 - r5/8 + 3*r6/32 - 9*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * m2 + (3*r10/32 + 3*r11/32 - r5/8 + 3*r6/32 - 9*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * m3 + (3*r10/32 + 3*r11/32 - r5/8 + 3*r6/32 - 9*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * m4 + (3*r10/32 + 3*r11/32 - r5/8 + 3*r6/32 - 9*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * m5 + (3*r10/32 + 3*r11/32 - r5/8 + 3*r6/32 - 9*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * m6 + (r11/4 + r5/4) * c12 + (r11/4 + r5/4) * c13 + (r11/4 + r5/4) * c14 + (-3*r11/4 - 3*r5/4) * c15 + (r11/4 + r5/4) * c16 + (-r10/4 - r11/4 - r6/4 + 3*r7/4 - r8/4 - r9/4 + 1/8) * c26 + (-r10/4 - r11/4 - r6/4 + 3*r7/4 - r8/4 - r9/4 + 1/8) * c36 + (-3*r10/8 - 3*r11/8 + r5/2 - 3*r6/8 + 9*r7/8 - 3*r8/8 - 3*r9/8 + 3/16) * c45 + (r10/8 + r11/8 - r5/2 + r6/8 - 3*r7/8 + r8/8 + r9/8 - 1/16) * c46 + (r10/8 + r11/8 + r5/2 + r6/8 - 3*r7/8 + r8/8 + r9/8 - 1/16) * c56

set_option maxHeartbeats 2000000 in
/-- Squared-modulus consequence 8, reduced against the moment system. -/
theorem lin8 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11)
    (hq : q0 * r0 = q6 * r6) :
    -3*r10/32 + r11/32 - 15*r6/32 - 3*r7/32 - 3*r8/32 - 3*r9/32 + 3/64 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11⟩ := h
  linear_combination hq + (-r0) * n0 + (5*r0/8 + 3*r10/32 - r11/32 + 3*r6/32 + 3*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * n1 + (r0 + r6) * m1 + (5*r0/8 + 3*r10/32 - r11/32 + 3*r6/32 + 3*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * m2 + (5*r0/8 + 3*r10/32 - r11/32 + 3*r6/32 + 3*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * m3 + (5*r0/8 + 3*r10/32 - r11/32 + 3*r6/32 + 3*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * m4 + (5*r0/8 + 3*r10/32 - r11/32 + 3*r6/32 + 3*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * m5 + (5*r0/8 - 21*r10/32 + 7*r11/32 - 21*r6/32 - 21*r7/32 - 21*r8/32 - 21*r9/32 + 21/64) * m6 + (-r0/4 - r6/4) * c12 + (-r0/4 - r6/4) * c13 + (-r0/4 - r6/4) * c14 + (-r0/4 - r6/4) * c15 + (-r0/4 - r6/4) * c16 + (-r0) * c26 + (-r0) * c36 + (-3*r0/2 - 3*r10/8 + r11/8 - 3*r6/8 - 3*r7/8 - 3*r8/8 - 3*r9/8 + 3/16) * c45 + (r0/2 + 3*r10/8 - r11/8 + 3*r6/8 + 3*r7/8 + 3*r8/8 + 3*r9/8 - 3/16) * c46 + (r0/2 + 3*r10/8 - r11/8 + 3*r6/8 + 3*r7/8 + 3*r8/8 + 3*r9/8 - 3/16) * c56

set_option maxHeartbeats 2000000 in
/-- Squared-modulus consequence 9, reduced against the moment system. -/
theorem lin9 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11)
    (hq : q5 * r5 = q11 * r11) :
    -3*r10/32 - 7*r11/32 + 9*r6/32 - 3*r7/32 - 3*r8/32 - 3*r9/32 + 3/64 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11⟩ := h
  linear_combination hq + (3*r10/32 + 3*r11/32 - r5/8 - 9*r6/32 + 3*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * n1 + (3*r10/32 + 3*r11/32 - r5/8 - 9*r6/32 + 3*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * m2 + (3*r10/32 + 3*r11/32 - r5/8 - 9*r6/32 + 3*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * m3 + (3*r10/32 + 3*r11/32 - r5/8 - 9*r6/32 + 3*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * m4 + (3*r10/32 + 3*r11/32 - r5/8 - 9*r6/32 + 3*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * m5 + (3*r10/32 + 3*r11/32 - r5/8 - 9*r6/32 + 3*r7/32 + 3*r8/32 + 3*r9/32 - 3/64) * m6 + (r11/4 + r5/4) * c12 + (r11/4 + r5/4) * c13 + (r11/4 + r5/4) * c14 + (r11/4 + r5/4) * c15 + (-3*r11/4 - 3*r5/4) * c16 + (-r10/4 - r11/4 + 3*r6/4 - r7/4 - r8/4 - r9/4 + 1/8) * c26 + (-r10/4 - r11/4 + 3*r6/4 - r7/4 - r8/4 - r9/4 + 1/8) * c36 + (-3*r10/8 - 3*r11/8 - r5/2 + 9*r6/8 - 3*r7/8 - 3*r8/8 - 3*r9/8 + 3/16) * c45 + (r10/8 + r11/8 + r5/2 - 3*r6/8 + r7/8 + r8/8 + r9/8 - 1/16) * c46 + (r10/8 + r11/8 + r5/2 - 3*r6/8 + r7/8 + r8/8 + r9/8 - 1/16) * c56

set_option maxHeartbeats 4000000 in
/-- The ten reduced consequences pin every probability. -/
theorem pinned {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11)
    (v0 : -15*r10/32 + r11/32 - 3*r6/32 - 3*r7/32 - 3*r8/32 - 3*r9/32 + 3/64 = 0)
    (v1 : 9*r10/32 - 7*r11/32 - 3*r6/32 - 3*r7/32 - 3*r8/32 - 3*r9/32 + 3/64 = 0)
    (v2 : -3*r10/32 + r11/32 - 3*r6/32 - 3*r7/32 - 3*r8/32 - 15*r9/32 + 3/64 = 0)
    (_v3 : -3*r10/32 - 7*r11/32 - 3*r6/32 - 3*r7/32 - 3*r8/32 + 9*r9/32 + 3/64 = 0)
    (v4 : -3*r10/32 + r11/32 - 3*r6/32 - 3*r7/32 - 15*r8/32 - 3*r9/32 + 3/64 = 0)
    (_v5 : -3*r10/32 - 7*r11/32 - 3*r6/32 - 3*r7/32 + 9*r8/32 - 3*r9/32 + 3/64 = 0)
    (v6 : -3*r10/32 + r11/32 - 3*r6/32 - 15*r7/32 - 3*r8/32 - 3*r9/32 + 3/64 = 0)
    (_v7 : -3*r10/32 - 7*r11/32 - 3*r6/32 + 9*r7/32 - 3*r8/32 - 3*r9/32 + 3/64 = 0)
    (v8 : -3*r10/32 + r11/32 - 15*r6/32 - 3*r7/32 - 3*r8/32 - 3*r9/32 + 3/64 = 0)
    (_v9 : -3*r10/32 - 7*r11/32 + 9*r6/32 - 3*r7/32 - 3*r8/32 - 3*r9/32 + 3/64 = 0)
    : q0 = 3/16 ∧ q1 = 1/16 ∧ q2 = 1/16 ∧ q3 = 1/16 ∧ q4 = 1/16 ∧ q5 = 1/16 ∧ q6 = 3/16 ∧ q7 = 1/16 ∧ q8 = 1/16 ∧ q9 = 1/16 ∧ q10 = 1/16 ∧ q11 = 1/16 ∧ r0 = 1/16 ∧ r1 = 1/16 ∧ r2 = 1/16 ∧ r3 = 1/16 ∧ r4 = 1/16 ∧ r5 = 3/16 ∧ r6 = 1/16 ∧ r7 = 1/16 ∧ r8 = 1/16 ∧ r9 = 1/16 ∧ r10 = 1/16 ∧ r11 = 3/16 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-! ## Walsh expansions -/

theorem ex0_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w0 = star (c y0) * d z0 + star (c y5) * d z5 + star (c y6) * d z6 + star (c y11) * d z11 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_0, fl0_5, fl0_6, fl0_11]
  simp only [sg0_w0_0, sg0_w0_5, sg0_w0_6, sg0_w0_11, SixQubit.signMul_false]
  try ring

theorem ex0_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w6 = star (c y0) * d z0 + star (c y5) * d z5 - star (c y6) * d z6 - star (c y11) * d z11 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_0, fl0_5, fl0_6, fl0_11]
  simp only [sg0_w6_0, sg0_w6_5, sg0_w6_6, sg0_w6_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex0_w5 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w5 = star (c y0) * d z0 - star (c y5) * d z5 + star (c y6) * d z6 - star (c y11) * d z11 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_0, fl0_5, fl0_6, fl0_11]
  simp only [sg0_w5_0, sg0_w5_5, sg0_w5_6, sg0_w5_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex0_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w4 = star (c y0) * d z0 - star (c y5) * d z5 + star (c y6) * d z6 - star (c y11) * d z11 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_0, fl0_5, fl0_6, fl0_11]
  simp only [sg0_w4_0, sg0_w4_5, sg0_w4_6, sg0_w4_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex0_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w3 = star (c y0) * d z0 - star (c y5) * d z5 + star (c y6) * d z6 - star (c y11) * d z11 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_0, fl0_5, fl0_6, fl0_11]
  simp only [sg0_w3_0, sg0_w3_5, sg0_w3_6, sg0_w3_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex0_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w2 = star (c y0) * d z0 - star (c y5) * d z5 + star (c y6) * d z6 - star (c y11) * d z11 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_0, fl0_5, fl0_6, fl0_11]
  simp only [sg0_w2_0, sg0_w2_5, sg0_w2_6, sg0_w2_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex0_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w1 = - star (c y0) * d z0 - star (c y5) * d z5 - star (c y6) * d z6 - star (c y11) * d z11 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_0, fl0_5, fl0_6, fl0_11]
  simp only [sg0_w1_0, sg0_w1_5, sg0_w1_6, sg0_w1_11, SixQubit.signMul_true]
  try ring

theorem ex1_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w0 = star (c y0) * d z1 + star (c y4) * d z5 + star (c y6) * d z7 + star (c y10) * d z11 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_1, fl1_5, fl1_7, fl1_11]
  simp only [sg1_w0_1, sg1_w0_5, sg1_w0_7, sg1_w0_11, SixQubit.signMul_false]
  try ring

theorem ex1_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w6 = star (c y0) * d z1 + star (c y4) * d z5 - star (c y6) * d z7 - star (c y10) * d z11 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_1, fl1_5, fl1_7, fl1_11]
  simp only [sg1_w6_1, sg1_w6_5, sg1_w6_7, sg1_w6_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex1_w5 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w5 = star (c y0) * d z1 - star (c y4) * d z5 + star (c y6) * d z7 - star (c y10) * d z11 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_1, fl1_5, fl1_7, fl1_11]
  simp only [sg1_w5_1, sg1_w5_5, sg1_w5_7, sg1_w5_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex1_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w4 = star (c y0) * d z1 - star (c y4) * d z5 + star (c y6) * d z7 - star (c y10) * d z11 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_1, fl1_5, fl1_7, fl1_11]
  simp only [sg1_w4_1, sg1_w4_5, sg1_w4_7, sg1_w4_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex1_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w3 = star (c y0) * d z1 - star (c y4) * d z5 + star (c y6) * d z7 - star (c y10) * d z11 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_1, fl1_5, fl1_7, fl1_11]
  simp only [sg1_w3_1, sg1_w3_5, sg1_w3_7, sg1_w3_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex1_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w2 = - star (c y0) * d z1 - star (c y4) * d z5 - star (c y6) * d z7 - star (c y10) * d z11 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_1, fl1_5, fl1_7, fl1_11]
  simp only [sg1_w2_1, sg1_w2_5, sg1_w2_7, sg1_w2_11, SixQubit.signMul_true]
  try ring

theorem ex1_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w1 = star (c y0) * d z1 - star (c y4) * d z5 + star (c y6) * d z7 - star (c y10) * d z11 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_1, fl1_5, fl1_7, fl1_11]
  simp only [sg1_w1_1, sg1_w1_5, sg1_w1_7, sg1_w1_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex2_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w0 = star (c y0) * d z2 + star (c y3) * d z5 + star (c y6) * d z8 + star (c y9) * d z11 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_2, fl2_5, fl2_8, fl2_11]
  simp only [sg2_w0_2, sg2_w0_5, sg2_w0_8, sg2_w0_11, SixQubit.signMul_false]
  try ring

theorem ex2_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w6 = star (c y0) * d z2 + star (c y3) * d z5 - star (c y6) * d z8 - star (c y9) * d z11 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_2, fl2_5, fl2_8, fl2_11]
  simp only [sg2_w6_2, sg2_w6_5, sg2_w6_8, sg2_w6_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex2_w5 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w5 = star (c y0) * d z2 - star (c y3) * d z5 + star (c y6) * d z8 - star (c y9) * d z11 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_2, fl2_5, fl2_8, fl2_11]
  simp only [sg2_w5_2, sg2_w5_5, sg2_w5_8, sg2_w5_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex2_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w4 = star (c y0) * d z2 - star (c y3) * d z5 + star (c y6) * d z8 - star (c y9) * d z11 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_2, fl2_5, fl2_8, fl2_11]
  simp only [sg2_w4_2, sg2_w4_5, sg2_w4_8, sg2_w4_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex2_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w3 = - star (c y0) * d z2 - star (c y3) * d z5 - star (c y6) * d z8 - star (c y9) * d z11 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_2, fl2_5, fl2_8, fl2_11]
  simp only [sg2_w3_2, sg2_w3_5, sg2_w3_8, sg2_w3_11, SixQubit.signMul_true]
  try ring

theorem ex2_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w2 = star (c y0) * d z2 - star (c y3) * d z5 + star (c y6) * d z8 - star (c y9) * d z11 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_2, fl2_5, fl2_8, fl2_11]
  simp only [sg2_w2_2, sg2_w2_5, sg2_w2_8, sg2_w2_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex2_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w1 = star (c y0) * d z2 - star (c y3) * d z5 + star (c y6) * d z8 - star (c y9) * d z11 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_2, fl2_5, fl2_8, fl2_11]
  simp only [sg2_w1_2, sg2_w1_5, sg2_w1_8, sg2_w1_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex3_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w0 = star (c y0) * d z3 + star (c y2) * d z5 + star (c y6) * d z9 + star (c y8) * d z11 := by
  unfold offSum
  rw [incidence3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl3_3, fl3_5, fl3_9, fl3_11]
  simp only [sg3_w0_3, sg3_w0_5, sg3_w0_9, sg3_w0_11, SixQubit.signMul_false]
  try ring

theorem ex3_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w6 = star (c y0) * d z3 + star (c y2) * d z5 - star (c y6) * d z9 - star (c y8) * d z11 := by
  unfold offSum
  rw [incidence3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl3_3, fl3_5, fl3_9, fl3_11]
  simp only [sg3_w6_3, sg3_w6_5, sg3_w6_9, sg3_w6_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex3_w5 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w5 = star (c y0) * d z3 - star (c y2) * d z5 + star (c y6) * d z9 - star (c y8) * d z11 := by
  unfold offSum
  rw [incidence3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl3_3, fl3_5, fl3_9, fl3_11]
  simp only [sg3_w5_3, sg3_w5_5, sg3_w5_9, sg3_w5_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex3_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w4 = - star (c y0) * d z3 - star (c y2) * d z5 - star (c y6) * d z9 - star (c y8) * d z11 := by
  unfold offSum
  rw [incidence3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl3_3, fl3_5, fl3_9, fl3_11]
  simp only [sg3_w4_3, sg3_w4_5, sg3_w4_9, sg3_w4_11, SixQubit.signMul_true]
  try ring

theorem ex3_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w3 = star (c y0) * d z3 - star (c y2) * d z5 + star (c y6) * d z9 - star (c y8) * d z11 := by
  unfold offSum
  rw [incidence3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl3_3, fl3_5, fl3_9, fl3_11]
  simp only [sg3_w3_3, sg3_w3_5, sg3_w3_9, sg3_w3_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex3_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w2 = star (c y0) * d z3 - star (c y2) * d z5 + star (c y6) * d z9 - star (c y8) * d z11 := by
  unfold offSum
  rw [incidence3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl3_3, fl3_5, fl3_9, fl3_11]
  simp only [sg3_w2_3, sg3_w2_5, sg3_w2_9, sg3_w2_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex3_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w1 = star (c y0) * d z3 - star (c y2) * d z5 + star (c y6) * d z9 - star (c y8) * d z11 := by
  unfold offSum
  rw [incidence3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl3_3, fl3_5, fl3_9, fl3_11]
  simp only [sg3_w1_3, sg3_w1_5, sg3_w1_9, sg3_w1_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex4_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w0 = star (c y0) * d z4 + star (c y1) * d z5 + star (c y6) * d z10 + star (c y7) * d z11 := by
  unfold offSum
  rw [incidence4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl4_4, fl4_5, fl4_10, fl4_11]
  simp only [sg4_w0_4, sg4_w0_5, sg4_w0_10, sg4_w0_11, SixQubit.signMul_false]
  try ring

theorem ex4_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w6 = star (c y0) * d z4 + star (c y1) * d z5 - star (c y6) * d z10 - star (c y7) * d z11 := by
  unfold offSum
  rw [incidence4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl4_4, fl4_5, fl4_10, fl4_11]
  simp only [sg4_w6_4, sg4_w6_5, sg4_w6_10, sg4_w6_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex4_w5 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w5 = - star (c y0) * d z4 - star (c y1) * d z5 - star (c y6) * d z10 - star (c y7) * d z11 := by
  unfold offSum
  rw [incidence4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl4_4, fl4_5, fl4_10, fl4_11]
  simp only [sg4_w5_4, sg4_w5_5, sg4_w5_10, sg4_w5_11, SixQubit.signMul_true]
  try ring

theorem ex4_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w4 = star (c y0) * d z4 - star (c y1) * d z5 + star (c y6) * d z10 - star (c y7) * d z11 := by
  unfold offSum
  rw [incidence4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl4_4, fl4_5, fl4_10, fl4_11]
  simp only [sg4_w4_4, sg4_w4_5, sg4_w4_10, sg4_w4_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex4_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w3 = star (c y0) * d z4 - star (c y1) * d z5 + star (c y6) * d z10 - star (c y7) * d z11 := by
  unfold offSum
  rw [incidence4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl4_4, fl4_5, fl4_10, fl4_11]
  simp only [sg4_w3_4, sg4_w3_5, sg4_w3_10, sg4_w3_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex4_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w2 = star (c y0) * d z4 - star (c y1) * d z5 + star (c y6) * d z10 - star (c y7) * d z11 := by
  unfold offSum
  rw [incidence4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl4_4, fl4_5, fl4_10, fl4_11]
  simp only [sg4_w2_4, sg4_w2_5, sg4_w2_10, sg4_w2_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex4_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w1 = star (c y0) * d z4 - star (c y1) * d z5 + star (c y6) * d z10 - star (c y7) * d z11 := by
  unfold offSum
  rw [incidence4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl4_4, fl4_5, fl4_10, fl4_11]
  simp only [sg4_w1_4, sg4_w1_5, sg4_w1_10, sg4_w1_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex6_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w0 = star (c y6) * d z0 + star (c y11) * d z5 + star (c y0) * d z6 + star (c y5) * d z11 := by
  unfold offSum
  rw [incidence6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl6_0, fl6_5, fl6_6, fl6_11]
  simp only [sg6_w0_0, sg6_w0_5, sg6_w0_6, sg6_w0_11, SixQubit.signMul_false]
  try ring

theorem ex6_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w6 = star (c y6) * d z0 + star (c y11) * d z5 - star (c y0) * d z6 - star (c y5) * d z11 := by
  unfold offSum
  rw [incidence6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl6_0, fl6_5, fl6_6, fl6_11]
  simp only [sg6_w6_0, sg6_w6_5, sg6_w6_6, sg6_w6_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex6_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w1 = - star (c y6) * d z0 - star (c y11) * d z5 - star (c y0) * d z6 - star (c y5) * d z11 := by
  unfold offSum
  rw [incidence6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl6_0, fl6_5, fl6_6, fl6_11]
  simp only [sg6_w1_0, sg6_w1_5, sg6_w1_6, sg6_w1_11, SixQubit.signMul_true]
  try ring

theorem ex6_w7 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w7 = - star (c y6) * d z0 - star (c y11) * d z5 + star (c y0) * d z6 + star (c y5) * d z11 := by
  unfold offSum
  rw [incidence6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl6_0, fl6_5, fl6_6, fl6_11]
  simp only [sg6_w7_0, sg6_w7_5, sg6_w7_6, sg6_w7_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex7_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef7 w0 = star (c y6) * d z1 + star (c y10) * d z5 + star (c y0) * d z7 + star (c y4) * d z11 := by
  unfold offSum
  rw [incidence7]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl7_1, fl7_5, fl7_7, fl7_11]
  simp only [sg7_w0_1, sg7_w0_5, sg7_w0_7, sg7_w0_11, SixQubit.signMul_false]
  try ring

theorem ex7_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef7 w6 = star (c y6) * d z1 + star (c y10) * d z5 - star (c y0) * d z7 - star (c y4) * d z11 := by
  unfold offSum
  rw [incidence7]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl7_1, fl7_5, fl7_7, fl7_11]
  simp only [sg7_w6_1, sg7_w6_5, sg7_w6_7, sg7_w6_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex7_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef7 w2 = - star (c y6) * d z1 - star (c y10) * d z5 - star (c y0) * d z7 - star (c y4) * d z11 := by
  unfold offSum
  rw [incidence7]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl7_1, fl7_5, fl7_7, fl7_11]
  simp only [sg7_w2_1, sg7_w2_5, sg7_w2_7, sg7_w2_11, SixQubit.signMul_true]
  try ring

theorem ex7_w8 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef7 w8 = - star (c y6) * d z1 - star (c y10) * d z5 + star (c y0) * d z7 + star (c y4) * d z11 := by
  unfold offSum
  rw [incidence7]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl7_1, fl7_5, fl7_7, fl7_11]
  simp only [sg7_w8_1, sg7_w8_5, sg7_w8_7, sg7_w8_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex8_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef8 w0 = star (c y6) * d z2 + star (c y9) * d z5 + star (c y0) * d z8 + star (c y3) * d z11 := by
  unfold offSum
  rw [incidence8]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl8_2, fl8_5, fl8_8, fl8_11]
  simp only [sg8_w0_2, sg8_w0_5, sg8_w0_8, sg8_w0_11, SixQubit.signMul_false]
  try ring

theorem ex8_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef8 w6 = star (c y6) * d z2 + star (c y9) * d z5 - star (c y0) * d z8 - star (c y3) * d z11 := by
  unfold offSum
  rw [incidence8]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl8_2, fl8_5, fl8_8, fl8_11]
  simp only [sg8_w6_2, sg8_w6_5, sg8_w6_8, sg8_w6_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex8_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef8 w3 = - star (c y6) * d z2 - star (c y9) * d z5 - star (c y0) * d z8 - star (c y3) * d z11 := by
  unfold offSum
  rw [incidence8]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl8_2, fl8_5, fl8_8, fl8_11]
  simp only [sg8_w3_2, sg8_w3_5, sg8_w3_8, sg8_w3_11, SixQubit.signMul_true]
  try ring

theorem ex8_w9 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef8 w9 = - star (c y6) * d z2 - star (c y9) * d z5 + star (c y0) * d z8 + star (c y3) * d z11 := by
  unfold offSum
  rw [incidence8]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl8_2, fl8_5, fl8_8, fl8_11]
  simp only [sg8_w9_2, sg8_w9_5, sg8_w9_8, sg8_w9_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex9_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef9 w0 = star (c y6) * d z3 + star (c y8) * d z5 + star (c y0) * d z9 + star (c y2) * d z11 := by
  unfold offSum
  rw [incidence9]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl9_3, fl9_5, fl9_9, fl9_11]
  simp only [sg9_w0_3, sg9_w0_5, sg9_w0_9, sg9_w0_11, SixQubit.signMul_false]
  try ring

theorem ex9_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef9 w6 = star (c y6) * d z3 + star (c y8) * d z5 - star (c y0) * d z9 - star (c y2) * d z11 := by
  unfold offSum
  rw [incidence9]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl9_3, fl9_5, fl9_9, fl9_11]
  simp only [sg9_w6_3, sg9_w6_5, sg9_w6_9, sg9_w6_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex9_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef9 w4 = - star (c y6) * d z3 - star (c y8) * d z5 - star (c y0) * d z9 - star (c y2) * d z11 := by
  unfold offSum
  rw [incidence9]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl9_3, fl9_5, fl9_9, fl9_11]
  simp only [sg9_w4_3, sg9_w4_5, sg9_w4_9, sg9_w4_11, SixQubit.signMul_true]
  try ring

theorem ex9_w10 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef9 w10 = - star (c y6) * d z3 - star (c y8) * d z5 + star (c y0) * d z9 + star (c y2) * d z11 := by
  unfold offSum
  rw [incidence9]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl9_3, fl9_5, fl9_9, fl9_11]
  simp only [sg9_w10_3, sg9_w10_5, sg9_w10_9, sg9_w10_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex10_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef10 w0 = star (c y6) * d z4 + star (c y7) * d z5 + star (c y0) * d z10 + star (c y1) * d z11 := by
  unfold offSum
  rw [incidence10]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl10_4, fl10_5, fl10_10, fl10_11]
  simp only [sg10_w0_4, sg10_w0_5, sg10_w0_10, sg10_w0_11, SixQubit.signMul_false]
  try ring

theorem ex10_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef10 w6 = star (c y6) * d z4 + star (c y7) * d z5 - star (c y0) * d z10 - star (c y1) * d z11 := by
  unfold offSum
  rw [incidence10]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl10_4, fl10_5, fl10_10, fl10_11]
  simp only [sg10_w6_4, sg10_w6_5, sg10_w6_10, sg10_w6_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex10_w5 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef10 w5 = - star (c y6) * d z4 - star (c y7) * d z5 - star (c y0) * d z10 - star (c y1) * d z11 := by
  unfold offSum
  rw [incidence10]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl10_4, fl10_5, fl10_10, fl10_11]
  simp only [sg10_w5_4, sg10_w5_5, sg10_w5_10, sg10_w5_11, SixQubit.signMul_true]
  try ring

theorem ex10_w11 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef10 w11 = - star (c y6) * d z4 - star (c y7) * d z5 + star (c y0) * d z10 + star (c y1) * d z11 := by
  unfold offSum
  rw [incidence10]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl10_4, fl10_5, fl10_10, fl10_11]
  simp only [sg10_w11_4, sg10_w11_5, sg10_w11_10, sg10_w11_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

/-! ## Hub links -/

/-- Point y1 is tied to the hub y0. -/
theorem hb1 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef10 w0 = 0)
    (h1 : offSum c d ef10 w6 = 0)
    : star (c y0) * d z10 + star (c y1) * d z11 = 0 := by
  rw [ex10_w0] at h0
  rw [ex10_w6] at h1
  linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1

/-- Point y2 is tied to the hub y0. -/
theorem hb2 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef9 w0 = 0)
    (h1 : offSum c d ef9 w6 = 0)
    : star (c y0) * d z9 + star (c y2) * d z11 = 0 := by
  rw [ex9_w0] at h0
  rw [ex9_w6] at h1
  linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1

/-- Point y3 is tied to the hub y0. -/
theorem hb3 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef8 w0 = 0)
    (h1 : offSum c d ef8 w6 = 0)
    : star (c y0) * d z8 + star (c y3) * d z11 = 0 := by
  rw [ex8_w0] at h0
  rw [ex8_w6] at h1
  linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1

/-- Point y4 is tied to the hub y0. -/
theorem hb4 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef7 w0 = 0)
    (h1 : offSum c d ef7 w6 = 0)
    : star (c y0) * d z7 + star (c y4) * d z11 = 0 := by
  rw [ex7_w0] at h0
  rw [ex7_w6] at h1
  linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1

/-- Point y5 is tied to the hub y0. -/
theorem hb5 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef6 w0 = 0)
    (h1 : offSum c d ef6 w6 = 0)
    : star (c y0) * d z6 + star (c y5) * d z11 = 0 := by
  rw [ex6_w0] at h0
  rw [ex6_w6] at h1
  linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1

/-- Point y7 is tied to the hub y0. -/
theorem hb7 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef4 w6 = 0)
    (h1 : offSum c d ef4 w4 = 0)
    : star (c y0) * d z4 - star (c y7) * d z11 = 0 := by
  rw [ex4_w6] at h0
  rw [ex4_w4] at h1
  linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- Point y8 is tied to the hub y0. -/
theorem hb8 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef3 w6 = 0)
    (h1 : offSum c d ef3 w5 = 0)
    : star (c y0) * d z3 - star (c y8) * d z11 = 0 := by
  rw [ex3_w6] at h0
  rw [ex3_w5] at h1
  linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- Point y9 is tied to the hub y0. -/
theorem hb9 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef2 w6 = 0)
    (h1 : offSum c d ef2 w5 = 0)
    : star (c y0) * d z2 - star (c y9) * d z11 = 0 := by
  rw [ex2_w6] at h0
  rw [ex2_w5] at h1
  linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- Point y10 is tied to the hub y0. -/
theorem hb10 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef1 w6 = 0)
    (h1 : offSum c d ef1 w5 = 0)
    : star (c y0) * d z1 - star (c y10) * d z11 = 0 := by
  rw [ex1_w6] at h0
  rw [ex1_w5] at h1
  linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- Point y11 is tied to the hub y0. -/
theorem hb11 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef0 w6 = 0)
    (h1 : offSum c d ef0 w5 = 0)
    : star (c y0) * d z0 - star (c y11) * d z11 = 0 := by
  rw [ex0_w6] at h0
  rw [ex0_w5] at h1
  linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-! ## Reaching the sixth point -/

/-- Point y6 is not linked to the hub directly.  One transitivity step through
y9 supplies it; the multiplier is the product at y9, nonzero because both its
probabilities are positive. -/
theorem hb6 (c d : SS.BitString 6 -> ℂ)
    (h9 : star (c y0) * d z2 - star (c y9) * d z11 = 0)
    (h69 : star (c y6) * d z2 + star (c y9) * d z5 = 0)
    (hm : star (c y9) * d z2 ≠ 0)
    : star (c y0) * d z5 + star (c y6) * d z11 = 0 := by
  have key : (star (c y0) * d z5 + star (c y6) * d z11) *
      (star (c y9) * d z2) = 0 := by
    linear_combination (d z5 * star (c y9)) * h9
      + (star (c y9) * d z11) * h69
  rcases mul_eq_zero.mp key with h | h
  · exact h
  · exact absurd h hm

/-! ## The bottom relations -/

/-- Cross relation 1, pushed onto the bottom fiber. -/
theorem bot1 (c d : SS.BitString 6 -> ℂ)
    (hx : star (c y0) * d z4 + star (c y1) * d z5 = 0)
    (ha : star (c y0) * d z4 - star (c y7) * d z11 = 0)
    (hb : star (c y0) * d z5 + star (c y6) * d z11 = 0)
    (hv : d z11 ≠ 0)
    : star (c y0) * star (c y7) - star (c y1) * star (c y6) = 0 := by
  have key : (star (c y0) * star (c y7) - star (c y1) * star (c y6)) *
      d z11 = 0 := by
    linear_combination (star (c y0)) * hx - (star (c y0)) * ha
      - (star (c y1)) * hb
  rcases mul_eq_zero.mp key with h | h
  · exact h
  · exact absurd h hv

/-- Cross relation 2, pushed onto the bottom fiber. -/
theorem bot2 (c d : SS.BitString 6 -> ℂ)
    (hx : star (c y0) * d z3 + star (c y2) * d z5 = 0)
    (ha : star (c y0) * d z3 - star (c y8) * d z11 = 0)
    (hb : star (c y0) * d z5 + star (c y6) * d z11 = 0)
    (hv : d z11 ≠ 0)
    : star (c y0) * star (c y8) - star (c y2) * star (c y6) = 0 := by
  have key : (star (c y0) * star (c y8) - star (c y2) * star (c y6)) *
      d z11 = 0 := by
    linear_combination (star (c y0)) * hx - (star (c y0)) * ha
      - (star (c y2)) * hb
  rcases mul_eq_zero.mp key with h | h
  · exact h
  · exact absurd h hv

/-- Cross relation 3, pushed onto the bottom fiber. -/
theorem bot3 (c d : SS.BitString 6 -> ℂ)
    (hx : star (c y0) * d z2 + star (c y3) * d z5 = 0)
    (ha : star (c y0) * d z2 - star (c y9) * d z11 = 0)
    (hb : star (c y0) * d z5 + star (c y6) * d z11 = 0)
    (hv : d z11 ≠ 0)
    : star (c y0) * star (c y9) - star (c y3) * star (c y6) = 0 := by
  have key : (star (c y0) * star (c y9) - star (c y3) * star (c y6)) *
      d z11 = 0 := by
    linear_combination (star (c y0)) * hx - (star (c y0)) * ha
      - (star (c y3)) * hb
  rcases mul_eq_zero.mp key with h | h
  · exact h
  · exact absurd h hv

/-- Cross relation 4, pushed onto the bottom fiber. -/
theorem bot4 (c d : SS.BitString 6 -> ℂ)
    (hx : star (c y0) * d z1 + star (c y4) * d z5 = 0)
    (ha : star (c y0) * d z1 - star (c y10) * d z11 = 0)
    (hb : star (c y0) * d z5 + star (c y6) * d z11 = 0)
    (hv : d z11 ≠ 0)
    : star (c y0) * star (c y10) - star (c y4) * star (c y6) = 0 := by
  have key : (star (c y0) * star (c y10) - star (c y4) * star (c y6)) *
      d z11 = 0 := by
    linear_combination (star (c y0)) * hx - (star (c y0)) * ha
      - (star (c y4)) * hb
  rcases mul_eq_zero.mp key with h | h
  · exact h
  · exact absurd h hv

/-- Cross relation 5, pushed onto the bottom fiber. -/
theorem bot5 (c d : SS.BitString 6 -> ℂ)
    (hx : star (c y0) * d z0 + star (c y5) * d z5 = 0)
    (ha : star (c y0) * d z0 - star (c y11) * d z11 = 0)
    (hb : star (c y0) * d z5 + star (c y6) * d z11 = 0)
    (hv : d z11 ≠ 0)
    : star (c y0) * star (c y11) - star (c y5) * star (c y6) = 0 := by
  have key : (star (c y0) * star (c y11) - star (c y5) * star (c y6)) *
      d z11 = 0 := by
    linear_combination (star (c y0)) * hx - (star (c y0)) * ha
      - (star (c y5)) * hb
  rcases mul_eq_zero.mp key with h | h
  · exact h
  · exact absurd h hv

/-! ## The coherence identities -/

/-- From `u_0 u_w = u_x u_6` to `q_0 D = q_x A`, stated with `star z * z` so
that `ring` sees the products directly. -/
theorem drel (c : SS.BitString 6 -> ℂ) (x w : SS.BitString 6)
    (hb : star (c y0) * star (c w) - star (c x) * star (c y6) = 0)
    : (star (c y0) * c y0) * (star (c x) * c w)
      = (star (c x) * c x) * (star (c y0) * c y6) := by
  have hc : c y0 * c w - c x * c y6 = 0 := by
    simpa using congrArg star hb
  linear_combination (star (c y0) * star (c x)) * hc

/-- From two hub links to `q_0 E = - r * D`. -/
theorem erel (c d : SS.BitString 6 -> ℂ) (x w : SS.BitString 6)
    (ya yb : SS.BitString 6)
    (ha : star (c y0) * d ya - star (c x) * d z11 = 0)
    (hb : star (c y0) * d yb + star (c w) * d z11 = 0)
    : (star (c y0) * c y0) * (star (d ya) * d yb)
      = -((star (c w) * c x) * (star (d z11) * d z11)) := by
  have hac : c y0 * star (d ya) - c x * star (d z11) = 0 := by
    simpa using congrArg star ha
  linear_combination (star (c y0) * d yb) * hac
    + (c x * star (d z11)) * hb

/-- `star z * z` is the squared modulus. -/
theorem sq (z : ℂ) : star z * z = (Complex.normSq z : ℂ) := by
  rw [Complex.normSq_eq_conj_mul_self]; rfl

/-! ## The diagonal expansions -/

theorem dbot_w0 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef5 w0 = star (c y6) * c y0 + star (c y7) * c y1 + star (c y8) * c y2 + star (c y9) * c y3 + star (c y10) * c y4 + star (c y11) * c y5 + star (c y0) * c y6 + star (c y1) * c y7 + star (c y2) * c y8 + star (c y3) * c y9 + star (c y4) * c y10 + star (c y5) * c y11 := by
  unfold diagBot
  rw [diagB_inc]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfb0, dfb1, dfb2, dfb3, dfb4, dfb5, dfb6, dfb7, dfb8, dfb9, dfb10, dfb11]
  simp only [dsbw0_0, dsbw0_1, dsbw0_2, dsbw0_3, dsbw0_4, dsbw0_5, dsbw0_6, dsbw0_7, dsbw0_8, dsbw0_9, dsbw0_10, dsbw0_11, SixQubit.signMul_false]
  try ring

theorem dtop_w0 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef5 w0 = star (d z6) * d z0 + star (d z7) * d z1 + star (d z8) * d z2 + star (d z9) * d z3 + star (d z10) * d z4 + star (d z11) * d z5 + star (d z0) * d z6 + star (d z1) * d z7 + star (d z2) * d z8 + star (d z3) * d z9 + star (d z4) * d z10 + star (d z5) * d z11 := by
  unfold diagTop
  rw [diagT_inc]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dft0, dft1, dft2, dft3, dft4, dft5, dft6, dft7, dft8, dft9, dft10, dft11]
  simp only [dstw0_0, dstw0_1, dstw0_2, dstw0_3, dstw0_4, dstw0_5, dstw0_6, dstw0_7, dstw0_8, dstw0_9, dstw0_10, dstw0_11, SixQubit.signMul_false]
  try ring

theorem dbot_w6 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef5 w6 = star (c y6) * c y0 + star (c y7) * c y1 + star (c y8) * c y2 + star (c y9) * c y3 + star (c y10) * c y4 + star (c y11) * c y5 - star (c y0) * c y6 - star (c y1) * c y7 - star (c y2) * c y8 - star (c y3) * c y9 - star (c y4) * c y10 - star (c y5) * c y11 := by
  unfold diagBot
  rw [diagB_inc]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfb0, dfb1, dfb2, dfb3, dfb4, dfb5, dfb6, dfb7, dfb8, dfb9, dfb10, dfb11]
  simp only [dsbw6_0, dsbw6_1, dsbw6_2, dsbw6_3, dsbw6_4, dsbw6_5, dsbw6_6, dsbw6_7, dsbw6_8, dsbw6_9, dsbw6_10, dsbw6_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dtop_w6 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef5 w6 = star (d z6) * d z0 + star (d z7) * d z1 + star (d z8) * d z2 + star (d z9) * d z3 + star (d z10) * d z4 + star (d z11) * d z5 - star (d z0) * d z6 - star (d z1) * d z7 - star (d z2) * d z8 - star (d z3) * d z9 - star (d z4) * d z10 - star (d z5) * d z11 := by
  unfold diagTop
  rw [diagT_inc]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dft0, dft1, dft2, dft3, dft4, dft5, dft6, dft7, dft8, dft9, dft10, dft11]
  simp only [dstw6_0, dstw6_1, dstw6_2, dstw6_3, dstw6_4, dstw6_5, dstw6_6, dstw6_7, dstw6_8, dstw6_9, dstw6_10, dstw6_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

/-! ## The anchor coherence at k = 5 -/

/-- The last coherence needs only the single link at y6. -/
theorem erel5 (c d : SS.BitString 6 -> ℂ)
    (hb : star (c y0) * d z5 + star (c y6) * d z11 = 0)
    : (star (c y0) * c y0) * (star (d z5) * d z11)
      = -((star (c y0) * c y6) * (star (d z11) * d z11)) := by
  have hbc : c y0 * star (d z5) + c y6 * star (d z11) = 0 := by
    simpa using congrArg star hb
  linear_combination (star (c y0) * d z11) * hbc

/-! ## The cross relations behind the pinning -/

/-- Cross relation 0, from mask 010000. -/
theorem xr0 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef4 w0 = 0)
    (h1 : offSum c d ef4 w4 = 0)
    : star (c y0) * d z4 + star (c y6) * d z10 = 0 := by
  rw [ex4_w0] at h0
  rw [ex4_w4] at h1
  linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- Its squared modulus. -/
theorem xq0 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef4 w0 = 0)
    (h1 : offSum c d ef4 w4 = 0)
    : Complex.normSq (c y0) * Complex.normSq (d z4)
      = Complex.normSq (c y6) * Complex.normSq (d z10) := by
  have hr := xr0 c d h0 h1
  have he : star (c y0) * d z4 = -(star (c y6) * d z10) := by
    linear_combination hr
  simpa [Complex.normSq_mul] using congrArg Complex.normSq he

/-- Cross relation 1, from mask 010000. -/
theorem xr1 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef4 w0 = 0)
    (h1 : offSum c d ef4 w4 = 0)
    : star (c y1) * d z5 + star (c y7) * d z11 = 0 := by
  rw [ex4_w0] at h0
  rw [ex4_w4] at h1
  linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1

/-- Its squared modulus. -/
theorem xq1 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef4 w0 = 0)
    (h1 : offSum c d ef4 w4 = 0)
    : Complex.normSq (c y1) * Complex.normSq (d z5)
      = Complex.normSq (c y7) * Complex.normSq (d z11) := by
  have hr := xr1 c d h0 h1
  have he : star (c y1) * d z5 = -(star (c y7) * d z11) := by
    linear_combination hr
  simpa [Complex.normSq_mul] using congrArg Complex.normSq he

/-- Cross relation 2, from mask 001000. -/
theorem xr2 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef3 w0 = 0)
    (h1 : offSum c d ef3 w5 = 0)
    : star (c y0) * d z3 + star (c y6) * d z9 = 0 := by
  rw [ex3_w0] at h0
  rw [ex3_w5] at h1
  linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- Its squared modulus. -/
theorem xq2 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef3 w0 = 0)
    (h1 : offSum c d ef3 w5 = 0)
    : Complex.normSq (c y0) * Complex.normSq (d z3)
      = Complex.normSq (c y6) * Complex.normSq (d z9) := by
  have hr := xr2 c d h0 h1
  have he : star (c y0) * d z3 = -(star (c y6) * d z9) := by
    linear_combination hr
  simpa [Complex.normSq_mul] using congrArg Complex.normSq he

/-- Cross relation 3, from mask 001000. -/
theorem xr3 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef3 w0 = 0)
    (h1 : offSum c d ef3 w5 = 0)
    : star (c y2) * d z5 + star (c y8) * d z11 = 0 := by
  rw [ex3_w0] at h0
  rw [ex3_w5] at h1
  linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1

/-- Its squared modulus. -/
theorem xq3 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef3 w0 = 0)
    (h1 : offSum c d ef3 w5 = 0)
    : Complex.normSq (c y2) * Complex.normSq (d z5)
      = Complex.normSq (c y8) * Complex.normSq (d z11) := by
  have hr := xr3 c d h0 h1
  have he : star (c y2) * d z5 = -(star (c y8) * d z11) := by
    linear_combination hr
  simpa [Complex.normSq_mul] using congrArg Complex.normSq he

/-- Cross relation 4, from mask 000100. -/
theorem xr4 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef2 w0 = 0)
    (h1 : offSum c d ef2 w5 = 0)
    : star (c y0) * d z2 + star (c y6) * d z8 = 0 := by
  rw [ex2_w0] at h0
  rw [ex2_w5] at h1
  linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- Its squared modulus. -/
theorem xq4 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef2 w0 = 0)
    (h1 : offSum c d ef2 w5 = 0)
    : Complex.normSq (c y0) * Complex.normSq (d z2)
      = Complex.normSq (c y6) * Complex.normSq (d z8) := by
  have hr := xr4 c d h0 h1
  have he : star (c y0) * d z2 = -(star (c y6) * d z8) := by
    linear_combination hr
  simpa [Complex.normSq_mul] using congrArg Complex.normSq he

/-- Cross relation 5, from mask 000100. -/
theorem xr5 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef2 w0 = 0)
    (h1 : offSum c d ef2 w5 = 0)
    : star (c y3) * d z5 + star (c y9) * d z11 = 0 := by
  rw [ex2_w0] at h0
  rw [ex2_w5] at h1
  linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1

/-- Its squared modulus. -/
theorem xq5 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef2 w0 = 0)
    (h1 : offSum c d ef2 w5 = 0)
    : Complex.normSq (c y3) * Complex.normSq (d z5)
      = Complex.normSq (c y9) * Complex.normSq (d z11) := by
  have hr := xr5 c d h0 h1
  have he : star (c y3) * d z5 = -(star (c y9) * d z11) := by
    linear_combination hr
  simpa [Complex.normSq_mul] using congrArg Complex.normSq he

/-- Cross relation 6, from mask 000010. -/
theorem xr6 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef1 w0 = 0)
    (h1 : offSum c d ef1 w5 = 0)
    : star (c y0) * d z1 + star (c y6) * d z7 = 0 := by
  rw [ex1_w0] at h0
  rw [ex1_w5] at h1
  linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- Its squared modulus. -/
theorem xq6 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef1 w0 = 0)
    (h1 : offSum c d ef1 w5 = 0)
    : Complex.normSq (c y0) * Complex.normSq (d z1)
      = Complex.normSq (c y6) * Complex.normSq (d z7) := by
  have hr := xr6 c d h0 h1
  have he : star (c y0) * d z1 = -(star (c y6) * d z7) := by
    linear_combination hr
  simpa [Complex.normSq_mul] using congrArg Complex.normSq he

/-- Cross relation 7, from mask 000010. -/
theorem xr7 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef1 w0 = 0)
    (h1 : offSum c d ef1 w5 = 0)
    : star (c y4) * d z5 + star (c y10) * d z11 = 0 := by
  rw [ex1_w0] at h0
  rw [ex1_w5] at h1
  linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1

/-- Its squared modulus. -/
theorem xq7 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef1 w0 = 0)
    (h1 : offSum c d ef1 w5 = 0)
    : Complex.normSq (c y4) * Complex.normSq (d z5)
      = Complex.normSq (c y10) * Complex.normSq (d z11) := by
  have hr := xr7 c d h0 h1
  have he : star (c y4) * d z5 = -(star (c y10) * d z11) := by
    linear_combination hr
  simpa [Complex.normSq_mul] using congrArg Complex.normSq he

/-- Cross relation 8, from mask 000001. -/
theorem xr8 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef0 w0 = 0)
    (h1 : offSum c d ef0 w5 = 0)
    : star (c y0) * d z0 + star (c y6) * d z6 = 0 := by
  rw [ex0_w0] at h0
  rw [ex0_w5] at h1
  linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- Its squared modulus. -/
theorem xq8 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef0 w0 = 0)
    (h1 : offSum c d ef0 w5 = 0)
    : Complex.normSq (c y0) * Complex.normSq (d z0)
      = Complex.normSq (c y6) * Complex.normSq (d z6) := by
  have hr := xr8 c d h0 h1
  have he : star (c y0) * d z0 = -(star (c y6) * d z6) := by
    linear_combination hr
  simpa [Complex.normSq_mul] using congrArg Complex.normSq he

/-- Cross relation 9, from mask 000001. -/
theorem xr9 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef0 w0 = 0)
    (h1 : offSum c d ef0 w5 = 0)
    : star (c y5) * d z5 + star (c y11) * d z11 = 0 := by
  rw [ex0_w0] at h0
  rw [ex0_w5] at h1
  linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1

/-- Its squared modulus. -/
theorem xq9 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef0 w0 = 0)
    (h1 : offSum c d ef0 w5 = 0)
    : Complex.normSq (c y5) * Complex.normSq (d z5)
      = Complex.normSq (c y11) * Complex.normSq (d z11) := by
  have hr := xr9 c d h0 h1
  have he : star (c y5) * d z5 = -(star (c y11) * d z11) := by
    linear_combination hr
  simpa [Complex.normSq_mul] using congrArg Complex.normSq he

/-! ## The cross relations used by the bottom step -/

/-- The cross relation pairing y0 with y7 and y1 with y6. -/
theorem cr1 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef4 w0 = 0)
    (h1 : offSum c d ef4 w6 = 0)
    : star (c y0) * d z4 + star (c y1) * d z5 = 0 := by
  rw [ex4_w0] at h0
  rw [ex4_w6] at h1
  linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- The cross relation pairing y0 with y8 and y2 with y6. -/
theorem cr2 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef3 w0 = 0)
    (h1 : offSum c d ef3 w6 = 0)
    : star (c y0) * d z3 + star (c y2) * d z5 = 0 := by
  rw [ex3_w0] at h0
  rw [ex3_w6] at h1
  linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- The cross relation pairing y0 with y9 and y3 with y6. -/
theorem cr3 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef2 w0 = 0)
    (h1 : offSum c d ef2 w6 = 0)
    : star (c y0) * d z2 + star (c y3) * d z5 = 0 := by
  rw [ex2_w0] at h0
  rw [ex2_w6] at h1
  linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- The cross relation pairing y0 with y10 and y4 with y6. -/
theorem cr4 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef1 w0 = 0)
    (h1 : offSum c d ef1 w6 = 0)
    : star (c y0) * d z1 + star (c y4) * d z5 = 0 := by
  rw [ex1_w0] at h0
  rw [ex1_w6] at h1
  linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- The cross relation pairing y0 with y11 and y5 with y6. -/
theorem cr5 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef0 w0 = 0)
    (h1 : offSum c d ef0 w6 = 0)
    : star (c y0) * d z0 + star (c y5) * d z5 = 0 := by
  rw [ex0_w0] at h0
  rw [ex0_w6] at h1
  linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- The link joining y6 and y9, the bridge the hub cannot reach directly. -/
theorem l69 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef8 w0 = 0)
    (h1 : offSum c d ef8 w6 = 0)
    : star (c y6) * d z2 + star (c y9) * d z5 = 0 := by
  rw [ex8_w0] at h0
  rw [ex8_w6] at h1
  linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-! ## The no-go -/

set_option maxHeartbeats 4000000 in
/-- **Orbit 25 is impossible.** -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)))
    (E0_w0 : offSum c d ef0 w0 = 0)
    (E0_w6 : offSum c d ef0 w6 = 0)
    (E0_w5 : offSum c d ef0 w5 = 0)
    (_E0_w4 : offSum c d ef0 w4 = 0)
    (_E0_w3 : offSum c d ef0 w3 = 0)
    (_E0_w2 : offSum c d ef0 w2 = 0)
    (_E0_w1 : offSum c d ef0 w1 = 0)
    (E1_w0 : offSum c d ef1 w0 = 0)
    (E1_w6 : offSum c d ef1 w6 = 0)
    (E1_w5 : offSum c d ef1 w5 = 0)
    (_E1_w4 : offSum c d ef1 w4 = 0)
    (_E1_w3 : offSum c d ef1 w3 = 0)
    (_E1_w2 : offSum c d ef1 w2 = 0)
    (_E1_w1 : offSum c d ef1 w1 = 0)
    (E2_w0 : offSum c d ef2 w0 = 0)
    (E2_w6 : offSum c d ef2 w6 = 0)
    (E2_w5 : offSum c d ef2 w5 = 0)
    (_E2_w4 : offSum c d ef2 w4 = 0)
    (_E2_w3 : offSum c d ef2 w3 = 0)
    (_E2_w2 : offSum c d ef2 w2 = 0)
    (_E2_w1 : offSum c d ef2 w1 = 0)
    (E3_w0 : offSum c d ef3 w0 = 0)
    (E3_w6 : offSum c d ef3 w6 = 0)
    (E3_w5 : offSum c d ef3 w5 = 0)
    (_E3_w4 : offSum c d ef3 w4 = 0)
    (_E3_w3 : offSum c d ef3 w3 = 0)
    (_E3_w2 : offSum c d ef3 w2 = 0)
    (_E3_w1 : offSum c d ef3 w1 = 0)
    (E4_w0 : offSum c d ef4 w0 = 0)
    (E4_w6 : offSum c d ef4 w6 = 0)
    (_E4_w5 : offSum c d ef4 w5 = 0)
    (E4_w4 : offSum c d ef4 w4 = 0)
    (_E4_w3 : offSum c d ef4 w3 = 0)
    (_E4_w2 : offSum c d ef4 w2 = 0)
    (_E4_w1 : offSum c d ef4 w1 = 0)
    (E6_w0 : offSum c d ef6 w0 = 0)
    (E6_w6 : offSum c d ef6 w6 = 0)
    (_E6_w1 : offSum c d ef6 w1 = 0)
    (_E6_w7 : offSum c d ef6 w7 = 0)
    (E7_w0 : offSum c d ef7 w0 = 0)
    (E7_w6 : offSum c d ef7 w6 = 0)
    (_E7_w2 : offSum c d ef7 w2 = 0)
    (_E7_w8 : offSum c d ef7 w8 = 0)
    (E8_w0 : offSum c d ef8 w0 = 0)
    (E8_w6 : offSum c d ef8 w6 = 0)
    (_E8_w3 : offSum c d ef8 w3 = 0)
    (_E8_w9 : offSum c d ef8 w9 = 0)
    (E9_w0 : offSum c d ef9 w0 = 0)
    (E9_w6 : offSum c d ef9 w6 = 0)
    (_E9_w4 : offSum c d ef9 w4 = 0)
    (_E9_w10 : offSum c d ef9 w10 = 0)
    (E10_w0 : offSum c d ef10 w0 = 0)
    (E10_w6 : offSum c d ef10 w6 = 0)
    (_E10_w5 : offSum c d ef10 w5 = 0)
    (_E10_w11 : offSum c d ef10 w11 = 0)
    (Dg0 : diagBot c ef5 w0 = diagTop d ef5 w0)
    (Dg1 : diagBot c ef5 w6 = diagTop d ef5 w6)
    : False := by
  have v0 := lin0 hm (xq0 c d E4_w0 E4_w4)
  have v1 := lin1 hm (xq1 c d E4_w0 E4_w4)
  have v2 := lin2 hm (xq2 c d E3_w0 E3_w5)
  have v3 := lin3 hm (xq3 c d E3_w0 E3_w5)
  have v4 := lin4 hm (xq4 c d E2_w0 E2_w5)
  have v5 := lin5 hm (xq5 c d E2_w0 E2_w5)
  have v6 := lin6 hm (xq6 c d E1_w0 E1_w5)
  have v7 := lin7 hm (xq7 c d E1_w0 E1_w5)
  have v8 := lin8 hm (xq8 c d E0_w0 E0_w5)
  have v9 := lin9 hm (xq9 c d E0_w0 E0_w5)
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23⟩ :=
    pinned hm v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  -- the two nonzero products the argument cancels by
  have nz11 : d z11 ≠ 0 := by
    intro h; rw [h] at p23; norm_num at p23
  have nz9 : star (c y9) * d z2 ≠ 0 := by
    refine mul_ne_zero (star_ne_zero.mpr ?_) ?_
    · intro h; rw [h] at p9; norm_num at p9
    · intro h; rw [h] at p14; norm_num at p14
  -- hub links
  have H1 := hb1 c d E10_w0 E10_w6
  have H2 := hb2 c d E9_w0 E9_w6
  have H3 := hb3 c d E8_w0 E8_w6
  have H4 := hb4 c d E7_w0 E7_w6
  have H5 := hb5 c d E6_w0 E6_w6
  have H7 := hb7 c d E4_w6 E4_w4
  have H8 := hb8 c d E3_w6 E3_w5
  have H9 := hb9 c d E2_w6 E2_w5
  have H10 := hb10 c d E1_w6 E1_w5
  have H11 := hb11 c d E0_w6 E0_w5
  have K69 := l69 c d E8_w0 E8_w6
  have H6 := hb6 c d H9 K69 nz9
  -- the bottom relations
  have C1 := cr1 c d E4_w0 E4_w6
  have B1 := bot1 c d C1 H7 H6 nz11
  have C2 := cr2 c d E3_w0 E3_w6
  have B2 := bot2 c d C2 H8 H6 nz11
  have C3 := cr3 c d E2_w0 E2_w6
  have B3 := bot3 c d C3 H9 H6 nz11
  have C4 := cr4 c d E1_w0 E1_w6
  have B4 := bot4 c d C4 H10 H6 nz11
  have C5 := cr5 c d E0_w0 E0_w6
  have B5 := bot5 c d C5 H11 H6 nz11
  -- squared moduli as numerals
  have s0 : star (c y0) * c y0 = ((3/16 : ℝ) : ℂ) := by
    rw [sq, p0]
  have s6 : star (c y6) * c y6 = ((3/16 : ℝ) : ℂ) := by
    rw [sq, p6]
  have s1 : star (c y1) * c y1 = ((1/16 : ℝ) : ℂ) := by
    rw [sq, p1]
  have s2 : star (c y2) * c y2 = ((1/16 : ℝ) : ℂ) := by
    rw [sq, p2]
  have s3 : star (c y3) * c y3 = ((1/16 : ℝ) : ℂ) := by
    rw [sq, p3]
  have s4 : star (c y4) * c y4 = ((1/16 : ℝ) : ℂ) := by
    rw [sq, p4]
  have s5 : star (c y5) * c y5 = ((1/16 : ℝ) : ℂ) := by
    rw [sq, p5]
  have sr : star (d z11) * d z11 = ((3/16 : ℝ) : ℂ) := by
    rw [sq, p23]
  -- three times each tail coherence is the anchor
  have D1 : (3 : ℂ) * (star (c y1) * c y7) = star (c y0) * c y6 := by
    have t := drel c y1 y7 B1
    rw [s0, s1] at t
    push_cast at t
    linear_combination 16 * t
  have D2 : (3 : ℂ) * (star (c y2) * c y8) = star (c y0) * c y6 := by
    have t := drel c y2 y8 B2
    rw [s0, s2] at t
    push_cast at t
    linear_combination 16 * t
  have D3 : (3 : ℂ) * (star (c y3) * c y9) = star (c y0) * c y6 := by
    have t := drel c y3 y9 B3
    rw [s0, s3] at t
    push_cast at t
    linear_combination 16 * t
  have D4 : (3 : ℂ) * (star (c y4) * c y10) = star (c y0) * c y6 := by
    have t := drel c y4 y10 B4
    rw [s0, s4] at t
    push_cast at t
    linear_combination 16 * t
  have D5 : (3 : ℂ) * (star (c y5) * c y11) = star (c y0) * c y6 := by
    have t := drel c y5 y11 B5
    rw [s0, s5] at t
    push_cast at t
    linear_combination 16 * t
  -- each top coherence is minus a bottom one
  have F0 : star (d z0) * d z6 = -(star (c y5) * c y11) := by
    have t := erel c d y11 y5 z0 z6 H11 H5
    rw [s0, sr] at t
    push_cast at t
    linear_combination (16 / 3 : ℂ) * t
  have F1 : star (d z1) * d z7 = -(star (c y4) * c y10) := by
    have t := erel c d y10 y4 z1 z7 H10 H4
    rw [s0, sr] at t
    push_cast at t
    linear_combination (16 / 3 : ℂ) * t
  have F2 : star (d z2) * d z8 = -(star (c y3) * c y9) := by
    have t := erel c d y9 y3 z2 z8 H9 H3
    rw [s0, sr] at t
    push_cast at t
    linear_combination (16 / 3 : ℂ) * t
  have F3 : star (d z3) * d z9 = -(star (c y2) * c y8) := by
    have t := erel c d y8 y2 z3 z9 H8 H2
    rw [s0, sr] at t
    push_cast at t
    linear_combination (16 / 3 : ℂ) * t
  have F4 : star (d z4) * d z10 = -(star (c y1) * c y7) := by
    have t := erel c d y7 y1 z4 z10 H7 H1
    rw [s0, sr] at t
    push_cast at t
    linear_combination (16 / 3 : ℂ) * t
  have F5 : star (d z5) * d z11 = -(star (c y0) * c y6) := by
    have t := erel5 c d H6
    rw [s0, sr] at t
    push_cast at t
    linear_combination (16 / 3 : ℂ) * t
  -- the diagonal condition
  rw [dbot_w0, dtop_w0] at Dg0
  rw [dbot_w6, dtop_w6] at Dg1
  -- the anchor vanishes
  have hA : star (c y0) * c y6 = 0 := by
    linear_combination (3 / 32 : ℂ) * Dg0 - (3 / 32 : ℂ) * Dg1
      + (3 / 16 : ℂ) * F0 + (3 / 16 : ℂ) * F1 + (3 / 16 : ℂ) * F2 + (3 / 16 : ℂ) * F3 + (3 / 16 : ℂ) * F4 + (3 / 16 : ℂ) * F5
      - (1 / 8 : ℂ) * D1 - (1 / 8 : ℂ) * D2 - (1 / 8 : ℂ) * D3 - (1 / 8 : ℂ) * D4 - (1 / 8 : ℂ) * D5
  have hq : Complex.normSq (c y0) * Complex.normSq (c y6) = 0 := by
    have := congrArg Complex.normSq hA
    simpa [Complex.normSq_mul] using this
  rw [p0, p6] at hq
  norm_num at hq

end

end SixQubit.Orbit25
