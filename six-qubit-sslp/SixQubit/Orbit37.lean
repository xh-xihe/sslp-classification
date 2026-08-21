import Mathlib

import SS.FullKL
import SixQubit.Common

/-!
# Six-qubit no-go for moment orbit 37: the setting

Orbit 37 of `six_qubit_sslp_v7.tex`: q = 5, angle vector
a = (1, 1, 1, 2, 3, 3), residues 0 and 1, closed in Section 17.

The bottom fiber is a star `S`, three points `A_1..A_3`, and a three-by-three
grid `B_ij`; the top fiber is the bitwise complement, so `hat k = 12 - k`.
Fifteen masks matter: three reciprocal pairs `{A_j, S}`, three weight-one
masks `X_1, X_2, X_3` with six incidences each carrying the star and sync
relations of a grid row, and nine permanents with four incidences each.

The permanent collapse rests on a sign fact the incidence list does not
supply: every admissible dressing of a permanent mask gives a UNIFORM sign
vector over its four incidences.  Each permanent mask has weight two, so the
support of any admissible dressing sits inside it, while two reciprocal
partners differ by the complement of the mask; the sign ratio is therefore
`(-1)^(z . complement e) = 1`.  This matters: with opposite relative signs the
collapse would give the two-by-two DETERMINANT rather than the two-by-two
PERMANENT, and the determinant version is satisfied by any rank-one grid, so
no contradiction would follow.  The sign lemmas below are therefore stated
and `decide`-checked one per mask and dressing.

Everything computational is decided by the Lean kernel; `native_decide` is
not used.
-/

namespace SixQubit.Orbit37

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]

def y0 : SS.BitString 6 := bs false false false false false false  -- 000000 = A1
def y1 : SS.BitString 6 := bs false false false true  false true   -- 000101 = A2
def y2 : SS.BitString 6 := bs false false false true  true  false  -- 000110 = A3
def y3 : SS.BitString 6 := bs false true  true  false false true   -- 011001 = B11
def y4 : SS.BitString 6 := bs false true  true  false true  false  -- 011010 = B12
def y5 : SS.BitString 6 := bs false true  true  true  true  true   -- 011111 = B13
def y6 : SS.BitString 6 := bs true  false true  false false true   -- 101001 = B21
def y7 : SS.BitString 6 := bs true  false true  false true  false  -- 101010 = B22
def y8 : SS.BitString 6 := bs true  false true  true  true  true   -- 101111 = B23
def y9 : SS.BitString 6 := bs true  true  false false false true   -- 110001 = B31
def y10 : SS.BitString 6 := bs true  true  false false true  false  -- 110010 = B32
def y11 : SS.BitString 6 := bs true  true  false true  true  true   -- 110111 = B33
def y12 : SS.BitString 6 := bs true  true  true  true  false false  -- 111100 = S

def z0 : SS.BitString 6 := bs false false false false true  true   -- 000011
def z1 : SS.BitString 6 := bs false false true  false false false  -- 001000
def z2 : SS.BitString 6 := bs false false true  true  false true   -- 001101
def z3 : SS.BitString 6 := bs false false true  true  true  false  -- 001110
def z4 : SS.BitString 6 := bs false true  false false false false  -- 010000
def z5 : SS.BitString 6 := bs false true  false true  false true   -- 010101
def z6 : SS.BitString 6 := bs false true  false true  true  false  -- 010110
def z7 : SS.BitString 6 := bs true  false false false false false  -- 100000
def z8 : SS.BitString 6 := bs true  false false true  false true   -- 100101
def z9 : SS.BitString 6 := bs true  false false true  true  false  -- 100110
def z10 : SS.BitString 6 := bs true  true  true  false false true   -- 111001
def z11 : SS.BitString 6 := bs true  true  true  false true  false  -- 111010
def z12 : SS.BitString 6 := bs true  true  true  true  true  true   -- 111111

def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12}
def S1 : Finset (SS.BitString 6) := {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12}

def av : Fin 6 -> ZMod 5 := ![1, 1, 1, 2, 3, 3]

/-- Each support is exactly its residue fiber, decided over all 64 strings. -/
theorem S0_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 0) = S0 := by
  decide

theorem S1_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 1) = S1 := by
  decide

def ef0 : SS.BitString 6 := bs false false false false true  true   -- mask 000011, reciprocal
def ef1 : SS.BitString 6 := bs false false false true  false true   -- mask 000101, reciprocal
def ef2 : SS.BitString 6 := bs false false false true  true  false  -- mask 000110, reciprocal
def ef3 : SS.BitString 6 := bs false false true  false false false  -- mask 001000, row
def ef4 : SS.BitString 6 := bs false false true  false false true   -- mask 001001, permanent
def ef5 : SS.BitString 6 := bs false false true  false true  false  -- mask 001010, permanent
def ef6 : SS.BitString 6 := bs false false true  true  false false  -- mask 001100, permanent
def ef7 : SS.BitString 6 := bs false true  false false false false  -- mask 010000, row
def ef8 : SS.BitString 6 := bs false true  false false false true   -- mask 010001, permanent
def ef9 : SS.BitString 6 := bs false true  false false true  false  -- mask 010010, permanent
def ef10 : SS.BitString 6 := bs false true  false true  false false  -- mask 010100, permanent
def ef11 : SS.BitString 6 := bs true  false false false false false  -- mask 100000, row
def ef12 : SS.BitString 6 := bs true  false false false false true   -- mask 100001, permanent
def ef13 : SS.BitString 6 := bs true  false false false true  false  -- mask 100010, permanent
def ef14 : SS.BitString 6 := bs true  false false true  false false  -- mask 100100, permanent
def w0 : SS.BitString 6 := bs false false false false false false  -- dressing 000000
def w1 : SS.BitString 6 := bs false false false false false true   -- dressing 000001
def w2 : SS.BitString 6 := bs false false false false true  false  -- dressing 000010
def w3 : SS.BitString 6 := bs false false false false true  true   -- dressing 000011
def w4 : SS.BitString 6 := bs false false false true  false false  -- dressing 000100
def w5 : SS.BitString 6 := bs false false false true  false true   -- dressing 000101
def w6 : SS.BitString 6 := bs false false false true  true  false  -- dressing 000110
def w7 : SS.BitString 6 := bs false false true  false false false  -- dressing 001000
def w8 : SS.BitString 6 := bs false false true  false false true   -- dressing 001001
def w9 : SS.BitString 6 := bs false false true  false true  false  -- dressing 001010
def w10 : SS.BitString 6 := bs false false true  true  false false  -- dressing 001100
def w11 : SS.BitString 6 := bs false true  false false false false  -- dressing 010000
def w12 : SS.BitString 6 := bs false true  false false false true   -- dressing 010001
def w13 : SS.BitString 6 := bs false true  false false true  false  -- dressing 010010
def w14 : SS.BitString 6 := bs false true  false true  false false  -- dressing 010100
def w15 : SS.BitString 6 := bs true  false false false false false  -- dressing 100000
def w16 : SS.BitString 6 := bs true  false false false false true   -- dressing 100001
def w17 : SS.BitString 6 := bs true  false false false true  false  -- dressing 100010
def w18 : SS.BitString 6 := bs true  false false true  false false  -- dressing 100100

theorem incidence0 :
    S1.filter (fun y => SS.bxor y ef0 ∈ S0) = {z0, z12} := by decide
theorem fl0_0 : SS.bxor z0 ef0 = y0 := by decide
theorem fl0_12 : SS.bxor z12 ef0 = y12 := by decide
theorem sg0_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg0_w0_12 : SS.bdot w0 z12 = false := by decide
theorem sg0_w2_0 : SS.bdot w2 z0 = true := by decide
theorem sg0_w2_12 : SS.bdot w2 z12 = true := by decide
theorem sg0_w1_0 : SS.bdot w1 z0 = true := by decide
theorem sg0_w1_12 : SS.bdot w1 z12 = true := by decide
theorem sg0_w3_0 : SS.bdot w3 z0 = false := by decide
theorem sg0_w3_12 : SS.bdot w3 z12 = false := by decide
theorem incidence1 :
    S1.filter (fun y => SS.bxor y ef1 ∈ S0) = {z0, z10} := by decide
theorem fl1_0 : SS.bxor z0 ef1 = y2 := by decide
theorem fl1_10 : SS.bxor z10 ef1 = y12 := by decide
theorem sg1_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg1_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg1_w4_0 : SS.bdot w4 z0 = false := by decide
theorem sg1_w4_10 : SS.bdot w4 z10 = false := by decide
theorem sg1_w1_0 : SS.bdot w1 z0 = true := by decide
theorem sg1_w1_10 : SS.bdot w1 z10 = true := by decide
theorem sg1_w5_0 : SS.bdot w5 z0 = true := by decide
theorem sg1_w5_10 : SS.bdot w5 z10 = true := by decide
theorem incidence2 :
    S1.filter (fun y => SS.bxor y ef2 ∈ S0) = {z0, z11} := by decide
theorem fl2_0 : SS.bxor z0 ef2 = y1 := by decide
theorem fl2_11 : SS.bxor z11 ef2 = y12 := by decide
theorem sg2_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg2_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg2_w4_0 : SS.bdot w4 z0 = false := by decide
theorem sg2_w4_11 : SS.bdot w4 z11 = false := by decide
theorem sg2_w2_0 : SS.bdot w2 z0 = true := by decide
theorem sg2_w2_11 : SS.bdot w2 z11 = true := by decide
theorem sg2_w6_0 : SS.bdot w6 z0 = true := by decide
theorem sg2_w6_11 : SS.bdot w6 z11 = true := by decide
theorem incidence3 :
    S1.filter (fun y => SS.bxor y ef3 ∈ S0) = {z1, z2, z3, z10, z11, z12} := by decide
theorem fl3_1 : SS.bxor z1 ef3 = y0 := by decide
theorem fl3_2 : SS.bxor z2 ef3 = y1 := by decide
theorem fl3_3 : SS.bxor z3 ef3 = y2 := by decide
theorem fl3_10 : SS.bxor z10 ef3 = y9 := by decide
theorem fl3_11 : SS.bxor z11 ef3 = y10 := by decide
theorem fl3_12 : SS.bxor z12 ef3 = y11 := by decide
theorem sg3_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg3_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg3_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg3_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg3_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg3_w0_12 : SS.bdot w0 z12 = false := by decide
theorem sg3_w15_1 : SS.bdot w15 z1 = false := by decide
theorem sg3_w15_2 : SS.bdot w15 z2 = false := by decide
theorem sg3_w15_3 : SS.bdot w15 z3 = false := by decide
theorem sg3_w15_10 : SS.bdot w15 z10 = true := by decide
theorem sg3_w15_11 : SS.bdot w15 z11 = true := by decide
theorem sg3_w15_12 : SS.bdot w15 z12 = true := by decide
theorem sg3_w11_1 : SS.bdot w11 z1 = false := by decide
theorem sg3_w11_2 : SS.bdot w11 z2 = false := by decide
theorem sg3_w11_3 : SS.bdot w11 z3 = false := by decide
theorem sg3_w11_10 : SS.bdot w11 z10 = true := by decide
theorem sg3_w11_11 : SS.bdot w11 z11 = true := by decide
theorem sg3_w11_12 : SS.bdot w11 z12 = true := by decide
theorem sg3_w7_1 : SS.bdot w7 z1 = true := by decide
theorem sg3_w7_2 : SS.bdot w7 z2 = true := by decide
theorem sg3_w7_3 : SS.bdot w7 z3 = true := by decide
theorem sg3_w7_10 : SS.bdot w7 z10 = true := by decide
theorem sg3_w7_11 : SS.bdot w7 z11 = true := by decide
theorem sg3_w7_12 : SS.bdot w7 z12 = true := by decide
theorem sg3_w4_1 : SS.bdot w4 z1 = false := by decide
theorem sg3_w4_2 : SS.bdot w4 z2 = true := by decide
theorem sg3_w4_3 : SS.bdot w4 z3 = true := by decide
theorem sg3_w4_10 : SS.bdot w4 z10 = false := by decide
theorem sg3_w4_11 : SS.bdot w4 z11 = false := by decide
theorem sg3_w4_12 : SS.bdot w4 z12 = true := by decide
theorem sg3_w2_1 : SS.bdot w2 z1 = false := by decide
theorem sg3_w2_2 : SS.bdot w2 z2 = false := by decide
theorem sg3_w2_3 : SS.bdot w2 z3 = true := by decide
theorem sg3_w2_10 : SS.bdot w2 z10 = false := by decide
theorem sg3_w2_11 : SS.bdot w2 z11 = true := by decide
theorem sg3_w2_12 : SS.bdot w2 z12 = true := by decide
theorem sg3_w1_1 : SS.bdot w1 z1 = false := by decide
theorem sg3_w1_2 : SS.bdot w1 z2 = true := by decide
theorem sg3_w1_3 : SS.bdot w1 z3 = false := by decide
theorem sg3_w1_10 : SS.bdot w1 z10 = true := by decide
theorem sg3_w1_11 : SS.bdot w1 z11 = false := by decide
theorem sg3_w1_12 : SS.bdot w1 z12 = true := by decide
theorem incidence4 :
    S1.filter (fun y => SS.bxor y ef4 ∈ S0) = {z4, z6, z7, z9} := by decide
theorem fl4_4 : SS.bxor z4 ef4 = y3 := by decide
theorem fl4_6 : SS.bxor z6 ef4 = y5 := by decide
theorem fl4_7 : SS.bxor z7 ef4 = y6 := by decide
theorem fl4_9 : SS.bxor z9 ef4 = y8 := by decide
theorem sg4_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg4_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg4_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg4_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg4_w7_4 : SS.bdot w7 z4 = false := by decide
theorem sg4_w7_6 : SS.bdot w7 z6 = false := by decide
theorem sg4_w7_7 : SS.bdot w7 z7 = false := by decide
theorem sg4_w7_9 : SS.bdot w7 z9 = false := by decide
theorem sg4_w1_4 : SS.bdot w1 z4 = false := by decide
theorem sg4_w1_6 : SS.bdot w1 z6 = false := by decide
theorem sg4_w1_7 : SS.bdot w1 z7 = false := by decide
theorem sg4_w1_9 : SS.bdot w1 z9 = false := by decide
theorem sg4_w8_4 : SS.bdot w8 z4 = false := by decide
theorem sg4_w8_6 : SS.bdot w8 z6 = false := by decide
theorem sg4_w8_7 : SS.bdot w8 z7 = false := by decide
theorem sg4_w8_9 : SS.bdot w8 z9 = false := by decide
theorem incidence5 :
    S1.filter (fun y => SS.bxor y ef5 ∈ S0) = {z4, z5, z7, z8} := by decide
theorem fl5_4 : SS.bxor z4 ef5 = y4 := by decide
theorem fl5_5 : SS.bxor z5 ef5 = y5 := by decide
theorem fl5_7 : SS.bxor z7 ef5 = y7 := by decide
theorem fl5_8 : SS.bxor z8 ef5 = y8 := by decide
theorem sg5_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg5_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg5_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg5_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg5_w7_4 : SS.bdot w7 z4 = false := by decide
theorem sg5_w7_5 : SS.bdot w7 z5 = false := by decide
theorem sg5_w7_7 : SS.bdot w7 z7 = false := by decide
theorem sg5_w7_8 : SS.bdot w7 z8 = false := by decide
theorem sg5_w2_4 : SS.bdot w2 z4 = false := by decide
theorem sg5_w2_5 : SS.bdot w2 z5 = false := by decide
theorem sg5_w2_7 : SS.bdot w2 z7 = false := by decide
theorem sg5_w2_8 : SS.bdot w2 z8 = false := by decide
theorem sg5_w9_4 : SS.bdot w9 z4 = false := by decide
theorem sg5_w9_5 : SS.bdot w9 z5 = false := by decide
theorem sg5_w9_7 : SS.bdot w9 z7 = false := by decide
theorem sg5_w9_8 : SS.bdot w9 z8 = false := by decide
theorem incidence6 :
    S1.filter (fun y => SS.bxor y ef6 ∈ S0) = {z5, z6, z8, z9} := by decide
theorem fl6_5 : SS.bxor z5 ef6 = y3 := by decide
theorem fl6_6 : SS.bxor z6 ef6 = y4 := by decide
theorem fl6_8 : SS.bxor z8 ef6 = y6 := by decide
theorem fl6_9 : SS.bxor z9 ef6 = y7 := by decide
theorem sg6_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg6_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg6_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg6_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg6_w7_5 : SS.bdot w7 z5 = false := by decide
theorem sg6_w7_6 : SS.bdot w7 z6 = false := by decide
theorem sg6_w7_8 : SS.bdot w7 z8 = false := by decide
theorem sg6_w7_9 : SS.bdot w7 z9 = false := by decide
theorem sg6_w4_5 : SS.bdot w4 z5 = true := by decide
theorem sg6_w4_6 : SS.bdot w4 z6 = true := by decide
theorem sg6_w4_8 : SS.bdot w4 z8 = true := by decide
theorem sg6_w4_9 : SS.bdot w4 z9 = true := by decide
theorem sg6_w10_5 : SS.bdot w10 z5 = true := by decide
theorem sg6_w10_6 : SS.bdot w10 z6 = true := by decide
theorem sg6_w10_8 : SS.bdot w10 z8 = true := by decide
theorem sg6_w10_9 : SS.bdot w10 z9 = true := by decide
theorem incidence7 :
    S1.filter (fun y => SS.bxor y ef7 ∈ S0) = {z4, z5, z6, z10, z11, z12} := by decide
theorem fl7_4 : SS.bxor z4 ef7 = y0 := by decide
theorem fl7_5 : SS.bxor z5 ef7 = y1 := by decide
theorem fl7_6 : SS.bxor z6 ef7 = y2 := by decide
theorem fl7_10 : SS.bxor z10 ef7 = y6 := by decide
theorem fl7_11 : SS.bxor z11 ef7 = y7 := by decide
theorem fl7_12 : SS.bxor z12 ef7 = y8 := by decide
theorem sg7_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg7_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg7_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg7_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg7_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg7_w0_12 : SS.bdot w0 z12 = false := by decide
theorem sg7_w15_4 : SS.bdot w15 z4 = false := by decide
theorem sg7_w15_5 : SS.bdot w15 z5 = false := by decide
theorem sg7_w15_6 : SS.bdot w15 z6 = false := by decide
theorem sg7_w15_10 : SS.bdot w15 z10 = true := by decide
theorem sg7_w15_11 : SS.bdot w15 z11 = true := by decide
theorem sg7_w15_12 : SS.bdot w15 z12 = true := by decide
theorem sg7_w11_4 : SS.bdot w11 z4 = true := by decide
theorem sg7_w11_5 : SS.bdot w11 z5 = true := by decide
theorem sg7_w11_6 : SS.bdot w11 z6 = true := by decide
theorem sg7_w11_10 : SS.bdot w11 z10 = true := by decide
theorem sg7_w11_11 : SS.bdot w11 z11 = true := by decide
theorem sg7_w11_12 : SS.bdot w11 z12 = true := by decide
theorem sg7_w7_4 : SS.bdot w7 z4 = false := by decide
theorem sg7_w7_5 : SS.bdot w7 z5 = false := by decide
theorem sg7_w7_6 : SS.bdot w7 z6 = false := by decide
theorem sg7_w7_10 : SS.bdot w7 z10 = true := by decide
theorem sg7_w7_11 : SS.bdot w7 z11 = true := by decide
theorem sg7_w7_12 : SS.bdot w7 z12 = true := by decide
theorem sg7_w4_4 : SS.bdot w4 z4 = false := by decide
theorem sg7_w4_5 : SS.bdot w4 z5 = true := by decide
theorem sg7_w4_6 : SS.bdot w4 z6 = true := by decide
theorem sg7_w4_10 : SS.bdot w4 z10 = false := by decide
theorem sg7_w4_11 : SS.bdot w4 z11 = false := by decide
theorem sg7_w4_12 : SS.bdot w4 z12 = true := by decide
theorem sg7_w2_4 : SS.bdot w2 z4 = false := by decide
theorem sg7_w2_5 : SS.bdot w2 z5 = false := by decide
theorem sg7_w2_6 : SS.bdot w2 z6 = true := by decide
theorem sg7_w2_10 : SS.bdot w2 z10 = false := by decide
theorem sg7_w2_11 : SS.bdot w2 z11 = true := by decide
theorem sg7_w2_12 : SS.bdot w2 z12 = true := by decide
theorem sg7_w1_4 : SS.bdot w1 z4 = false := by decide
theorem sg7_w1_5 : SS.bdot w1 z5 = true := by decide
theorem sg7_w1_6 : SS.bdot w1 z6 = false := by decide
theorem sg7_w1_10 : SS.bdot w1 z10 = true := by decide
theorem sg7_w1_11 : SS.bdot w1 z11 = false := by decide
theorem sg7_w1_12 : SS.bdot w1 z12 = true := by decide
theorem incidence8 :
    S1.filter (fun y => SS.bxor y ef8 ∈ S0) = {z1, z3, z7, z9} := by decide
theorem fl8_1 : SS.bxor z1 ef8 = y3 := by decide
theorem fl8_3 : SS.bxor z3 ef8 = y5 := by decide
theorem fl8_7 : SS.bxor z7 ef8 = y9 := by decide
theorem fl8_9 : SS.bxor z9 ef8 = y11 := by decide
theorem sg8_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg8_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg8_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg8_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg8_w11_1 : SS.bdot w11 z1 = false := by decide
theorem sg8_w11_3 : SS.bdot w11 z3 = false := by decide
theorem sg8_w11_7 : SS.bdot w11 z7 = false := by decide
theorem sg8_w11_9 : SS.bdot w11 z9 = false := by decide
theorem sg8_w1_1 : SS.bdot w1 z1 = false := by decide
theorem sg8_w1_3 : SS.bdot w1 z3 = false := by decide
theorem sg8_w1_7 : SS.bdot w1 z7 = false := by decide
theorem sg8_w1_9 : SS.bdot w1 z9 = false := by decide
theorem sg8_w12_1 : SS.bdot w12 z1 = false := by decide
theorem sg8_w12_3 : SS.bdot w12 z3 = false := by decide
theorem sg8_w12_7 : SS.bdot w12 z7 = false := by decide
theorem sg8_w12_9 : SS.bdot w12 z9 = false := by decide
theorem incidence9 :
    S1.filter (fun y => SS.bxor y ef9 ∈ S0) = {z1, z2, z7, z8} := by decide
theorem fl9_1 : SS.bxor z1 ef9 = y4 := by decide
theorem fl9_2 : SS.bxor z2 ef9 = y5 := by decide
theorem fl9_7 : SS.bxor z7 ef9 = y10 := by decide
theorem fl9_8 : SS.bxor z8 ef9 = y11 := by decide
theorem sg9_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg9_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg9_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg9_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg9_w11_1 : SS.bdot w11 z1 = false := by decide
theorem sg9_w11_2 : SS.bdot w11 z2 = false := by decide
theorem sg9_w11_7 : SS.bdot w11 z7 = false := by decide
theorem sg9_w11_8 : SS.bdot w11 z8 = false := by decide
theorem sg9_w2_1 : SS.bdot w2 z1 = false := by decide
theorem sg9_w2_2 : SS.bdot w2 z2 = false := by decide
theorem sg9_w2_7 : SS.bdot w2 z7 = false := by decide
theorem sg9_w2_8 : SS.bdot w2 z8 = false := by decide
theorem sg9_w13_1 : SS.bdot w13 z1 = false := by decide
theorem sg9_w13_2 : SS.bdot w13 z2 = false := by decide
theorem sg9_w13_7 : SS.bdot w13 z7 = false := by decide
theorem sg9_w13_8 : SS.bdot w13 z8 = false := by decide
theorem incidence10 :
    S1.filter (fun y => SS.bxor y ef10 ∈ S0) = {z2, z3, z8, z9} := by decide
theorem fl10_2 : SS.bxor z2 ef10 = y3 := by decide
theorem fl10_3 : SS.bxor z3 ef10 = y4 := by decide
theorem fl10_8 : SS.bxor z8 ef10 = y9 := by decide
theorem fl10_9 : SS.bxor z9 ef10 = y10 := by decide
theorem sg10_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg10_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg10_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg10_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg10_w11_2 : SS.bdot w11 z2 = false := by decide
theorem sg10_w11_3 : SS.bdot w11 z3 = false := by decide
theorem sg10_w11_8 : SS.bdot w11 z8 = false := by decide
theorem sg10_w11_9 : SS.bdot w11 z9 = false := by decide
theorem sg10_w4_2 : SS.bdot w4 z2 = true := by decide
theorem sg10_w4_3 : SS.bdot w4 z3 = true := by decide
theorem sg10_w4_8 : SS.bdot w4 z8 = true := by decide
theorem sg10_w4_9 : SS.bdot w4 z9 = true := by decide
theorem sg10_w14_2 : SS.bdot w14 z2 = true := by decide
theorem sg10_w14_3 : SS.bdot w14 z3 = true := by decide
theorem sg10_w14_8 : SS.bdot w14 z8 = true := by decide
theorem sg10_w14_9 : SS.bdot w14 z9 = true := by decide
theorem incidence11 :
    S1.filter (fun y => SS.bxor y ef11 ∈ S0) = {z7, z8, z9, z10, z11, z12} := by decide
theorem fl11_7 : SS.bxor z7 ef11 = y0 := by decide
theorem fl11_8 : SS.bxor z8 ef11 = y1 := by decide
theorem fl11_9 : SS.bxor z9 ef11 = y2 := by decide
theorem fl11_10 : SS.bxor z10 ef11 = y3 := by decide
theorem fl11_11 : SS.bxor z11 ef11 = y4 := by decide
theorem fl11_12 : SS.bxor z12 ef11 = y5 := by decide
theorem sg11_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg11_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg11_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg11_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg11_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg11_w0_12 : SS.bdot w0 z12 = false := by decide
theorem sg11_w15_7 : SS.bdot w15 z7 = true := by decide
theorem sg11_w15_8 : SS.bdot w15 z8 = true := by decide
theorem sg11_w15_9 : SS.bdot w15 z9 = true := by decide
theorem sg11_w15_10 : SS.bdot w15 z10 = true := by decide
theorem sg11_w15_11 : SS.bdot w15 z11 = true := by decide
theorem sg11_w15_12 : SS.bdot w15 z12 = true := by decide
theorem sg11_w11_7 : SS.bdot w11 z7 = false := by decide
theorem sg11_w11_8 : SS.bdot w11 z8 = false := by decide
theorem sg11_w11_9 : SS.bdot w11 z9 = false := by decide
theorem sg11_w11_10 : SS.bdot w11 z10 = true := by decide
theorem sg11_w11_11 : SS.bdot w11 z11 = true := by decide
theorem sg11_w11_12 : SS.bdot w11 z12 = true := by decide
theorem sg11_w7_7 : SS.bdot w7 z7 = false := by decide
theorem sg11_w7_8 : SS.bdot w7 z8 = false := by decide
theorem sg11_w7_9 : SS.bdot w7 z9 = false := by decide
theorem sg11_w7_10 : SS.bdot w7 z10 = true := by decide
theorem sg11_w7_11 : SS.bdot w7 z11 = true := by decide
theorem sg11_w7_12 : SS.bdot w7 z12 = true := by decide
theorem sg11_w4_7 : SS.bdot w4 z7 = false := by decide
theorem sg11_w4_8 : SS.bdot w4 z8 = true := by decide
theorem sg11_w4_9 : SS.bdot w4 z9 = true := by decide
theorem sg11_w4_10 : SS.bdot w4 z10 = false := by decide
theorem sg11_w4_11 : SS.bdot w4 z11 = false := by decide
theorem sg11_w4_12 : SS.bdot w4 z12 = true := by decide
theorem sg11_w2_7 : SS.bdot w2 z7 = false := by decide
theorem sg11_w2_8 : SS.bdot w2 z8 = false := by decide
theorem sg11_w2_9 : SS.bdot w2 z9 = true := by decide
theorem sg11_w2_10 : SS.bdot w2 z10 = false := by decide
theorem sg11_w2_11 : SS.bdot w2 z11 = true := by decide
theorem sg11_w2_12 : SS.bdot w2 z12 = true := by decide
theorem sg11_w1_7 : SS.bdot w1 z7 = false := by decide
theorem sg11_w1_8 : SS.bdot w1 z8 = true := by decide
theorem sg11_w1_9 : SS.bdot w1 z9 = false := by decide
theorem sg11_w1_10 : SS.bdot w1 z10 = true := by decide
theorem sg11_w1_11 : SS.bdot w1 z11 = false := by decide
theorem sg11_w1_12 : SS.bdot w1 z12 = true := by decide
theorem incidence12 :
    S1.filter (fun y => SS.bxor y ef12 ∈ S0) = {z1, z3, z4, z6} := by decide
theorem fl12_1 : SS.bxor z1 ef12 = y6 := by decide
theorem fl12_3 : SS.bxor z3 ef12 = y8 := by decide
theorem fl12_4 : SS.bxor z4 ef12 = y9 := by decide
theorem fl12_6 : SS.bxor z6 ef12 = y11 := by decide
theorem sg12_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg12_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg12_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg12_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg12_w15_1 : SS.bdot w15 z1 = false := by decide
theorem sg12_w15_3 : SS.bdot w15 z3 = false := by decide
theorem sg12_w15_4 : SS.bdot w15 z4 = false := by decide
theorem sg12_w15_6 : SS.bdot w15 z6 = false := by decide
theorem sg12_w1_1 : SS.bdot w1 z1 = false := by decide
theorem sg12_w1_3 : SS.bdot w1 z3 = false := by decide
theorem sg12_w1_4 : SS.bdot w1 z4 = false := by decide
theorem sg12_w1_6 : SS.bdot w1 z6 = false := by decide
theorem sg12_w16_1 : SS.bdot w16 z1 = false := by decide
theorem sg12_w16_3 : SS.bdot w16 z3 = false := by decide
theorem sg12_w16_4 : SS.bdot w16 z4 = false := by decide
theorem sg12_w16_6 : SS.bdot w16 z6 = false := by decide
theorem incidence13 :
    S1.filter (fun y => SS.bxor y ef13 ∈ S0) = {z1, z2, z4, z5} := by decide
theorem fl13_1 : SS.bxor z1 ef13 = y7 := by decide
theorem fl13_2 : SS.bxor z2 ef13 = y8 := by decide
theorem fl13_4 : SS.bxor z4 ef13 = y10 := by decide
theorem fl13_5 : SS.bxor z5 ef13 = y11 := by decide
theorem sg13_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg13_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg13_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg13_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg13_w15_1 : SS.bdot w15 z1 = false := by decide
theorem sg13_w15_2 : SS.bdot w15 z2 = false := by decide
theorem sg13_w15_4 : SS.bdot w15 z4 = false := by decide
theorem sg13_w15_5 : SS.bdot w15 z5 = false := by decide
theorem sg13_w2_1 : SS.bdot w2 z1 = false := by decide
theorem sg13_w2_2 : SS.bdot w2 z2 = false := by decide
theorem sg13_w2_4 : SS.bdot w2 z4 = false := by decide
theorem sg13_w2_5 : SS.bdot w2 z5 = false := by decide
theorem sg13_w17_1 : SS.bdot w17 z1 = false := by decide
theorem sg13_w17_2 : SS.bdot w17 z2 = false := by decide
theorem sg13_w17_4 : SS.bdot w17 z4 = false := by decide
theorem sg13_w17_5 : SS.bdot w17 z5 = false := by decide
theorem incidence14 :
    S1.filter (fun y => SS.bxor y ef14 ∈ S0) = {z2, z3, z5, z6} := by decide
theorem fl14_2 : SS.bxor z2 ef14 = y6 := by decide
theorem fl14_3 : SS.bxor z3 ef14 = y7 := by decide
theorem fl14_5 : SS.bxor z5 ef14 = y9 := by decide
theorem fl14_6 : SS.bxor z6 ef14 = y10 := by decide
theorem sg14_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg14_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg14_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg14_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg14_w15_2 : SS.bdot w15 z2 = false := by decide
theorem sg14_w15_3 : SS.bdot w15 z3 = false := by decide
theorem sg14_w15_5 : SS.bdot w15 z5 = false := by decide
theorem sg14_w15_6 : SS.bdot w15 z6 = false := by decide
theorem sg14_w4_2 : SS.bdot w4 z2 = true := by decide
theorem sg14_w4_3 : SS.bdot w4 z3 = true := by decide
theorem sg14_w4_5 : SS.bdot w4 z5 = true := by decide
theorem sg14_w4_6 : SS.bdot w4 z6 = true := by decide
theorem sg14_w18_2 : SS.bdot w18 z2 = true := by decide
theorem sg14_w18_3 : SS.bdot w18 z3 = true := by decide
theorem sg14_w18_5 : SS.bdot w18 z5 = true := by decide
theorem sg14_w18_6 : SS.bdot w18 z6 = true := by decide

/-! ## The moment system -/

/-- The two normalizations, the twenty-one moment equalities, and the
nonnegativity of every probability. -/
structure MomentSystem (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : Real) : Prop where
  n0 : q0 + q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 + q9 + q10 + q11 + q12 = 1
  n1 : r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 = 1
  m1 : q6 + q7 + q8 + q9 + q10 + q11 + q12 = r7 + r8 + r9 + r10 + r11 + r12
  m2 : q3 + q4 + q5 + q9 + q10 + q11 + q12 = r4 + r5 + r6 + r10 + r11 + r12
  m3 : q3 + q4 + q5 + q6 + q7 + q8 + q12 = r1 + r2 + r3 + r10 + r11 + r12
  m4 : q1 + q2 + q5 + q8 + q11 + q12 = r2 + r3 + r5 + r6 + r8 + r9 + r12
  m5 : q2 + q4 + q5 + q7 + q8 + q10 + q11 = r0 + r3 + r6 + r9 + r11 + r12
  m6 : q1 + q3 + q5 + q6 + q8 + q9 + q11 = r0 + r2 + r5 + r8 + r10 + r12
  c12 : q9 + q10 + q11 + q12 = r10 + r11 + r12
  c13 : q6 + q7 + q8 + q12 = r10 + r11 + r12
  c14 : q8 + q11 + q12 = r8 + r9 + r12
  c15 : q7 + q8 + q10 + q11 = r9 + r11 + r12
  c16 : q6 + q8 + q9 + q11 = r8 + r10 + r12
  c23 : q3 + q4 + q5 + q12 = r10 + r11 + r12
  c24 : q5 + q11 + q12 = r5 + r6 + r12
  c25 : q4 + q5 + q10 + q11 = r6 + r11 + r12
  c26 : q3 + q5 + q9 + q11 = r5 + r10 + r12
  c34 : q5 + q8 + q12 = r2 + r3 + r12
  c35 : q4 + q5 + q7 + q8 = r3 + r11 + r12
  c36 : q3 + q5 + q6 + q8 = r2 + r10 + r12
  c45 : q2 + q5 + q8 + q11 = r3 + r6 + r9 + r12
  c46 : q1 + q5 + q8 + q11 = r2 + r5 + r8 + r12
  c56 : q5 + q8 + q11 = r0 + r12

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

/-- The star probabilities, the A-sums and the six row sums. -/
theorem MomentSystem.facts {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) :
    q12 = 1/10 ∧ r0 = 1/10 ∧ q0 + q1 + q2 = 3/10 ∧ r12 + r11 + r10 = 3/10 ∧ q3 + q4 + q5 = 1/5 ∧ q6 + q7 + q8 = 1/5 ∧ q9 + q10 + q11 = 1/5 ∧ r9 + r8 + r7 = 1/5 ∧ r6 + r5 + r4 = 1/5 ∧ r3 + r2 + r1 = 1/5 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- Every grid column carries at least one tenth of the weight. -/
theorem MomentSystem.columns {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) :
    1/10 ≤ q3 + q6 + q9 ∧ 1/10 ≤ q4 + q7 + q10 ∧ 1/10 ≤ q5 + q8 + q11 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-! ## The Walsh equations -/

def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),
      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

theorem ex0_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w0 = star (c y0) * d z0 + star (c y12) * d z12 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_0, fl0_12]
  simp only [sg0_w0_0, sg0_w0_12, SixQubit.signMul_false]
  try ring

theorem ex0_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w2 = - star (c y0) * d z0 - star (c y12) * d z12 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_0, fl0_12]
  simp only [sg0_w2_0, sg0_w2_12, SixQubit.signMul_true]
  try ring

theorem ex0_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w1 = - star (c y0) * d z0 - star (c y12) * d z12 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_0, fl0_12]
  simp only [sg0_w1_0, sg0_w1_12, SixQubit.signMul_true]
  try ring

theorem ex0_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w3 = star (c y0) * d z0 + star (c y12) * d z12 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_0, fl0_12]
  simp only [sg0_w3_0, sg0_w3_12, SixQubit.signMul_false]
  try ring

theorem ex1_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w0 = star (c y2) * d z0 + star (c y12) * d z10 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_0, fl1_10]
  simp only [sg1_w0_0, sg1_w0_10, SixQubit.signMul_false]
  try ring

theorem ex1_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w4 = star (c y2) * d z0 + star (c y12) * d z10 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_0, fl1_10]
  simp only [sg1_w4_0, sg1_w4_10, SixQubit.signMul_false]
  try ring

theorem ex1_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w1 = - star (c y2) * d z0 - star (c y12) * d z10 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_0, fl1_10]
  simp only [sg1_w1_0, sg1_w1_10, SixQubit.signMul_true]
  try ring

theorem ex1_w5 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w5 = - star (c y2) * d z0 - star (c y12) * d z10 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_0, fl1_10]
  simp only [sg1_w5_0, sg1_w5_10, SixQubit.signMul_true]
  try ring

theorem ex2_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w0 = star (c y1) * d z0 + star (c y12) * d z11 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_0, fl2_11]
  simp only [sg2_w0_0, sg2_w0_11, SixQubit.signMul_false]
  try ring

theorem ex2_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w4 = star (c y1) * d z0 + star (c y12) * d z11 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_0, fl2_11]
  simp only [sg2_w4_0, sg2_w4_11, SixQubit.signMul_false]
  try ring

theorem ex2_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w2 = - star (c y1) * d z0 - star (c y12) * d z11 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_0, fl2_11]
  simp only [sg2_w2_0, sg2_w2_11, SixQubit.signMul_true]
  try ring

theorem ex2_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w6 = - star (c y1) * d z0 - star (c y12) * d z11 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_0, fl2_11]
  simp only [sg2_w6_0, sg2_w6_11, SixQubit.signMul_true]
  try ring

theorem ex3_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w0 = star (c y0) * d z1 + star (c y1) * d z2 + star (c y2) * d z3 + star (c y9) * d z10 + star (c y10) * d z11 + star (c y11) * d z12 := by
  unfold offSum
  rw [incidence3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl3_1, fl3_2, fl3_3, fl3_10, fl3_11, fl3_12]
  simp only [sg3_w0_1, sg3_w0_2, sg3_w0_3, sg3_w0_10, sg3_w0_11, sg3_w0_12, SixQubit.signMul_false]
  try ring

theorem ex3_w15 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w15 = star (c y0) * d z1 + star (c y1) * d z2 + star (c y2) * d z3 - star (c y9) * d z10 - star (c y10) * d z11 - star (c y11) * d z12 := by
  unfold offSum
  rw [incidence3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl3_1, fl3_2, fl3_3, fl3_10, fl3_11, fl3_12]
  simp only [sg3_w15_1, sg3_w15_2, sg3_w15_3, sg3_w15_10, sg3_w15_11, sg3_w15_12, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex3_w11 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w11 = star (c y0) * d z1 + star (c y1) * d z2 + star (c y2) * d z3 - star (c y9) * d z10 - star (c y10) * d z11 - star (c y11) * d z12 := by
  unfold offSum
  rw [incidence3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl3_1, fl3_2, fl3_3, fl3_10, fl3_11, fl3_12]
  simp only [sg3_w11_1, sg3_w11_2, sg3_w11_3, sg3_w11_10, sg3_w11_11, sg3_w11_12, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex3_w7 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w7 = - star (c y0) * d z1 - star (c y1) * d z2 - star (c y2) * d z3 - star (c y9) * d z10 - star (c y10) * d z11 - star (c y11) * d z12 := by
  unfold offSum
  rw [incidence3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl3_1, fl3_2, fl3_3, fl3_10, fl3_11, fl3_12]
  simp only [sg3_w7_1, sg3_w7_2, sg3_w7_3, sg3_w7_10, sg3_w7_11, sg3_w7_12, SixQubit.signMul_true]
  try ring

theorem ex3_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w4 = star (c y0) * d z1 - star (c y1) * d z2 - star (c y2) * d z3 + star (c y9) * d z10 + star (c y10) * d z11 - star (c y11) * d z12 := by
  unfold offSum
  rw [incidence3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl3_1, fl3_2, fl3_3, fl3_10, fl3_11, fl3_12]
  simp only [sg3_w4_1, sg3_w4_2, sg3_w4_3, sg3_w4_10, sg3_w4_11, sg3_w4_12, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex3_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w2 = star (c y0) * d z1 + star (c y1) * d z2 - star (c y2) * d z3 + star (c y9) * d z10 - star (c y10) * d z11 - star (c y11) * d z12 := by
  unfold offSum
  rw [incidence3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl3_1, fl3_2, fl3_3, fl3_10, fl3_11, fl3_12]
  simp only [sg3_w2_1, sg3_w2_2, sg3_w2_3, sg3_w2_10, sg3_w2_11, sg3_w2_12, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex3_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w1 = star (c y0) * d z1 - star (c y1) * d z2 + star (c y2) * d z3 - star (c y9) * d z10 + star (c y10) * d z11 - star (c y11) * d z12 := by
  unfold offSum
  rw [incidence3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl3_1, fl3_2, fl3_3, fl3_10, fl3_11, fl3_12]
  simp only [sg3_w1_1, sg3_w1_2, sg3_w1_3, sg3_w1_10, sg3_w1_11, sg3_w1_12, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex4_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w0 = star (c y3) * d z4 + star (c y5) * d z6 + star (c y6) * d z7 + star (c y8) * d z9 := by
  unfold offSum
  rw [incidence4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl4_4, fl4_6, fl4_7, fl4_9]
  simp only [sg4_w0_4, sg4_w0_6, sg4_w0_7, sg4_w0_9, SixQubit.signMul_false]
  try ring

theorem ex4_w7 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w7 = star (c y3) * d z4 + star (c y5) * d z6 + star (c y6) * d z7 + star (c y8) * d z9 := by
  unfold offSum
  rw [incidence4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl4_4, fl4_6, fl4_7, fl4_9]
  simp only [sg4_w7_4, sg4_w7_6, sg4_w7_7, sg4_w7_9, SixQubit.signMul_false]
  try ring

theorem ex4_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w1 = star (c y3) * d z4 + star (c y5) * d z6 + star (c y6) * d z7 + star (c y8) * d z9 := by
  unfold offSum
  rw [incidence4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl4_4, fl4_6, fl4_7, fl4_9]
  simp only [sg4_w1_4, sg4_w1_6, sg4_w1_7, sg4_w1_9, SixQubit.signMul_false]
  try ring

theorem ex4_w8 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w8 = star (c y3) * d z4 + star (c y5) * d z6 + star (c y6) * d z7 + star (c y8) * d z9 := by
  unfold offSum
  rw [incidence4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl4_4, fl4_6, fl4_7, fl4_9]
  simp only [sg4_w8_4, sg4_w8_6, sg4_w8_7, sg4_w8_9, SixQubit.signMul_false]
  try ring

theorem ex5_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef5 w0 = star (c y4) * d z4 + star (c y5) * d z5 + star (c y7) * d z7 + star (c y8) * d z8 := by
  unfold offSum
  rw [incidence5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl5_4, fl5_5, fl5_7, fl5_8]
  simp only [sg5_w0_4, sg5_w0_5, sg5_w0_7, sg5_w0_8, SixQubit.signMul_false]
  try ring

theorem ex5_w7 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef5 w7 = star (c y4) * d z4 + star (c y5) * d z5 + star (c y7) * d z7 + star (c y8) * d z8 := by
  unfold offSum
  rw [incidence5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl5_4, fl5_5, fl5_7, fl5_8]
  simp only [sg5_w7_4, sg5_w7_5, sg5_w7_7, sg5_w7_8, SixQubit.signMul_false]
  try ring

theorem ex5_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef5 w2 = star (c y4) * d z4 + star (c y5) * d z5 + star (c y7) * d z7 + star (c y8) * d z8 := by
  unfold offSum
  rw [incidence5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl5_4, fl5_5, fl5_7, fl5_8]
  simp only [sg5_w2_4, sg5_w2_5, sg5_w2_7, sg5_w2_8, SixQubit.signMul_false]
  try ring

theorem ex5_w9 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef5 w9 = star (c y4) * d z4 + star (c y5) * d z5 + star (c y7) * d z7 + star (c y8) * d z8 := by
  unfold offSum
  rw [incidence5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl5_4, fl5_5, fl5_7, fl5_8]
  simp only [sg5_w9_4, sg5_w9_5, sg5_w9_7, sg5_w9_8, SixQubit.signMul_false]
  try ring

theorem ex6_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w0 = star (c y3) * d z5 + star (c y4) * d z6 + star (c y6) * d z8 + star (c y7) * d z9 := by
  unfold offSum
  rw [incidence6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl6_5, fl6_6, fl6_8, fl6_9]
  simp only [sg6_w0_5, sg6_w0_6, sg6_w0_8, sg6_w0_9, SixQubit.signMul_false]
  try ring

theorem ex6_w7 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w7 = star (c y3) * d z5 + star (c y4) * d z6 + star (c y6) * d z8 + star (c y7) * d z9 := by
  unfold offSum
  rw [incidence6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl6_5, fl6_6, fl6_8, fl6_9]
  simp only [sg6_w7_5, sg6_w7_6, sg6_w7_8, sg6_w7_9, SixQubit.signMul_false]
  try ring

theorem ex6_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w4 = - star (c y3) * d z5 - star (c y4) * d z6 - star (c y6) * d z8 - star (c y7) * d z9 := by
  unfold offSum
  rw [incidence6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl6_5, fl6_6, fl6_8, fl6_9]
  simp only [sg6_w4_5, sg6_w4_6, sg6_w4_8, sg6_w4_9, SixQubit.signMul_true]
  try ring

theorem ex6_w10 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w10 = - star (c y3) * d z5 - star (c y4) * d z6 - star (c y6) * d z8 - star (c y7) * d z9 := by
  unfold offSum
  rw [incidence6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl6_5, fl6_6, fl6_8, fl6_9]
  simp only [sg6_w10_5, sg6_w10_6, sg6_w10_8, sg6_w10_9, SixQubit.signMul_true]
  try ring

theorem ex7_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef7 w0 = star (c y0) * d z4 + star (c y1) * d z5 + star (c y2) * d z6 + star (c y6) * d z10 + star (c y7) * d z11 + star (c y8) * d z12 := by
  unfold offSum
  rw [incidence7]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl7_4, fl7_5, fl7_6, fl7_10, fl7_11, fl7_12]
  simp only [sg7_w0_4, sg7_w0_5, sg7_w0_6, sg7_w0_10, sg7_w0_11, sg7_w0_12, SixQubit.signMul_false]
  try ring

theorem ex7_w15 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef7 w15 = star (c y0) * d z4 + star (c y1) * d z5 + star (c y2) * d z6 - star (c y6) * d z10 - star (c y7) * d z11 - star (c y8) * d z12 := by
  unfold offSum
  rw [incidence7]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl7_4, fl7_5, fl7_6, fl7_10, fl7_11, fl7_12]
  simp only [sg7_w15_4, sg7_w15_5, sg7_w15_6, sg7_w15_10, sg7_w15_11, sg7_w15_12, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex7_w11 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef7 w11 = - star (c y0) * d z4 - star (c y1) * d z5 - star (c y2) * d z6 - star (c y6) * d z10 - star (c y7) * d z11 - star (c y8) * d z12 := by
  unfold offSum
  rw [incidence7]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl7_4, fl7_5, fl7_6, fl7_10, fl7_11, fl7_12]
  simp only [sg7_w11_4, sg7_w11_5, sg7_w11_6, sg7_w11_10, sg7_w11_11, sg7_w11_12, SixQubit.signMul_true]
  try ring

theorem ex7_w7 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef7 w7 = star (c y0) * d z4 + star (c y1) * d z5 + star (c y2) * d z6 - star (c y6) * d z10 - star (c y7) * d z11 - star (c y8) * d z12 := by
  unfold offSum
  rw [incidence7]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl7_4, fl7_5, fl7_6, fl7_10, fl7_11, fl7_12]
  simp only [sg7_w7_4, sg7_w7_5, sg7_w7_6, sg7_w7_10, sg7_w7_11, sg7_w7_12, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex7_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef7 w4 = star (c y0) * d z4 - star (c y1) * d z5 - star (c y2) * d z6 + star (c y6) * d z10 + star (c y7) * d z11 - star (c y8) * d z12 := by
  unfold offSum
  rw [incidence7]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl7_4, fl7_5, fl7_6, fl7_10, fl7_11, fl7_12]
  simp only [sg7_w4_4, sg7_w4_5, sg7_w4_6, sg7_w4_10, sg7_w4_11, sg7_w4_12, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex7_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef7 w2 = star (c y0) * d z4 + star (c y1) * d z5 - star (c y2) * d z6 + star (c y6) * d z10 - star (c y7) * d z11 - star (c y8) * d z12 := by
  unfold offSum
  rw [incidence7]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl7_4, fl7_5, fl7_6, fl7_10, fl7_11, fl7_12]
  simp only [sg7_w2_4, sg7_w2_5, sg7_w2_6, sg7_w2_10, sg7_w2_11, sg7_w2_12, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex7_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef7 w1 = star (c y0) * d z4 - star (c y1) * d z5 + star (c y2) * d z6 - star (c y6) * d z10 + star (c y7) * d z11 - star (c y8) * d z12 := by
  unfold offSum
  rw [incidence7]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl7_4, fl7_5, fl7_6, fl7_10, fl7_11, fl7_12]
  simp only [sg7_w1_4, sg7_w1_5, sg7_w1_6, sg7_w1_10, sg7_w1_11, sg7_w1_12, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex8_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef8 w0 = star (c y3) * d z1 + star (c y5) * d z3 + star (c y9) * d z7 + star (c y11) * d z9 := by
  unfold offSum
  rw [incidence8]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl8_1, fl8_3, fl8_7, fl8_9]
  simp only [sg8_w0_1, sg8_w0_3, sg8_w0_7, sg8_w0_9, SixQubit.signMul_false]
  try ring

theorem ex8_w11 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef8 w11 = star (c y3) * d z1 + star (c y5) * d z3 + star (c y9) * d z7 + star (c y11) * d z9 := by
  unfold offSum
  rw [incidence8]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl8_1, fl8_3, fl8_7, fl8_9]
  simp only [sg8_w11_1, sg8_w11_3, sg8_w11_7, sg8_w11_9, SixQubit.signMul_false]
  try ring

theorem ex8_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef8 w1 = star (c y3) * d z1 + star (c y5) * d z3 + star (c y9) * d z7 + star (c y11) * d z9 := by
  unfold offSum
  rw [incidence8]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl8_1, fl8_3, fl8_7, fl8_9]
  simp only [sg8_w1_1, sg8_w1_3, sg8_w1_7, sg8_w1_9, SixQubit.signMul_false]
  try ring

theorem ex8_w12 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef8 w12 = star (c y3) * d z1 + star (c y5) * d z3 + star (c y9) * d z7 + star (c y11) * d z9 := by
  unfold offSum
  rw [incidence8]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl8_1, fl8_3, fl8_7, fl8_9]
  simp only [sg8_w12_1, sg8_w12_3, sg8_w12_7, sg8_w12_9, SixQubit.signMul_false]
  try ring

theorem ex9_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef9 w0 = star (c y4) * d z1 + star (c y5) * d z2 + star (c y10) * d z7 + star (c y11) * d z8 := by
  unfold offSum
  rw [incidence9]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl9_1, fl9_2, fl9_7, fl9_8]
  simp only [sg9_w0_1, sg9_w0_2, sg9_w0_7, sg9_w0_8, SixQubit.signMul_false]
  try ring

theorem ex9_w11 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef9 w11 = star (c y4) * d z1 + star (c y5) * d z2 + star (c y10) * d z7 + star (c y11) * d z8 := by
  unfold offSum
  rw [incidence9]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl9_1, fl9_2, fl9_7, fl9_8]
  simp only [sg9_w11_1, sg9_w11_2, sg9_w11_7, sg9_w11_8, SixQubit.signMul_false]
  try ring

theorem ex9_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef9 w2 = star (c y4) * d z1 + star (c y5) * d z2 + star (c y10) * d z7 + star (c y11) * d z8 := by
  unfold offSum
  rw [incidence9]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl9_1, fl9_2, fl9_7, fl9_8]
  simp only [sg9_w2_1, sg9_w2_2, sg9_w2_7, sg9_w2_8, SixQubit.signMul_false]
  try ring

theorem ex9_w13 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef9 w13 = star (c y4) * d z1 + star (c y5) * d z2 + star (c y10) * d z7 + star (c y11) * d z8 := by
  unfold offSum
  rw [incidence9]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl9_1, fl9_2, fl9_7, fl9_8]
  simp only [sg9_w13_1, sg9_w13_2, sg9_w13_7, sg9_w13_8, SixQubit.signMul_false]
  try ring

theorem ex10_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef10 w0 = star (c y3) * d z2 + star (c y4) * d z3 + star (c y9) * d z8 + star (c y10) * d z9 := by
  unfold offSum
  rw [incidence10]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl10_2, fl10_3, fl10_8, fl10_9]
  simp only [sg10_w0_2, sg10_w0_3, sg10_w0_8, sg10_w0_9, SixQubit.signMul_false]
  try ring

theorem ex10_w11 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef10 w11 = star (c y3) * d z2 + star (c y4) * d z3 + star (c y9) * d z8 + star (c y10) * d z9 := by
  unfold offSum
  rw [incidence10]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl10_2, fl10_3, fl10_8, fl10_9]
  simp only [sg10_w11_2, sg10_w11_3, sg10_w11_8, sg10_w11_9, SixQubit.signMul_false]
  try ring

theorem ex10_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef10 w4 = - star (c y3) * d z2 - star (c y4) * d z3 - star (c y9) * d z8 - star (c y10) * d z9 := by
  unfold offSum
  rw [incidence10]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl10_2, fl10_3, fl10_8, fl10_9]
  simp only [sg10_w4_2, sg10_w4_3, sg10_w4_8, sg10_w4_9, SixQubit.signMul_true]
  try ring

theorem ex10_w14 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef10 w14 = - star (c y3) * d z2 - star (c y4) * d z3 - star (c y9) * d z8 - star (c y10) * d z9 := by
  unfold offSum
  rw [incidence10]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl10_2, fl10_3, fl10_8, fl10_9]
  simp only [sg10_w14_2, sg10_w14_3, sg10_w14_8, sg10_w14_9, SixQubit.signMul_true]
  try ring

theorem ex11_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef11 w0 = star (c y0) * d z7 + star (c y1) * d z8 + star (c y2) * d z9 + star (c y3) * d z10 + star (c y4) * d z11 + star (c y5) * d z12 := by
  unfold offSum
  rw [incidence11]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl11_7, fl11_8, fl11_9, fl11_10, fl11_11, fl11_12]
  simp only [sg11_w0_7, sg11_w0_8, sg11_w0_9, sg11_w0_10, sg11_w0_11, sg11_w0_12, SixQubit.signMul_false]
  try ring

theorem ex11_w15 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef11 w15 = - star (c y0) * d z7 - star (c y1) * d z8 - star (c y2) * d z9 - star (c y3) * d z10 - star (c y4) * d z11 - star (c y5) * d z12 := by
  unfold offSum
  rw [incidence11]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl11_7, fl11_8, fl11_9, fl11_10, fl11_11, fl11_12]
  simp only [sg11_w15_7, sg11_w15_8, sg11_w15_9, sg11_w15_10, sg11_w15_11, sg11_w15_12, SixQubit.signMul_true]
  try ring

theorem ex11_w11 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef11 w11 = star (c y0) * d z7 + star (c y1) * d z8 + star (c y2) * d z9 - star (c y3) * d z10 - star (c y4) * d z11 - star (c y5) * d z12 := by
  unfold offSum
  rw [incidence11]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl11_7, fl11_8, fl11_9, fl11_10, fl11_11, fl11_12]
  simp only [sg11_w11_7, sg11_w11_8, sg11_w11_9, sg11_w11_10, sg11_w11_11, sg11_w11_12, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex11_w7 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef11 w7 = star (c y0) * d z7 + star (c y1) * d z8 + star (c y2) * d z9 - star (c y3) * d z10 - star (c y4) * d z11 - star (c y5) * d z12 := by
  unfold offSum
  rw [incidence11]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl11_7, fl11_8, fl11_9, fl11_10, fl11_11, fl11_12]
  simp only [sg11_w7_7, sg11_w7_8, sg11_w7_9, sg11_w7_10, sg11_w7_11, sg11_w7_12, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex11_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef11 w4 = star (c y0) * d z7 - star (c y1) * d z8 - star (c y2) * d z9 + star (c y3) * d z10 + star (c y4) * d z11 - star (c y5) * d z12 := by
  unfold offSum
  rw [incidence11]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl11_7, fl11_8, fl11_9, fl11_10, fl11_11, fl11_12]
  simp only [sg11_w4_7, sg11_w4_8, sg11_w4_9, sg11_w4_10, sg11_w4_11, sg11_w4_12, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex11_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef11 w2 = star (c y0) * d z7 + star (c y1) * d z8 - star (c y2) * d z9 + star (c y3) * d z10 - star (c y4) * d z11 - star (c y5) * d z12 := by
  unfold offSum
  rw [incidence11]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl11_7, fl11_8, fl11_9, fl11_10, fl11_11, fl11_12]
  simp only [sg11_w2_7, sg11_w2_8, sg11_w2_9, sg11_w2_10, sg11_w2_11, sg11_w2_12, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex11_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef11 w1 = star (c y0) * d z7 - star (c y1) * d z8 + star (c y2) * d z9 - star (c y3) * d z10 + star (c y4) * d z11 - star (c y5) * d z12 := by
  unfold offSum
  rw [incidence11]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl11_7, fl11_8, fl11_9, fl11_10, fl11_11, fl11_12]
  simp only [sg11_w1_7, sg11_w1_8, sg11_w1_9, sg11_w1_10, sg11_w1_11, sg11_w1_12, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex12_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef12 w0 = star (c y6) * d z1 + star (c y8) * d z3 + star (c y9) * d z4 + star (c y11) * d z6 := by
  unfold offSum
  rw [incidence12]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl12_1, fl12_3, fl12_4, fl12_6]
  simp only [sg12_w0_1, sg12_w0_3, sg12_w0_4, sg12_w0_6, SixQubit.signMul_false]
  try ring

theorem ex12_w15 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef12 w15 = star (c y6) * d z1 + star (c y8) * d z3 + star (c y9) * d z4 + star (c y11) * d z6 := by
  unfold offSum
  rw [incidence12]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl12_1, fl12_3, fl12_4, fl12_6]
  simp only [sg12_w15_1, sg12_w15_3, sg12_w15_4, sg12_w15_6, SixQubit.signMul_false]
  try ring

theorem ex12_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef12 w1 = star (c y6) * d z1 + star (c y8) * d z3 + star (c y9) * d z4 + star (c y11) * d z6 := by
  unfold offSum
  rw [incidence12]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl12_1, fl12_3, fl12_4, fl12_6]
  simp only [sg12_w1_1, sg12_w1_3, sg12_w1_4, sg12_w1_6, SixQubit.signMul_false]
  try ring

theorem ex12_w16 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef12 w16 = star (c y6) * d z1 + star (c y8) * d z3 + star (c y9) * d z4 + star (c y11) * d z6 := by
  unfold offSum
  rw [incidence12]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl12_1, fl12_3, fl12_4, fl12_6]
  simp only [sg12_w16_1, sg12_w16_3, sg12_w16_4, sg12_w16_6, SixQubit.signMul_false]
  try ring

theorem ex13_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef13 w0 = star (c y7) * d z1 + star (c y8) * d z2 + star (c y10) * d z4 + star (c y11) * d z5 := by
  unfold offSum
  rw [incidence13]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl13_1, fl13_2, fl13_4, fl13_5]
  simp only [sg13_w0_1, sg13_w0_2, sg13_w0_4, sg13_w0_5, SixQubit.signMul_false]
  try ring

theorem ex13_w15 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef13 w15 = star (c y7) * d z1 + star (c y8) * d z2 + star (c y10) * d z4 + star (c y11) * d z5 := by
  unfold offSum
  rw [incidence13]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl13_1, fl13_2, fl13_4, fl13_5]
  simp only [sg13_w15_1, sg13_w15_2, sg13_w15_4, sg13_w15_5, SixQubit.signMul_false]
  try ring

theorem ex13_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef13 w2 = star (c y7) * d z1 + star (c y8) * d z2 + star (c y10) * d z4 + star (c y11) * d z5 := by
  unfold offSum
  rw [incidence13]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl13_1, fl13_2, fl13_4, fl13_5]
  simp only [sg13_w2_1, sg13_w2_2, sg13_w2_4, sg13_w2_5, SixQubit.signMul_false]
  try ring

theorem ex13_w17 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef13 w17 = star (c y7) * d z1 + star (c y8) * d z2 + star (c y10) * d z4 + star (c y11) * d z5 := by
  unfold offSum
  rw [incidence13]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl13_1, fl13_2, fl13_4, fl13_5]
  simp only [sg13_w17_1, sg13_w17_2, sg13_w17_4, sg13_w17_5, SixQubit.signMul_false]
  try ring

theorem ex14_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef14 w0 = star (c y6) * d z2 + star (c y7) * d z3 + star (c y9) * d z5 + star (c y10) * d z6 := by
  unfold offSum
  rw [incidence14]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl14_2, fl14_3, fl14_5, fl14_6]
  simp only [sg14_w0_2, sg14_w0_3, sg14_w0_5, sg14_w0_6, SixQubit.signMul_false]
  try ring

theorem ex14_w15 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef14 w15 = star (c y6) * d z2 + star (c y7) * d z3 + star (c y9) * d z5 + star (c y10) * d z6 := by
  unfold offSum
  rw [incidence14]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl14_2, fl14_3, fl14_5, fl14_6]
  simp only [sg14_w15_2, sg14_w15_3, sg14_w15_5, sg14_w15_6, SixQubit.signMul_false]
  try ring

theorem ex14_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef14 w4 = - star (c y6) * d z2 - star (c y7) * d z3 - star (c y9) * d z5 - star (c y10) * d z6 := by
  unfold offSum
  rw [incidence14]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl14_2, fl14_3, fl14_5, fl14_6]
  simp only [sg14_w4_2, sg14_w4_3, sg14_w4_5, sg14_w4_6, SixQubit.signMul_true]
  try ring

theorem ex14_w18 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef14 w18 = - star (c y6) * d z2 - star (c y7) * d z3 - star (c y9) * d z5 - star (c y10) * d z6 := by
  unfold offSum
  rw [incidence14]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl14_2, fl14_3, fl14_5, fl14_6]
  simp only [sg14_w18_2, sg14_w18_3, sg14_w18_5, sg14_w18_6, SixQubit.signMul_true]
  try ring

/-! ## Reciprocal pairs, star and sync -/

/-- The reciprocal pair at A_1. -/
theorem rec1 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef0 w0 = 0)
    : star (c y0) * d z0 + star (c y12) * d z12 = 0 := by
  rw [ex0_w0] at h0
  linear_combination (1 : ℂ) * h0

/-- The reciprocal pair at A_2. -/
theorem rec2 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef2 w0 = 0)
    : star (c y1) * d z0 + star (c y12) * d z11 = 0 := by
  rw [ex2_w0] at h0
  linear_combination (1 : ℂ) * h0

/-- The reciprocal pair at A_3. -/
theorem rec3 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef1 w0 = 0)
    : star (c y2) * d z0 + star (c y12) * d z10 = 0 := by
  rw [ex1_w0] at h0
  linear_combination (1 : ℂ) * h0

/-- The star relation of grid row 1. -/
theorem star1 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef11 w0 = 0)
    (h1 : offSum c d ef11 w11 = 0)
    : star (c y0) * d z7 + star (c y1) * d z8 + star (c y2) * d z9 = 0 := by
  rw [ex11_w0] at h0
  rw [ex11_w11] at h1
  linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- Sync of row 1 at A_1. -/
theorem sync1_1 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef11 w11 = 0)
    (h1 : offSum c d ef11 w4 = 0)
    : star (c y0) * d z7 = star (c y5) * d z12 := by
  rw [ex11_w11] at h0
  rw [ex11_w4] at h1
  linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- Sync of row 1 at A_2. -/
theorem sync1_2 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef11 w4 = 0)
    (h1 : offSum c d ef11 w2 = 0)
    : star (c y1) * d z8 = star (c y4) * d z11 := by
  rw [ex11_w4] at h0
  rw [ex11_w2] at h1
  linear_combination (-1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- Sync of row 1 at A_3. -/
theorem sync1_3 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef11 w11 = 0)
    (h1 : offSum c d ef11 w2 = 0)
    : star (c y2) * d z9 = star (c y3) * d z10 := by
  rw [ex11_w11] at h0
  rw [ex11_w2] at h1
  linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1

/-- The star relation of grid row 2. -/
theorem star2 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef7 w0 = 0)
    (h1 : offSum c d ef7 w15 = 0)
    : star (c y0) * d z4 + star (c y1) * d z5 + star (c y2) * d z6 = 0 := by
  rw [ex7_w0] at h0
  rw [ex7_w15] at h1
  linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- Sync of row 2 at A_1. -/
theorem sync2_1 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef7 w15 = 0)
    (h1 : offSum c d ef7 w4 = 0)
    : star (c y0) * d z4 = star (c y8) * d z12 := by
  rw [ex7_w15] at h0
  rw [ex7_w4] at h1
  linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- Sync of row 2 at A_2. -/
theorem sync2_2 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef7 w4 = 0)
    (h1 : offSum c d ef7 w2 = 0)
    : star (c y1) * d z5 = star (c y7) * d z11 := by
  rw [ex7_w4] at h0
  rw [ex7_w2] at h1
  linear_combination (-1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- Sync of row 2 at A_3. -/
theorem sync2_3 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef7 w15 = 0)
    (h1 : offSum c d ef7 w2 = 0)
    : star (c y2) * d z6 = star (c y6) * d z10 := by
  rw [ex7_w15] at h0
  rw [ex7_w2] at h1
  linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1

/-- The star relation of grid row 3. -/
theorem star3 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef3 w0 = 0)
    (h1 : offSum c d ef3 w15 = 0)
    : star (c y0) * d z1 + star (c y1) * d z2 + star (c y2) * d z3 = 0 := by
  rw [ex3_w0] at h0
  rw [ex3_w15] at h1
  linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- Sync of row 3 at A_1. -/
theorem sync3_1 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef3 w15 = 0)
    (h1 : offSum c d ef3 w4 = 0)
    : star (c y0) * d z1 = star (c y11) * d z12 := by
  rw [ex3_w15] at h0
  rw [ex3_w4] at h1
  linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- Sync of row 3 at A_2. -/
theorem sync3_2 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef3 w4 = 0)
    (h1 : offSum c d ef3 w2 = 0)
    : star (c y1) * d z2 = star (c y10) * d z11 := by
  rw [ex3_w4] at h0
  rw [ex3_w2] at h1
  linear_combination (-1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- Sync of row 3 at A_3. -/
theorem sync3_3 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef3 w15 = 0)
    (h1 : offSum c d ef3 w2 = 0)
    : star (c y2) * d z3 = star (c y9) * d z10 := by
  rw [ex3_w15] at h0
  rw [ex3_w2] at h1
  linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1

/-! ## The hub -/

/-- A grid point in an active column inherits the reciprocal relation with S. -/
theorem grid_rec (c d : SS.BitString 6 -> ℂ) (xa xb : SS.BitString 6)
    (ya yb : SS.BitString 6)
    (hrec : star (c xa) * d z0 + star (c y12) * d ya = 0)
    (hsync : star (c xa) * d yb = star (c xb) * d ya)
    (hne : c xa ≠ 0)
    : star (c xb) * d z0 + star (c y12) * d yb = 0 := by
  have key : (star (c xb) * d z0 + star (c y12) * d yb) * star (c xa) = 0 := by
    linear_combination (star (c xb)) * hrec + (star (c y12)) * hsync
  rcases mul_eq_zero.mp key with h | h
  · exact h
  · exact absurd (by simpa using congrArg star h) hne

/-- Two points reciprocally related to S have their cross products paired. -/
theorem hub (c d : SS.BitString 6 -> ℂ) (x1 x2 : SS.BitString 6)
    (yh1 yh2 : SS.BitString 6)
    (h1 : star (c x1) * d z0 + star (c y12) * d yh1 = 0)
    (h2 : star (c x2) * d z0 + star (c y12) * d yh2 = 0)
    (hs : star (c y12) * d z0 ≠ 0) :
    star (c x2) * d yh1 = star (c x1) * d yh2 := by
  have key : (star (c x2) * d yh1 - star (c x1) * d yh2) *
      (star (c y12) * d z0) = 0 := by
    linear_combination (star (c x2) * d z0) * h1 - (star (c x1) * d z0) * h2
  rcases mul_eq_zero.mp key with h | h
  · linear_combination h
  · exact absurd h hs

/-! ## The permanent collapse -/

/-- Rows 1,2 and columns 1,2: the four-term permanent, collapsed. -/
theorem perm1212 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef6 w0 = 0)
    (s1 : star (c y7) * d z9 = star (c y3) * d z5)
    (s2 : star (c y6) * d z8 = star (c y4) * d z6)
    : star (c y3) * d z5 + star (c y4) * d z6 = 0 := by
  rw [ex6_w0] at h0
  linear_combination (1 : ℂ) / 2 * h0 - s1 / 2 - s2 / 2

/-- Rows 1,2 and columns 1,3: the four-term permanent, collapsed. -/
theorem perm1213 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef4 w0 = 0)
    (s1 : star (c y8) * d z9 = star (c y3) * d z4)
    (s2 : star (c y6) * d z7 = star (c y5) * d z6)
    : star (c y3) * d z4 + star (c y5) * d z6 = 0 := by
  rw [ex4_w0] at h0
  linear_combination (1 : ℂ) / 2 * h0 - s1 / 2 - s2 / 2

/-- Rows 1,2 and columns 2,3: the four-term permanent, collapsed. -/
theorem perm1223 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef5 w0 = 0)
    (s1 : star (c y8) * d z8 = star (c y4) * d z4)
    (s2 : star (c y7) * d z7 = star (c y5) * d z5)
    : star (c y4) * d z4 + star (c y5) * d z5 = 0 := by
  rw [ex5_w0] at h0
  linear_combination (1 : ℂ) / 2 * h0 - s1 / 2 - s2 / 2

/-- Rows 1,3 and columns 1,2: the four-term permanent, collapsed. -/
theorem perm1312 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef10 w0 = 0)
    (s1 : star (c y10) * d z9 = star (c y3) * d z2)
    (s2 : star (c y9) * d z8 = star (c y4) * d z3)
    : star (c y3) * d z2 + star (c y4) * d z3 = 0 := by
  rw [ex10_w0] at h0
  linear_combination (1 : ℂ) / 2 * h0 - s1 / 2 - s2 / 2

/-- Rows 1,3 and columns 1,3: the four-term permanent, collapsed. -/
theorem perm1313 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef8 w0 = 0)
    (s1 : star (c y11) * d z9 = star (c y3) * d z1)
    (s2 : star (c y9) * d z7 = star (c y5) * d z3)
    : star (c y3) * d z1 + star (c y5) * d z3 = 0 := by
  rw [ex8_w0] at h0
  linear_combination (1 : ℂ) / 2 * h0 - s1 / 2 - s2 / 2

/-- Rows 1,3 and columns 2,3: the four-term permanent, collapsed. -/
theorem perm1323 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef9 w0 = 0)
    (s1 : star (c y11) * d z8 = star (c y4) * d z1)
    (s2 : star (c y10) * d z7 = star (c y5) * d z2)
    : star (c y4) * d z1 + star (c y5) * d z2 = 0 := by
  rw [ex9_w0] at h0
  linear_combination (1 : ℂ) / 2 * h0 - s1 / 2 - s2 / 2

/-- Rows 2,3 and columns 1,2: the four-term permanent, collapsed. -/
theorem perm2312 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef14 w0 = 0)
    (s1 : star (c y10) * d z6 = star (c y6) * d z2)
    (s2 : star (c y9) * d z5 = star (c y7) * d z3)
    : star (c y6) * d z2 + star (c y7) * d z3 = 0 := by
  rw [ex14_w0] at h0
  linear_combination (1 : ℂ) / 2 * h0 - s1 / 2 - s2 / 2

/-- Rows 2,3 and columns 1,3: the four-term permanent, collapsed. -/
theorem perm2313 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef12 w0 = 0)
    (s1 : star (c y11) * d z6 = star (c y6) * d z1)
    (s2 : star (c y9) * d z4 = star (c y8) * d z3)
    : star (c y6) * d z1 + star (c y8) * d z3 = 0 := by
  rw [ex12_w0] at h0
  linear_combination (1 : ℂ) / 2 * h0 - s1 / 2 - s2 / 2

/-- Rows 2,3 and columns 2,3: the four-term permanent, collapsed. -/
theorem perm2323 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef13 w0 = 0)
    (s1 : star (c y11) * d z5 = star (c y7) * d z1)
    (s2 : star (c y10) * d z4 = star (c y8) * d z2)
    : star (c y7) * d z1 + star (c y8) * d z2 = 0 := by
  rw [ex13_w0] at h0
  linear_combination (1 : ℂ) / 2 * h0 - s1 / 2 - s2 / 2

/-- Grid column 1 cannot vanish. -/
theorem col_dead_0 (c : SS.BitString 6 -> ℂ) (a b e : Real)
    (ea : a = Complex.normSq (c y3)) (eb : b = Complex.normSq (c y6))
    (ee : e = Complex.normSq (c y9)) (hb : 1/10 ≤ a + b + e)
    (z0 : c y3 = 0) (z1 : c y6 = 0) (z2 : c y9 = 0) : False := by
  rw [z0] at ea; rw [z1] at eb; rw [z2] at ee; simp at ea eb ee
  rw [ea, eb, ee] at hb; norm_num at hb

/-- Grid column 2 cannot vanish. -/
theorem col_dead_1 (c : SS.BitString 6 -> ℂ) (a b e : Real)
    (ea : a = Complex.normSq (c y4)) (eb : b = Complex.normSq (c y7))
    (ee : e = Complex.normSq (c y10)) (hb : 1/10 ≤ a + b + e)
    (z0 : c y4 = 0) (z1 : c y7 = 0) (z2 : c y10 = 0) : False := by
  rw [z0] at ea; rw [z1] at eb; rw [z2] at ee; simp at ea eb ee
  rw [ea, eb, ee] at hb; norm_num at hb

/-- Grid column 3 cannot vanish. -/
theorem col_dead_2 (c : SS.BitString 6 -> ℂ) (a b e : Real)
    (ea : a = Complex.normSq (c y5)) (eb : b = Complex.normSq (c y8))
    (ee : e = Complex.normSq (c y11)) (hb : 1/10 ≤ a + b + e)
    (z0 : c y5 = 0) (z1 : c y8 = 0) (z2 : c y11 = 0) : False := by
  rw [z0] at ea; rw [z1] at eb; rw [z2] at ee; simp at ea eb ee
  rw [ea, eb, ee] at hb; norm_num at hb

/-- A column that vanishes on the bottom fiber contradicts its weight bound. -/
theorem col_dead (c : SS.BitString 6 -> ℂ) (q0 q1 q2 : Real)
    (e0 : q0 = Complex.normSq (c y0)) (e1 : q1 = Complex.normSq (c y1))
    (e2 : q2 = Complex.normSq (c y2)) (hb : 1/10 ≤ q0 + q1 + q2)
    (z0 : c y0 = 0) (z1 : c y1 = 0) (z2 : c y2 = 0) : False := by
  rw [z0] at e0; rw [z1] at e1; rw [z2] at e2; simp at e0 e1 e2
  rw [e0, e1, e2] at hb; norm_num at hb

/-! ## From a collapsed permanent to the bottom grid -/

/-- With both partners tied to the star, a collapsed permanent becomes a
relation among bottom amplitudes alone. -/
theorem to_bottom (c d : SS.BitString 6 -> ℂ)
    (ua ub ue uf : SS.BitString 6) (bh fh : SS.BitString 6)
    (hb : star (c ub) * d z0 + star (c y12) * d bh = 0)
    (hf : star (c uf) * d z0 + star (c y12) * d fh = 0)
    (hs : d z0 ≠ 0)
    (hperm : star (c ua) * d bh + star (c ue) * d fh = 0)
    : star (c ua) * star (c ub) + star (c ue) * star (c uf) = 0 := by
  have key : (star (c ua) * star (c ub) + star (c ue) * star (c uf)) * d z0 = 0 := by
    linear_combination (star (c ua)) * hb + (star (c ue)) * hf
      - (star (c y12)) * hperm
  rcases mul_eq_zero.mp key with h | h
  · exact h
  · exact absurd h hs

/-! ## Two active columns -/

/-- Three two-by-two permanents on two columns, against the weight bounds. -/
theorem two_active (x1 x2 x3 y1 y2 y3 : ℂ)
    (X1 X2 X3 Y1 Y2 Y3 W1 W2 W3 : Real)
    (eX1 : X1 = Complex.normSq x1) (eX2 : X2 = Complex.normSq x2)
    (eX3 : X3 = Complex.normSq x3) (eY1 : Y1 = Complex.normSq y1)
    (eY2 : Y2 = Complex.normSq y2) (eY3 : Y3 = Complex.normSq y3)
    (nW1 : 0 ≤ W1) (nW2 : 0 ≤ W2) (nW3 : 0 ≤ W3)
    (r1 : X1 + Y1 + W1 = 1/5) (r2 : X2 + Y2 + W2 = 1/5) (r3 : X3 + Y3 + W3 = 1/5)
    (third : W1 + W2 + W3 = 1/10)
    (cX : 1/10 ≤ X1 + X2 + X3) (cY : 1/10 ≤ Y1 + Y2 + Y3)
    (R12 : x1 * y2 + x2 * y1 = 0) (R13 : x1 * y3 + x3 * y1 = 0)
    (R23 : x2 * y3 + x3 * y2 = 0) : False := by
  -- no entry of the first column vanishes
  have hx : ∀ (p : ℂ), p = 0 -> Complex.normSq p = 0 := fun p hp => by rw [hp]; simp
  have nx1 : x1 ≠ 0 := by
    intro hz
    by_cases hy : y1 = 0
    · rw [hx _ hz] at eX1; rw [hx _ hy] at eY1; linarith
    · have e2 : x2 = 0 := by
        rcases mul_eq_zero.mp (show x2 * y1 = 0 by rw [hz] at R12; linear_combination R12)
          with h | h
        · exact h
        · exact absurd h hy
      have e3 : x3 = 0 := by
        rcases mul_eq_zero.mp (show x3 * y1 = 0 by rw [hz] at R13; linear_combination R13)
          with h | h
        · exact h
        · exact absurd h hy
      rw [hx _ hz] at eX1; rw [hx _ e2] at eX2; rw [hx _ e3] at eX3; linarith
  have nx2 : x2 ≠ 0 := by
    intro hz
    by_cases hy : y2 = 0
    · rw [hx _ hz] at eX2; rw [hx _ hy] at eY2; linarith
    · have e1 : x1 = 0 := by
        rcases mul_eq_zero.mp (show x1 * y2 = 0 by rw [hz] at R12; linear_combination R12)
          with h | h
        · exact h
        · exact absurd h hy
      exact nx1 e1
  have nx3 : x3 ≠ 0 := by
    intro hz
    by_cases hy : y3 = 0
    · rw [hx _ hz] at eX3; rw [hx _ hy] at eY3; linarith
    · have e1 : x1 = 0 := by
        rcases mul_eq_zero.mp (show x1 * y3 = 0 by rw [hz] at R13; linear_combination R13)
          with h | h
        · exact h
        · exact absurd h hy
      exact nx1 e1
  -- and then none of the second column either
  have ny1 : y1 ≠ 0 := by
    intro hz
    have e2 : y2 = 0 := by
      rcases mul_eq_zero.mp (show x1 * y2 = 0 by rw [hz] at R12; linear_combination R12)
        with h | h
      · exact absurd h nx1
      · exact h
    have e3 : y3 = 0 := by
      rcases mul_eq_zero.mp (show x1 * y3 = 0 by rw [hz] at R13; linear_combination R13)
        with h | h
      · exact absurd h nx1
      · exact h
    rw [hx _ hz] at eY1; rw [hx _ e2] at eY2; rw [hx _ e3] at eY3; linarith
  have ny2 : y2 ≠ 0 := by
    intro hz
    rcases mul_eq_zero.mp (show x2 * y1 = 0 by rw [hz] at R12; linear_combination R12)
      with h | h
    · exact nx2 h
    · exact ny1 h
  have ny3 : y3 ≠ 0 := by
    intro hz
    rcases mul_eq_zero.mp (show x3 * y1 = 0 by rw [hz] at R13; linear_combination R13)
      with h | h
    · exact nx3 h
    · exact ny1 h
  -- the odd cycle
  have key : (2 : ℂ) * (x1 * y2 * (x2 * y3) * (x3 * y1)) = 0 := by
    linear_combination (x2 * y3 * (x3 * y1)) * R12 - (x2 * y1 * (x3 * y1)) * R23
      + (x2 * y1 * (x3 * y2)) * R13
  have hz : x1 * y2 * (x2 * y3) * (x3 * y1) = 0 := by linear_combination key / 2
  simp [nx1, nx2, nx3, ny1, ny2, ny3] at hz

/-! ## The conditional column pin -/

/-- If A_1 carries no weight, grid column 3 totals exactly one tenth. -/
theorem MomentSystem.pin0 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12)
    (hz : q0 = 0) : q5 + q8 + q11 = 1/10 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12⟩ := h
  linarith

/-- If A_2 carries no weight, grid column 2 totals exactly one tenth. -/
theorem MomentSystem.pin1 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12)
    (hz : q1 = 0) : q4 + q7 + q10 = 1/10 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12⟩ := h
  linarith

/-- If A_3 carries no weight, grid column 1 totals exactly one tenth. -/
theorem MomentSystem.pin2 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12)
    (hz : q2 = 0) : q3 + q6 + q9 = 1/10 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12⟩ := h
  linarith

/-! ## A vanishing grid entry empties a row or a column -/

/-- `a` is the entry, `b` and `e` its row-mates, `p` and `q` its column-mates. -/
theorem entry_ne (a b e p q : ℂ) (A Bv E P Qv : Real)
    (eA : A = Complex.normSq a) (eB : Bv = Complex.normSq b)
    (eE : E = Complex.normSq e) (eP : P = Complex.normSq p)
    (eQ : Qv = Complex.normSq q)
    (hrow : A + Bv + E = 1/5) (hcol : 1/10 ≤ A + P + Qv)
    (hbp : b * p = 0) (hbq : b * q = 0) (hep : e * p = 0) (heq : e * q = 0)
    (ha : a = 0) : False := by
  have hz : ∀ (t : ℂ), t = 0 -> Complex.normSq t = 0 := fun t ht => by rw [ht]; simp
  rw [hz _ ha] at eA
  by_cases hb : b = 0
  · by_cases he : e = 0
    · rw [hz _ hb] at eB; rw [hz _ he] at eE; linarith
    · have hp : p = 0 := by
        rcases mul_eq_zero.mp hep with h | h
        · exact absurd h he
        · exact h
      have hq : q = 0 := by
        rcases mul_eq_zero.mp heq with h | h
        · exact absurd h he
        · exact h
      rw [hz _ hp] at eP; rw [hz _ hq] at eQ; linarith
  · have hp : p = 0 := by
      rcases mul_eq_zero.mp hbp with h | h
      · exact absurd h hb
      · exact h
    have hq : q = 0 := by
      rcases mul_eq_zero.mp hbq with h | h
      · exact absurd h hb
      · exact h
    rw [hz _ hp] at eP; rw [hz _ hq] at eQ; linarith

/-! ## All three columns active -/

/-- Nine collapsed permanents against the row sums and the column bounds. -/
theorem three_active (m11 m12 m13 m21 m22 m23 m31 m32 m33 : ℂ)
    (M11 M12 M13 M21 M22 M23 M31 M32 M33 : Real)
    (e11 : M11 = Complex.normSq m11)
    (e12 : M12 = Complex.normSq m12)
    (e13 : M13 = Complex.normSq m13)
    (e21 : M21 = Complex.normSq m21)
    (e22 : M22 = Complex.normSq m22)
    (e23 : M23 = Complex.normSq m23)
    (e31 : M31 = Complex.normSq m31)
    (e32 : M32 = Complex.normSq m32)
    (e33 : M33 = Complex.normSq m33)
    (r1 : M11 + M12 + M13 = 1/5)
    (r2 : M21 + M22 + M23 = 1/5)
    (r3 : M31 + M32 + M33 = 1/5)
    (cc1 : 1/10 ≤ M11 + M21 + M31)
    (cc2 : 1/10 ≤ M12 + M22 + M32)
    (cc3 : 1/10 ≤ M13 + M23 + M33)
    (P1212 : m11 * m22 + m12 * m21 = 0)
    (P1213 : m11 * m23 + m13 * m21 = 0)
    (P1223 : m12 * m23 + m13 * m22 = 0)
    (P1312 : m11 * m32 + m12 * m31 = 0)
    (P1313 : m11 * m33 + m13 * m31 = 0)
    (P1323 : m12 * m33 + m13 * m32 = 0)
    (P2312 : m21 * m32 + m22 * m31 = 0)
    (P2313 : m21 * m33 + m23 * m31 = 0)
    (P2323 : m22 * m33 + m23 * m32 = 0)
    : False := by
  have n11 : m11 ≠ 0 := by
    intro hz
    have hbp : m12 * m21 = 0 := by
      rw [hz] at P1212; linear_combination P1212
    have hbq : m12 * m31 = 0 := by
      rw [hz] at P1312; linear_combination P1312
    have hep : m13 * m21 = 0 := by
      rw [hz] at P1213; linear_combination P1213
    have heq : m13 * m31 = 0 := by
      rw [hz] at P1313; linear_combination P1313
    exact entry_ne m11 m12 m13 m21 m31 M11 M12 M13 M21 M31
      e11 e12 e13 e21 e31 (by linarith [r1]) (by linarith [cc1])
      hbp hbq hep heq hz
  have n12 : m12 ≠ 0 := by
    intro hz
    have hbp : m11 * m22 = 0 := by
      rw [hz] at P1212; linear_combination P1212
    have hbq : m11 * m32 = 0 := by
      rw [hz] at P1312; linear_combination P1312
    have hep : m13 * m22 = 0 := by
      rw [hz] at P1223; linear_combination P1223
    have heq : m13 * m32 = 0 := by
      rw [hz] at P1323; linear_combination P1323
    exact entry_ne m12 m11 m13 m22 m32 M12 M11 M13 M22 M32
      e12 e11 e13 e22 e32 (by linarith [r1]) (by linarith [cc2])
      hbp hbq hep heq hz
  have n13 : m13 ≠ 0 := by
    intro hz
    have hbp : m11 * m23 = 0 := by
      rw [hz] at P1213; linear_combination P1213
    have hbq : m11 * m33 = 0 := by
      rw [hz] at P1313; linear_combination P1313
    have hep : m12 * m23 = 0 := by
      rw [hz] at P1223; linear_combination P1223
    have heq : m12 * m33 = 0 := by
      rw [hz] at P1323; linear_combination P1323
    exact entry_ne m13 m11 m12 m23 m33 M13 M11 M12 M23 M33
      e13 e11 e12 e23 e33 (by linarith [r1]) (by linarith [cc3])
      hbp hbq hep heq hz
  have n21 : m21 ≠ 0 := by
    intro hz
    have hbp : m22 * m11 = 0 := by
      rw [hz] at P1212; linear_combination P1212
    have hbq : m22 * m31 = 0 := by
      rw [hz] at P2312; linear_combination P2312
    have hep : m23 * m11 = 0 := by
      rw [hz] at P1213; linear_combination P1213
    have heq : m23 * m31 = 0 := by
      rw [hz] at P2313; linear_combination P2313
    exact entry_ne m21 m22 m23 m11 m31 M21 M22 M23 M11 M31
      e21 e22 e23 e11 e31 (by linarith [r2]) (by linarith [cc1])
      hbp hbq hep heq hz
  have n22 : m22 ≠ 0 := by
    intro hz
    have hbp : m21 * m12 = 0 := by
      rw [hz] at P1212; linear_combination P1212
    have hbq : m21 * m32 = 0 := by
      rw [hz] at P2312; linear_combination P2312
    have hep : m23 * m12 = 0 := by
      rw [hz] at P1223; linear_combination P1223
    have heq : m23 * m32 = 0 := by
      rw [hz] at P2323; linear_combination P2323
    exact entry_ne m22 m21 m23 m12 m32 M22 M21 M23 M12 M32
      e22 e21 e23 e12 e32 (by linarith [r2]) (by linarith [cc2])
      hbp hbq hep heq hz
  have n23 : m23 ≠ 0 := by
    intro hz
    have hbp : m21 * m13 = 0 := by
      rw [hz] at P1213; linear_combination P1213
    have hbq : m21 * m33 = 0 := by
      rw [hz] at P2313; linear_combination P2313
    have hep : m22 * m13 = 0 := by
      rw [hz] at P1223; linear_combination P1223
    have heq : m22 * m33 = 0 := by
      rw [hz] at P2323; linear_combination P2323
    exact entry_ne m23 m21 m22 m13 m33 M23 M21 M22 M13 M33
      e23 e21 e22 e13 e33 (by linarith [r2]) (by linarith [cc3])
      hbp hbq hep heq hz
  have n31 : m31 ≠ 0 := by
    intro hz
    have hbp : m32 * m11 = 0 := by
      rw [hz] at P1312; linear_combination P1312
    have hbq : m32 * m21 = 0 := by
      rw [hz] at P2312; linear_combination P2312
    have hep : m33 * m11 = 0 := by
      rw [hz] at P1313; linear_combination P1313
    have heq : m33 * m21 = 0 := by
      rw [hz] at P2313; linear_combination P2313
    exact entry_ne m31 m32 m33 m11 m21 M31 M32 M33 M11 M21
      e31 e32 e33 e11 e21 (by linarith [r3]) (by linarith [cc1])
      hbp hbq hep heq hz
  have n32 : m32 ≠ 0 := by
    intro hz
    have hbp : m31 * m12 = 0 := by
      rw [hz] at P1312; linear_combination P1312
    have hbq : m31 * m22 = 0 := by
      rw [hz] at P2312; linear_combination P2312
    have hep : m33 * m12 = 0 := by
      rw [hz] at P1323; linear_combination P1323
    have heq : m33 * m22 = 0 := by
      rw [hz] at P2323; linear_combination P2323
    exact entry_ne m32 m31 m33 m12 m22 M32 M31 M33 M12 M22
      e32 e31 e33 e12 e22 (by linarith [r3]) (by linarith [cc2])
      hbp hbq hep heq hz
  have n33 : m33 ≠ 0 := by
    intro hz
    have hbp : m31 * m13 = 0 := by
      rw [hz] at P1313; linear_combination P1313
    have hbq : m31 * m23 = 0 := by
      rw [hz] at P2313; linear_combination P2313
    have hep : m32 * m13 = 0 := by
      rw [hz] at P1323; linear_combination P1323
    have heq : m32 * m23 = 0 := by
      rw [hz] at P2323; linear_combination P2323
    exact entry_ne m33 m31 m32 m13 m23 M33 M31 M32 M13 M23
      e33 e31 e32 e13 e23 (by linarith [r3]) (by linarith [cc3])
      hbp hbq hep heq hz
  have key : (2 : ℂ) * (m11 * m22 * (m21 * m32) * (m31 * m12)) = 0 := by
    linear_combination (m21 * m32 * (m31 * m12)) * P1212
      - (m12 * m21 * (m31 * m12)) * P2312 + (m12 * m21 * (m31 * m22)) * P1312
  have hz : m11 * m22 * (m21 * m32) * (m31 * m12) = 0 := by linear_combination key / 2
  simp [n11, n12, n21, n22, n31, n32] at hz

/-! ## The no-go -/

set_option maxHeartbeats 4000000 in
/-- **Orbit 37 is impossible.** -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11)) (Complex.normSq (c y12))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)) (Complex.normSq (d z12)))
    (E0_w0 : offSum c d ef0 w0 = 0)
    (_E0_w2 : offSum c d ef0 w2 = 0)
    (_E0_w1 : offSum c d ef0 w1 = 0)
    (_E0_w3 : offSum c d ef0 w3 = 0)
    (E1_w0 : offSum c d ef1 w0 = 0)
    (_E1_w4 : offSum c d ef1 w4 = 0)
    (_E1_w1 : offSum c d ef1 w1 = 0)
    (_E1_w5 : offSum c d ef1 w5 = 0)
    (E2_w0 : offSum c d ef2 w0 = 0)
    (_E2_w4 : offSum c d ef2 w4 = 0)
    (_E2_w2 : offSum c d ef2 w2 = 0)
    (_E2_w6 : offSum c d ef2 w6 = 0)
    (E3_w0 : offSum c d ef3 w0 = 0)
    (E3_w15 : offSum c d ef3 w15 = 0)
    (_E3_w11 : offSum c d ef3 w11 = 0)
    (_E3_w7 : offSum c d ef3 w7 = 0)
    (E3_w4 : offSum c d ef3 w4 = 0)
    (E3_w2 : offSum c d ef3 w2 = 0)
    (_E3_w1 : offSum c d ef3 w1 = 0)
    (E4_w0 : offSum c d ef4 w0 = 0)
    (_E4_w7 : offSum c d ef4 w7 = 0)
    (_E4_w1 : offSum c d ef4 w1 = 0)
    (_E4_w8 : offSum c d ef4 w8 = 0)
    (E5_w0 : offSum c d ef5 w0 = 0)
    (_E5_w7 : offSum c d ef5 w7 = 0)
    (_E5_w2 : offSum c d ef5 w2 = 0)
    (_E5_w9 : offSum c d ef5 w9 = 0)
    (E6_w0 : offSum c d ef6 w0 = 0)
    (_E6_w7 : offSum c d ef6 w7 = 0)
    (_E6_w4 : offSum c d ef6 w4 = 0)
    (_E6_w10 : offSum c d ef6 w10 = 0)
    (E7_w0 : offSum c d ef7 w0 = 0)
    (E7_w15 : offSum c d ef7 w15 = 0)
    (_E7_w11 : offSum c d ef7 w11 = 0)
    (_E7_w7 : offSum c d ef7 w7 = 0)
    (E7_w4 : offSum c d ef7 w4 = 0)
    (E7_w2 : offSum c d ef7 w2 = 0)
    (_E7_w1 : offSum c d ef7 w1 = 0)
    (E8_w0 : offSum c d ef8 w0 = 0)
    (_E8_w11 : offSum c d ef8 w11 = 0)
    (_E8_w1 : offSum c d ef8 w1 = 0)
    (_E8_w12 : offSum c d ef8 w12 = 0)
    (E9_w0 : offSum c d ef9 w0 = 0)
    (_E9_w11 : offSum c d ef9 w11 = 0)
    (_E9_w2 : offSum c d ef9 w2 = 0)
    (_E9_w13 : offSum c d ef9 w13 = 0)
    (E10_w0 : offSum c d ef10 w0 = 0)
    (_E10_w11 : offSum c d ef10 w11 = 0)
    (_E10_w4 : offSum c d ef10 w4 = 0)
    (_E10_w14 : offSum c d ef10 w14 = 0)
    (E11_w0 : offSum c d ef11 w0 = 0)
    (_E11_w15 : offSum c d ef11 w15 = 0)
    (E11_w11 : offSum c d ef11 w11 = 0)
    (_E11_w7 : offSum c d ef11 w7 = 0)
    (E11_w4 : offSum c d ef11 w4 = 0)
    (E11_w2 : offSum c d ef11 w2 = 0)
    (_E11_w1 : offSum c d ef11 w1 = 0)
    (E12_w0 : offSum c d ef12 w0 = 0)
    (_E12_w15 : offSum c d ef12 w15 = 0)
    (_E12_w1 : offSum c d ef12 w1 = 0)
    (_E12_w16 : offSum c d ef12 w16 = 0)
    (E13_w0 : offSum c d ef13 w0 = 0)
    (_E13_w15 : offSum c d ef13 w15 = 0)
    (_E13_w2 : offSum c d ef13 w2 = 0)
    (_E13_w17 : offSum c d ef13 w17 = 0)
    (E14_w0 : offSum c d ef14 w0 = 0)
    (_E14_w15 : offSum c d ef14 w15 = 0)
    (_E14_w4 : offSum c d ef14 w4 = 0)
    (_E14_w18 : offSum c d ef14 w18 = 0)
    : False := by
  obtain ⟨fqS, frS, fA, ftA, fb0, fb1, fb2, ft0, ft1, ft2⟩ := hm.facts
  obtain ⟨fc0, fc1, fc2⟩ := hm.columns
  have hcS : c y12 ≠ 0 := fun h => by rw [h] at fqS; norm_num at fqS
  have hdS : d z0 ≠ 0 := fun h => by rw [h] at frS; norm_num at frS
  have C1 := rec1 c d E0_w0
  have C2 := rec2 c d E2_w0
  have C3 := rec3 c d E1_w0
  have T1 := star1 c d E11_w0 E11_w11
  have Y11 := sync1_1 c d E11_w11 E11_w4
  have Y12 := sync1_2 c d E11_w4 E11_w2
  have Y13 := sync1_3 c d E11_w11 E11_w2
  have T2 := star2 c d E7_w0 E7_w15
  have Y21 := sync2_1 c d E7_w15 E7_w4
  have Y22 := sync2_2 c d E7_w4 E7_w2
  have Y23 := sync2_3 c d E7_w15 E7_w2
  have T3 := star3 c d E3_w0 E3_w15
  have Y31 := sync3_1 c d E3_w15 E3_w4
  have Y32 := sync3_2 c d E3_w4 E3_w2
  have Y33 := sync3_3 c d E3_w15 E3_w2
  -- the case analysis on which A-amplitudes vanish
  by_cases h0 : c y0 = 0
  · by_cases h1 : c y1 = 0
    · by_cases h2 : c y2 = 0
      · -- J is empty
        have e0 : Complex.normSq (c y0) = 0 := by rw [h0]; simp
        have e1 : Complex.normSq (c y1) = 0 := by rw [h1]; simp
        have e2 : Complex.normSq (c y2) = 0 := by rw [h2]; simp
        rw [e0, e1, e2] at fA; norm_num at fA
      · -- J = {3}
        -- J = {3}: only A_3 survives
        have e0 : Complex.normSq (c y0) = 0 := by rw [h0]; simp
        have e1 : Complex.normSq (c y1) = 0 := by rw [h1]; simp
        have hAk : star (c y2) ≠ 0 := fun hz =>
          h2 (by simpa using congrArg star hz)
        have hvA : d z10 ≠ 0 := by
          intro hz
          have hp : star (c y2) * d z0 = 0 := by
            rw [hz] at C3; linear_combination C3
          rcases mul_eq_zero.mp hp with hh | hh
          · exact hAk hh
          · exact hdS hh
        have V0 : d z9 = 0 := by
          have z0a : star (c y0) = 0 := by rw [h0]; simp
          have z0b : star (c y1) = 0 := by rw [h1]; simp
          have hk : star (c y2) * d z9 = 0 := by
            linear_combination T1 - (d z7) * z0a - (d z8) * z0b
          rcases mul_eq_zero.mp hk with hh | hh
          · exact absurd hh hAk
          · exact hh
        have Bz0 : c y3 = 0 := by
          have hs := Y13
          have hp : star (c y3) * d z10 = 0 := by
            rw [V0] at hs; linear_combination -hs
          rcases mul_eq_zero.mp hp with hh | hh
          · simpa using congrArg star hh
          · exact absurd hh hvA
        have V1 : d z6 = 0 := by
          have z1a : star (c y0) = 0 := by rw [h0]; simp
          have z1b : star (c y1) = 0 := by rw [h1]; simp
          have hk : star (c y2) * d z6 = 0 := by
            linear_combination T2 - (d z4) * z1a - (d z5) * z1b
          rcases mul_eq_zero.mp hk with hh | hh
          · exact absurd hh hAk
          · exact hh
        have Bz1 : c y6 = 0 := by
          have hs := Y23
          have hp : star (c y6) * d z10 = 0 := by
            rw [V1] at hs; linear_combination -hs
          rcases mul_eq_zero.mp hp with hh | hh
          · simpa using congrArg star hh
          · exact absurd hh hvA
        have V2 : d z3 = 0 := by
          have z2a : star (c y0) = 0 := by rw [h0]; simp
          have z2b : star (c y1) = 0 := by rw [h1]; simp
          have hk : star (c y2) * d z3 = 0 := by
            linear_combination T3 - (d z1) * z2a - (d z2) * z2b
          rcases mul_eq_zero.mp hk with hh | hh
          · exact absurd hh hAk
          · exact hh
        have Bz2 : c y9 = 0 := by
          have hs := Y33
          have hp : star (c y9) * d z10 = 0 := by
            rw [V2] at hs; linear_combination -hs
          rcases mul_eq_zero.mp hp with hh | hh
          · simpa using congrArg star hh
          · exact absurd hh hvA
        exact col_dead_0 c _ _ _ rfl rfl rfl fc0 Bz0 Bz1 Bz2
    · by_cases h2 : c y2 = 0
      · -- J = {2}
        -- J = {2}: only A_2 survives
        have e0 : Complex.normSq (c y0) = 0 := by rw [h0]; simp
        have e2 : Complex.normSq (c y2) = 0 := by rw [h2]; simp
        have hAk : star (c y1) ≠ 0 := fun hz =>
          h1 (by simpa using congrArg star hz)
        have hvA : d z11 ≠ 0 := by
          intro hz
          have hp : star (c y1) * d z0 = 0 := by
            rw [hz] at C2; linear_combination C2
          rcases mul_eq_zero.mp hp with hh | hh
          · exact hAk hh
          · exact hdS hh
        have V0 : d z8 = 0 := by
          have z0a : star (c y0) = 0 := by rw [h0]; simp
          have z0b : star (c y2) = 0 := by rw [h2]; simp
          have hk : star (c y1) * d z8 = 0 := by
            linear_combination T1 - (d z7) * z0a - (d z9) * z0b
          rcases mul_eq_zero.mp hk with hh | hh
          · exact absurd hh hAk
          · exact hh
        have Bz0 : c y4 = 0 := by
          have hs := Y12
          have hp : star (c y4) * d z11 = 0 := by
            rw [V0] at hs; linear_combination -hs
          rcases mul_eq_zero.mp hp with hh | hh
          · simpa using congrArg star hh
          · exact absurd hh hvA
        have V1 : d z5 = 0 := by
          have z1a : star (c y0) = 0 := by rw [h0]; simp
          have z1b : star (c y2) = 0 := by rw [h2]; simp
          have hk : star (c y1) * d z5 = 0 := by
            linear_combination T2 - (d z4) * z1a - (d z6) * z1b
          rcases mul_eq_zero.mp hk with hh | hh
          · exact absurd hh hAk
          · exact hh
        have Bz1 : c y7 = 0 := by
          have hs := Y22
          have hp : star (c y7) * d z11 = 0 := by
            rw [V1] at hs; linear_combination -hs
          rcases mul_eq_zero.mp hp with hh | hh
          · simpa using congrArg star hh
          · exact absurd hh hvA
        have V2 : d z2 = 0 := by
          have z2a : star (c y0) = 0 := by rw [h0]; simp
          have z2b : star (c y2) = 0 := by rw [h2]; simp
          have hk : star (c y1) * d z2 = 0 := by
            linear_combination T3 - (d z1) * z2a - (d z3) * z2b
          rcases mul_eq_zero.mp hk with hh | hh
          · exact absurd hh hAk
          · exact hh
        have Bz2 : c y10 = 0 := by
          have hs := Y32
          have hp : star (c y10) * d z11 = 0 := by
            rw [V2] at hs; linear_combination -hs
          rcases mul_eq_zero.mp hp with hh | hh
          · simpa using congrArg star hh
          · exact absurd hh hvA
        exact col_dead_1 c _ _ _ rfl rfl rfl fc1 Bz0 Bz1 Bz2
      · -- J = {2,3}
        -- J = {2,3}: columns 2 and 1 are active
        have hz3 : Complex.normSq (c y0) = 0 := by rw [h0]; simp
        have hpin := hm.pin0 hz3
        have hA1 : c y1 ≠ 0 := h1
        have G10 := grid_rec c d y1 y4 z11 z8 C2 Y12 hA1
        have G11 := grid_rec c d y1 y7 z11 z5 C2 Y22 hA1
        have G12 := grid_rec c d y1 y10 z11 z2 C2 Y32 hA1
        have hA2 : c y2 ≠ 0 := h2
        have G20 := grid_rec c d y2 y3 z10 z9 C3 Y13 hA2
        have G21 := grid_rec c d y2 y6 z10 z6 C3 Y23 hA2
        have G22 := grid_rec c d y2 y9 z10 z3 C3 Y33 hA2
        have hstar : star (c y12) * d z0 ≠ 0 :=
          mul_ne_zero (star_ne_zero.mpr hcS) hdS
        have S01a := hub c d y3 y7 z9 z5 G20 G11 hstar
        have S01b := hub c d y4 y6 z8 z6 G10 G21 hstar
        have Pm01 := perm1212 c d E6_w0 S01a S01b
        have Q01 := to_bottom c d y3 y7 y4 y6 z5 z6 G11 G21 hdS Pm01
        have S02a := hub c d y3 y10 z9 z2 G20 G12 hstar
        have S02b := hub c d y4 y9 z8 z3 G10 G22 hstar
        have Pm02 := perm1312 c d E10_w0 S02a S02b
        have Q02 := to_bottom c d y3 y10 y4 y9 z2 z3 G12 G22 hdS Pm02
        have S12a := hub c d y6 y10 z6 z2 G21 G12 hstar
        have S12b := hub c d y7 y9 z5 z3 G11 G22 hstar
        have Pm12 := perm2312 c d E14_w0 S12a S12b
        have Q12 := to_bottom c d y6 y10 y7 y9 z2 z3 G12 G22 hdS Pm12
        exact two_active (star (c y3)) (star (c y6)) (star (c y9))
          (star (c y4)) (star (c y7)) (star (c y10))
          (Complex.normSq (c y3)) (Complex.normSq (c y6)) (Complex.normSq (c y9))
          (Complex.normSq (c y4)) (Complex.normSq (c y7)) (Complex.normSq (c y10))
          (Complex.normSq (c y5)) (Complex.normSq (c y8)) (Complex.normSq (c y11))
          (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
          (Complex.normSq_nonneg _) (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
          (by linarith [fb0]) (by linarith [fb1]) (by linarith [fb2])
          (by linarith [hpin]) (by linarith [fc0]) (by linarith [fc1])
          (by linear_combination Q01) (by linear_combination Q02)
          (by linear_combination Q12)
  · by_cases h1 : c y1 = 0
    · by_cases h2 : c y2 = 0
      · -- J = {1}
        -- J = {1}: only A_1 survives
        have e1 : Complex.normSq (c y1) = 0 := by rw [h1]; simp
        have e2 : Complex.normSq (c y2) = 0 := by rw [h2]; simp
        have hAk : star (c y0) ≠ 0 := fun hz =>
          h0 (by simpa using congrArg star hz)
        have hvA : d z12 ≠ 0 := by
          intro hz
          have hp : star (c y0) * d z0 = 0 := by
            rw [hz] at C1; linear_combination C1
          rcases mul_eq_zero.mp hp with hh | hh
          · exact hAk hh
          · exact hdS hh
        have V0 : d z7 = 0 := by
          have z0a : star (c y1) = 0 := by rw [h1]; simp
          have z0b : star (c y2) = 0 := by rw [h2]; simp
          have hk : star (c y0) * d z7 = 0 := by
            linear_combination T1 - (d z8) * z0a - (d z9) * z0b
          rcases mul_eq_zero.mp hk with hh | hh
          · exact absurd hh hAk
          · exact hh
        have Bz0 : c y5 = 0 := by
          have hs := Y11
          have hp : star (c y5) * d z12 = 0 := by
            rw [V0] at hs; linear_combination -hs
          rcases mul_eq_zero.mp hp with hh | hh
          · simpa using congrArg star hh
          · exact absurd hh hvA
        have V1 : d z4 = 0 := by
          have z1a : star (c y1) = 0 := by rw [h1]; simp
          have z1b : star (c y2) = 0 := by rw [h2]; simp
          have hk : star (c y0) * d z4 = 0 := by
            linear_combination T2 - (d z5) * z1a - (d z6) * z1b
          rcases mul_eq_zero.mp hk with hh | hh
          · exact absurd hh hAk
          · exact hh
        have Bz1 : c y8 = 0 := by
          have hs := Y21
          have hp : star (c y8) * d z12 = 0 := by
            rw [V1] at hs; linear_combination -hs
          rcases mul_eq_zero.mp hp with hh | hh
          · simpa using congrArg star hh
          · exact absurd hh hvA
        have V2 : d z1 = 0 := by
          have z2a : star (c y1) = 0 := by rw [h1]; simp
          have z2b : star (c y2) = 0 := by rw [h2]; simp
          have hk : star (c y0) * d z1 = 0 := by
            linear_combination T3 - (d z2) * z2a - (d z3) * z2b
          rcases mul_eq_zero.mp hk with hh | hh
          · exact absurd hh hAk
          · exact hh
        have Bz2 : c y11 = 0 := by
          have hs := Y31
          have hp : star (c y11) * d z12 = 0 := by
            rw [V2] at hs; linear_combination -hs
          rcases mul_eq_zero.mp hp with hh | hh
          · simpa using congrArg star hh
          · exact absurd hh hvA
        exact col_dead_2 c _ _ _ rfl rfl rfl fc2 Bz0 Bz1 Bz2
      · -- J = {1,3}
        -- J = {1,3}: columns 3 and 1 are active
        have hz3 : Complex.normSq (c y1) = 0 := by rw [h1]; simp
        have hpin := hm.pin1 hz3
        have hA0 : c y0 ≠ 0 := h0
        have G00 := grid_rec c d y0 y5 z12 z7 C1 Y11 hA0
        have G01 := grid_rec c d y0 y8 z12 z4 C1 Y21 hA0
        have G02 := grid_rec c d y0 y11 z12 z1 C1 Y31 hA0
        have hA2 : c y2 ≠ 0 := h2
        have G20 := grid_rec c d y2 y3 z10 z9 C3 Y13 hA2
        have G21 := grid_rec c d y2 y6 z10 z6 C3 Y23 hA2
        have G22 := grid_rec c d y2 y9 z10 z3 C3 Y33 hA2
        have hstar : star (c y12) * d z0 ≠ 0 :=
          mul_ne_zero (star_ne_zero.mpr hcS) hdS
        have S01a := hub c d y3 y8 z9 z4 G20 G01 hstar
        have S01b := hub c d y5 y6 z7 z6 G00 G21 hstar
        have Pm01 := perm1213 c d E4_w0 S01a S01b
        have Q01 := to_bottom c d y3 y8 y5 y6 z4 z6 G01 G21 hdS Pm01
        have S02a := hub c d y3 y11 z9 z1 G20 G02 hstar
        have S02b := hub c d y5 y9 z7 z3 G00 G22 hstar
        have Pm02 := perm1313 c d E8_w0 S02a S02b
        have Q02 := to_bottom c d y3 y11 y5 y9 z1 z3 G02 G22 hdS Pm02
        have S12a := hub c d y6 y11 z6 z1 G21 G02 hstar
        have S12b := hub c d y8 y9 z4 z3 G01 G22 hstar
        have Pm12 := perm2313 c d E12_w0 S12a S12b
        have Q12 := to_bottom c d y6 y11 y8 y9 z1 z3 G02 G22 hdS Pm12
        exact two_active (star (c y3)) (star (c y6)) (star (c y9))
          (star (c y5)) (star (c y8)) (star (c y11))
          (Complex.normSq (c y3)) (Complex.normSq (c y6)) (Complex.normSq (c y9))
          (Complex.normSq (c y5)) (Complex.normSq (c y8)) (Complex.normSq (c y11))
          (Complex.normSq (c y4)) (Complex.normSq (c y7)) (Complex.normSq (c y10))
          (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
          (Complex.normSq_nonneg _) (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
          (by linarith [fb0]) (by linarith [fb1]) (by linarith [fb2])
          (by linarith [hpin]) (by linarith [fc0]) (by linarith [fc2])
          (by linear_combination Q01) (by linear_combination Q02)
          (by linear_combination Q12)
    · by_cases h2 : c y2 = 0
      · -- J = {1,2}
        -- J = {1,2}: columns 3 and 2 are active
        have hz3 : Complex.normSq (c y2) = 0 := by rw [h2]; simp
        have hpin := hm.pin2 hz3
        have hA0 : c y0 ≠ 0 := h0
        have G00 := grid_rec c d y0 y5 z12 z7 C1 Y11 hA0
        have G01 := grid_rec c d y0 y8 z12 z4 C1 Y21 hA0
        have G02 := grid_rec c d y0 y11 z12 z1 C1 Y31 hA0
        have hA1 : c y1 ≠ 0 := h1
        have G10 := grid_rec c d y1 y4 z11 z8 C2 Y12 hA1
        have G11 := grid_rec c d y1 y7 z11 z5 C2 Y22 hA1
        have G12 := grid_rec c d y1 y10 z11 z2 C2 Y32 hA1
        have hstar : star (c y12) * d z0 ≠ 0 :=
          mul_ne_zero (star_ne_zero.mpr hcS) hdS
        have S01a := hub c d y4 y8 z8 z4 G10 G01 hstar
        have S01b := hub c d y5 y7 z7 z5 G00 G11 hstar
        have Pm01 := perm1223 c d E5_w0 S01a S01b
        have Q01 := to_bottom c d y4 y8 y5 y7 z4 z5 G01 G11 hdS Pm01
        have S02a := hub c d y4 y11 z8 z1 G10 G02 hstar
        have S02b := hub c d y5 y10 z7 z2 G00 G12 hstar
        have Pm02 := perm1323 c d E9_w0 S02a S02b
        have Q02 := to_bottom c d y4 y11 y5 y10 z1 z2 G02 G12 hdS Pm02
        have S12a := hub c d y7 y11 z5 z1 G11 G02 hstar
        have S12b := hub c d y8 y10 z4 z2 G01 G12 hstar
        have Pm12 := perm2323 c d E13_w0 S12a S12b
        have Q12 := to_bottom c d y7 y11 y8 y10 z1 z2 G02 G12 hdS Pm12
        exact two_active (star (c y4)) (star (c y7)) (star (c y10))
          (star (c y5)) (star (c y8)) (star (c y11))
          (Complex.normSq (c y4)) (Complex.normSq (c y7)) (Complex.normSq (c y10))
          (Complex.normSq (c y5)) (Complex.normSq (c y8)) (Complex.normSq (c y11))
          (Complex.normSq (c y3)) (Complex.normSq (c y6)) (Complex.normSq (c y9))
          (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
          (Complex.normSq_nonneg _) (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
          (by linarith [fb0]) (by linarith [fb1]) (by linarith [fb2])
          (by linarith [hpin]) (by linarith [fc1]) (by linarith [fc2])
          (by linear_combination Q01) (by linear_combination Q02)
          (by linear_combination Q12)
      · -- J = {1,2,3}
        -- J = {1,2,3}: every column is active
        have hA0 : c y0 ≠ 0 := h0
        have G00 := grid_rec c d y0 y5 z12 z7 C1 Y11 hA0
        have G01 := grid_rec c d y0 y8 z12 z4 C1 Y21 hA0
        have G02 := grid_rec c d y0 y11 z12 z1 C1 Y31 hA0
        have hA1 : c y1 ≠ 0 := h1
        have G10 := grid_rec c d y1 y4 z11 z8 C2 Y12 hA1
        have G11 := grid_rec c d y1 y7 z11 z5 C2 Y22 hA1
        have G12 := grid_rec c d y1 y10 z11 z2 C2 Y32 hA1
        have hA2 : c y2 ≠ 0 := h2
        have G20 := grid_rec c d y2 y3 z10 z9 C3 Y13 hA2
        have G21 := grid_rec c d y2 y6 z10 z6 C3 Y23 hA2
        have G22 := grid_rec c d y2 y9 z10 z3 C3 Y33 hA2
        have hstar : star (c y12) * d z0 ≠ 0 :=
          mul_ne_zero (star_ne_zero.mpr hcS) hdS
        have S0101a := hub c d y3 y7 z9 z5 G20 G11 hstar
        have S0101b := hub c d y4 y6 z8 z6 G10 G21 hstar
        have Pm0101 := perm1212 c d E6_w0 S0101a S0101b
        have Q0101 := to_bottom c d y3 y7 y4 y6 z5 z6 G11 G21 hdS Pm0101
        have S0102a := hub c d y3 y8 z9 z4 G20 G01 hstar
        have S0102b := hub c d y5 y6 z7 z6 G00 G21 hstar
        have Pm0102 := perm1213 c d E4_w0 S0102a S0102b
        have Q0102 := to_bottom c d y3 y8 y5 y6 z4 z6 G01 G21 hdS Pm0102
        have S0112a := hub c d y4 y8 z8 z4 G10 G01 hstar
        have S0112b := hub c d y5 y7 z7 z5 G00 G11 hstar
        have Pm0112 := perm1223 c d E5_w0 S0112a S0112b
        have Q0112 := to_bottom c d y4 y8 y5 y7 z4 z5 G01 G11 hdS Pm0112
        have S0201a := hub c d y3 y10 z9 z2 G20 G12 hstar
        have S0201b := hub c d y4 y9 z8 z3 G10 G22 hstar
        have Pm0201 := perm1312 c d E10_w0 S0201a S0201b
        have Q0201 := to_bottom c d y3 y10 y4 y9 z2 z3 G12 G22 hdS Pm0201
        have S0202a := hub c d y3 y11 z9 z1 G20 G02 hstar
        have S0202b := hub c d y5 y9 z7 z3 G00 G22 hstar
        have Pm0202 := perm1313 c d E8_w0 S0202a S0202b
        have Q0202 := to_bottom c d y3 y11 y5 y9 z1 z3 G02 G22 hdS Pm0202
        have S0212a := hub c d y4 y11 z8 z1 G10 G02 hstar
        have S0212b := hub c d y5 y10 z7 z2 G00 G12 hstar
        have Pm0212 := perm1323 c d E9_w0 S0212a S0212b
        have Q0212 := to_bottom c d y4 y11 y5 y10 z1 z2 G02 G12 hdS Pm0212
        have S1201a := hub c d y6 y10 z6 z2 G21 G12 hstar
        have S1201b := hub c d y7 y9 z5 z3 G11 G22 hstar
        have Pm1201 := perm2312 c d E14_w0 S1201a S1201b
        have Q1201 := to_bottom c d y6 y10 y7 y9 z2 z3 G12 G22 hdS Pm1201
        have S1202a := hub c d y6 y11 z6 z1 G21 G02 hstar
        have S1202b := hub c d y8 y9 z4 z3 G01 G22 hstar
        have Pm1202 := perm2313 c d E12_w0 S1202a S1202b
        have Q1202 := to_bottom c d y6 y11 y8 y9 z1 z3 G02 G22 hdS Pm1202
        have S1212a := hub c d y7 y11 z5 z1 G11 G02 hstar
        have S1212b := hub c d y8 y10 z4 z2 G01 G12 hstar
        have Pm1212 := perm2323 c d E13_w0 S1212a S1212b
        have Q1212 := to_bottom c d y7 y11 y8 y10 z1 z2 G02 G12 hdS Pm1212
        exact three_active (star (c y3)) (star (c y4)) (star (c y5)) (star (c y6)) (star (c y7)) (star (c y8)) (star (c y9)) (star (c y10)) (star (c y11))
          (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11))
          (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
          (by linarith [fb0]) (by linarith [fb1]) (by linarith [fb2])
          (by linarith [fc0]) (by linarith [fc1]) (by linarith [fc2])
          (by linear_combination Q0101) (by linear_combination Q0102) (by linear_combination Q0112) (by linear_combination Q0201) (by linear_combination Q0202)
          (by linear_combination Q0212) (by linear_combination Q1201) (by linear_combination Q1202) (by linear_combination Q1212)
end

end SixQubit.Orbit37
