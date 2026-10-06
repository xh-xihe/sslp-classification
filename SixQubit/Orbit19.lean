import Mathlib

import SS.FullKL
import SixQubit.Common

/-!
# Six-qubit no-go for moment orbit 19

Orbit 19 of `six_qubit_sslp.tex`: q = 4, angle vector
a = (1, 1, 1, 1, 2, 2), residues 0 and 2.

Coordinates 5 and 6 are both half-angle, so each of the flip masks
`efA = 000010` and `efB = 000001` is a bijection from the bottom fiber to
the top fiber.  For each mask the twelve admissible dressings span the
four restricted product projectors of the paper, and each of those
isolates a single anchor incidence.  The eight isolated monomials are
exactly the four products between the two bottom `w = 0` anchors and the
two top `w = 0` anchors, together with the same four at `w = 4`.

The pure-`Z` (moment) layer forces `P0 = Q0`, `P4 = Q4` and
`P0 + P4 = 1/2` for the anchor masses.  The vanishing products give
`P0 * Q0 = 0` and `P4 * Q4 = 0`, hence `P0 = P4 = 0`, contradicting the
half-mass identity.

Everything computational is decided by the Lean kernel; `native_decide`
is not used.
-/

namespace SixQubit.Orbit19

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

/-! ## The two fibers -/

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

def z0 : SS.BitString 6 := bs false false false false false true   -- 000001
def z1 : SS.BitString 6 := bs false false false false true  false  -- 000010
def z2 : SS.BitString 6 := bs false false true  true  false false  -- 001100
def z3 : SS.BitString 6 := bs false false true  true  true  true   -- 001111
def z4 : SS.BitString 6 := bs false true  false true  false false  -- 010100
def z5 : SS.BitString 6 := bs false true  false true  true  true   -- 010111
def z6 : SS.BitString 6 := bs false true  true  false false false  -- 011000
def z7 : SS.BitString 6 := bs false true  true  false true  true   -- 011011
def z8 : SS.BitString 6 := bs true  false false true  false false  -- 100100
def z9 : SS.BitString 6 := bs true  false false true  true  true   -- 100111
def z10 : SS.BitString 6 := bs true  false true  false false false  -- 101000
def z11 : SS.BitString 6 := bs true  false true  false true  true   -- 101011
def z12 : SS.BitString 6 := bs true  true  false false false false  -- 110000
def z13 : SS.BitString 6 := bs true  true  false false true  true   -- 110011
def z14 : SS.BitString 6 := bs true  true  true  true  false true   -- 111101
def z15 : SS.BitString 6 := bs true  true  true  true  true  false  -- 111110

def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15}
def S1 : Finset (SS.BitString 6) := {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15}

def av : Fin 6 -> ZMod 4 := ![1, 1, 1, 1, 2, 2]

theorem S0_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 0) = S0 := by
  decide

theorem S1_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 2) = S1 := by
  decide

/-! ## Two elementary facts about squared moduli -/

theorem nsqStar (a b : ℂ) :
    Complex.normSq (star a * b) = Complex.normSq a * Complex.normSq b := by
  rw [Complex.normSq_mul, Complex.star_def, Complex.normSq_conj]

theorem nsqZero {a b : ℂ} (h : star a * b = 0) :
    Complex.normSq a * Complex.normSq b = 0 := by
  rw [← nsqStar, h, Complex.normSq_zero]

/-! ## The two half-angle flip masks and their dressings -/

def efA : SS.BitString 6 := bs false false false false true  false  -- 000010
def efB : SS.BitString 6 := bs false false false false false true   -- 000001

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
def w10 : SS.BitString 6 := bs false true  false false false false  -- 010000
def w11 : SS.BitString 6 := bs false true  false false false true   -- 010001
def w12 : SS.BitString 6 := bs false true  false false true  false  -- 010010
def w13 : SS.BitString 6 := bs true  false false false false false  -- 100000
def w14 : SS.BitString 6 := bs true  false false false false true   -- 100001
def w15 : SS.BitString 6 := bs true  false false false true  false  -- 100010

theorem incidenceA :
    S1.filter (fun y => SS.bxor y efA ∈ S0) = {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15} := by decide
theorem flipA_0 : SS.bxor z0 efA = y1 := by decide
theorem flipA_1 : SS.bxor z1 efA = y0 := by decide
theorem flipA_2 : SS.bxor z2 efA = y3 := by decide
theorem flipA_3 : SS.bxor z3 efA = y2 := by decide
theorem flipA_4 : SS.bxor z4 efA = y5 := by decide
theorem flipA_5 : SS.bxor z5 efA = y4 := by decide
theorem flipA_6 : SS.bxor z6 efA = y7 := by decide
theorem flipA_7 : SS.bxor z7 efA = y6 := by decide
theorem flipA_8 : SS.bxor z8 efA = y9 := by decide
theorem flipA_9 : SS.bxor z9 efA = y8 := by decide
theorem flipA_10 : SS.bxor z10 efA = y11 := by decide
theorem flipA_11 : SS.bxor z11 efA = y10 := by decide
theorem flipA_12 : SS.bxor z12 efA = y13 := by decide
theorem flipA_13 : SS.bxor z13 efA = y12 := by decide
theorem flipA_14 : SS.bxor z14 efA = y15 := by decide
theorem flipA_15 : SS.bxor z15 efA = y14 := by decide

theorem incidenceB :
    S1.filter (fun y => SS.bxor y efB ∈ S0) = {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15} := by decide
theorem flipB_0 : SS.bxor z0 efB = y0 := by decide
theorem flipB_1 : SS.bxor z1 efB = y1 := by decide
theorem flipB_2 : SS.bxor z2 efB = y2 := by decide
theorem flipB_3 : SS.bxor z3 efB = y3 := by decide
theorem flipB_4 : SS.bxor z4 efB = y4 := by decide
theorem flipB_5 : SS.bxor z5 efB = y5 := by decide
theorem flipB_6 : SS.bxor z6 efB = y6 := by decide
theorem flipB_7 : SS.bxor z7 efB = y7 := by decide
theorem flipB_8 : SS.bxor z8 efB = y8 := by decide
theorem flipB_9 : SS.bxor z9 efB = y9 := by decide
theorem flipB_10 : SS.bxor z10 efB = y10 := by decide
theorem flipB_11 : SS.bxor z11 efB = y11 := by decide
theorem flipB_12 : SS.bxor z12 efB = y12 := by decide
theorem flipB_13 : SS.bxor z13 efB = y13 := by decide
theorem flipB_14 : SS.bxor z14 efB = y14 := by decide
theorem flipB_15 : SS.bxor z15 efB = y15 := by decide

theorem sg_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg_w0_12 : SS.bdot w0 z12 = false := by decide
theorem sg_w0_13 : SS.bdot w0 z13 = false := by decide
theorem sg_w0_14 : SS.bdot w0 z14 = false := by decide
theorem sg_w0_15 : SS.bdot w0 z15 = false := by decide
theorem sg_w1_0 : SS.bdot w1 z0 = true := by decide
theorem sg_w1_1 : SS.bdot w1 z1 = false := by decide
theorem sg_w1_2 : SS.bdot w1 z2 = false := by decide
theorem sg_w1_3 : SS.bdot w1 z3 = true := by decide
theorem sg_w1_4 : SS.bdot w1 z4 = false := by decide
theorem sg_w1_5 : SS.bdot w1 z5 = true := by decide
theorem sg_w1_6 : SS.bdot w1 z6 = false := by decide
theorem sg_w1_7 : SS.bdot w1 z7 = true := by decide
theorem sg_w1_8 : SS.bdot w1 z8 = false := by decide
theorem sg_w1_9 : SS.bdot w1 z9 = true := by decide
theorem sg_w1_10 : SS.bdot w1 z10 = false := by decide
theorem sg_w1_11 : SS.bdot w1 z11 = true := by decide
theorem sg_w1_12 : SS.bdot w1 z12 = false := by decide
theorem sg_w1_13 : SS.bdot w1 z13 = true := by decide
theorem sg_w1_14 : SS.bdot w1 z14 = true := by decide
theorem sg_w1_15 : SS.bdot w1 z15 = false := by decide
theorem sg_w2_0 : SS.bdot w2 z0 = false := by decide
theorem sg_w2_1 : SS.bdot w2 z1 = true := by decide
theorem sg_w2_2 : SS.bdot w2 z2 = false := by decide
theorem sg_w2_3 : SS.bdot w2 z3 = true := by decide
theorem sg_w2_4 : SS.bdot w2 z4 = false := by decide
theorem sg_w2_5 : SS.bdot w2 z5 = true := by decide
theorem sg_w2_6 : SS.bdot w2 z6 = false := by decide
theorem sg_w2_7 : SS.bdot w2 z7 = true := by decide
theorem sg_w2_8 : SS.bdot w2 z8 = false := by decide
theorem sg_w2_9 : SS.bdot w2 z9 = true := by decide
theorem sg_w2_10 : SS.bdot w2 z10 = false := by decide
theorem sg_w2_11 : SS.bdot w2 z11 = true := by decide
theorem sg_w2_12 : SS.bdot w2 z12 = false := by decide
theorem sg_w2_13 : SS.bdot w2 z13 = true := by decide
theorem sg_w2_14 : SS.bdot w2 z14 = false := by decide
theorem sg_w2_15 : SS.bdot w2 z15 = true := by decide
theorem sg_w3_0 : SS.bdot w3 z0 = true := by decide
theorem sg_w3_1 : SS.bdot w3 z1 = true := by decide
theorem sg_w3_2 : SS.bdot w3 z2 = false := by decide
theorem sg_w3_3 : SS.bdot w3 z3 = false := by decide
theorem sg_w3_4 : SS.bdot w3 z4 = false := by decide
theorem sg_w3_5 : SS.bdot w3 z5 = false := by decide
theorem sg_w3_6 : SS.bdot w3 z6 = false := by decide
theorem sg_w3_7 : SS.bdot w3 z7 = false := by decide
theorem sg_w3_8 : SS.bdot w3 z8 = false := by decide
theorem sg_w3_9 : SS.bdot w3 z9 = false := by decide
theorem sg_w3_10 : SS.bdot w3 z10 = false := by decide
theorem sg_w3_11 : SS.bdot w3 z11 = false := by decide
theorem sg_w3_12 : SS.bdot w3 z12 = false := by decide
theorem sg_w3_13 : SS.bdot w3 z13 = false := by decide
theorem sg_w3_14 : SS.bdot w3 z14 = true := by decide
theorem sg_w3_15 : SS.bdot w3 z15 = true := by decide
theorem sg_w4_0 : SS.bdot w4 z0 = false := by decide
theorem sg_w4_1 : SS.bdot w4 z1 = false := by decide
theorem sg_w4_2 : SS.bdot w4 z2 = true := by decide
theorem sg_w4_3 : SS.bdot w4 z3 = true := by decide
theorem sg_w4_4 : SS.bdot w4 z4 = true := by decide
theorem sg_w4_5 : SS.bdot w4 z5 = true := by decide
theorem sg_w4_6 : SS.bdot w4 z6 = false := by decide
theorem sg_w4_7 : SS.bdot w4 z7 = false := by decide
theorem sg_w4_8 : SS.bdot w4 z8 = true := by decide
theorem sg_w4_9 : SS.bdot w4 z9 = true := by decide
theorem sg_w4_10 : SS.bdot w4 z10 = false := by decide
theorem sg_w4_11 : SS.bdot w4 z11 = false := by decide
theorem sg_w4_12 : SS.bdot w4 z12 = false := by decide
theorem sg_w4_13 : SS.bdot w4 z13 = false := by decide
theorem sg_w4_14 : SS.bdot w4 z14 = true := by decide
theorem sg_w4_15 : SS.bdot w4 z15 = true := by decide
theorem sg_w5_0 : SS.bdot w5 z0 = true := by decide
theorem sg_w5_1 : SS.bdot w5 z1 = false := by decide
theorem sg_w5_2 : SS.bdot w5 z2 = true := by decide
theorem sg_w5_3 : SS.bdot w5 z3 = false := by decide
theorem sg_w5_4 : SS.bdot w5 z4 = true := by decide
theorem sg_w5_5 : SS.bdot w5 z5 = false := by decide
theorem sg_w5_6 : SS.bdot w5 z6 = false := by decide
theorem sg_w5_7 : SS.bdot w5 z7 = true := by decide
theorem sg_w5_8 : SS.bdot w5 z8 = true := by decide
theorem sg_w5_9 : SS.bdot w5 z9 = false := by decide
theorem sg_w5_10 : SS.bdot w5 z10 = false := by decide
theorem sg_w5_11 : SS.bdot w5 z11 = true := by decide
theorem sg_w5_12 : SS.bdot w5 z12 = false := by decide
theorem sg_w5_13 : SS.bdot w5 z13 = true := by decide
theorem sg_w5_14 : SS.bdot w5 z14 = false := by decide
theorem sg_w5_15 : SS.bdot w5 z15 = true := by decide
theorem sg_w6_0 : SS.bdot w6 z0 = false := by decide
theorem sg_w6_1 : SS.bdot w6 z1 = true := by decide
theorem sg_w6_2 : SS.bdot w6 z2 = true := by decide
theorem sg_w6_3 : SS.bdot w6 z3 = false := by decide
theorem sg_w6_4 : SS.bdot w6 z4 = true := by decide
theorem sg_w6_5 : SS.bdot w6 z5 = false := by decide
theorem sg_w6_6 : SS.bdot w6 z6 = false := by decide
theorem sg_w6_7 : SS.bdot w6 z7 = true := by decide
theorem sg_w6_8 : SS.bdot w6 z8 = true := by decide
theorem sg_w6_9 : SS.bdot w6 z9 = false := by decide
theorem sg_w6_10 : SS.bdot w6 z10 = false := by decide
theorem sg_w6_11 : SS.bdot w6 z11 = true := by decide
theorem sg_w6_12 : SS.bdot w6 z12 = false := by decide
theorem sg_w6_13 : SS.bdot w6 z13 = true := by decide
theorem sg_w6_14 : SS.bdot w6 z14 = true := by decide
theorem sg_w6_15 : SS.bdot w6 z15 = false := by decide
theorem sg_w7_0 : SS.bdot w7 z0 = false := by decide
theorem sg_w7_1 : SS.bdot w7 z1 = false := by decide
theorem sg_w7_2 : SS.bdot w7 z2 = true := by decide
theorem sg_w7_3 : SS.bdot w7 z3 = true := by decide
theorem sg_w7_4 : SS.bdot w7 z4 = false := by decide
theorem sg_w7_5 : SS.bdot w7 z5 = false := by decide
theorem sg_w7_6 : SS.bdot w7 z6 = true := by decide
theorem sg_w7_7 : SS.bdot w7 z7 = true := by decide
theorem sg_w7_8 : SS.bdot w7 z8 = false := by decide
theorem sg_w7_9 : SS.bdot w7 z9 = false := by decide
theorem sg_w7_10 : SS.bdot w7 z10 = true := by decide
theorem sg_w7_11 : SS.bdot w7 z11 = true := by decide
theorem sg_w7_12 : SS.bdot w7 z12 = false := by decide
theorem sg_w7_13 : SS.bdot w7 z13 = false := by decide
theorem sg_w7_14 : SS.bdot w7 z14 = true := by decide
theorem sg_w7_15 : SS.bdot w7 z15 = true := by decide
theorem sg_w8_0 : SS.bdot w8 z0 = true := by decide
theorem sg_w8_1 : SS.bdot w8 z1 = false := by decide
theorem sg_w8_2 : SS.bdot w8 z2 = true := by decide
theorem sg_w8_3 : SS.bdot w8 z3 = false := by decide
theorem sg_w8_4 : SS.bdot w8 z4 = false := by decide
theorem sg_w8_5 : SS.bdot w8 z5 = true := by decide
theorem sg_w8_6 : SS.bdot w8 z6 = true := by decide
theorem sg_w8_7 : SS.bdot w8 z7 = false := by decide
theorem sg_w8_8 : SS.bdot w8 z8 = false := by decide
theorem sg_w8_9 : SS.bdot w8 z9 = true := by decide
theorem sg_w8_10 : SS.bdot w8 z10 = true := by decide
theorem sg_w8_11 : SS.bdot w8 z11 = false := by decide
theorem sg_w8_12 : SS.bdot w8 z12 = false := by decide
theorem sg_w8_13 : SS.bdot w8 z13 = true := by decide
theorem sg_w8_14 : SS.bdot w8 z14 = false := by decide
theorem sg_w8_15 : SS.bdot w8 z15 = true := by decide
theorem sg_w9_0 : SS.bdot w9 z0 = false := by decide
theorem sg_w9_1 : SS.bdot w9 z1 = true := by decide
theorem sg_w9_2 : SS.bdot w9 z2 = true := by decide
theorem sg_w9_3 : SS.bdot w9 z3 = false := by decide
theorem sg_w9_4 : SS.bdot w9 z4 = false := by decide
theorem sg_w9_5 : SS.bdot w9 z5 = true := by decide
theorem sg_w9_6 : SS.bdot w9 z6 = true := by decide
theorem sg_w9_7 : SS.bdot w9 z7 = false := by decide
theorem sg_w9_8 : SS.bdot w9 z8 = false := by decide
theorem sg_w9_9 : SS.bdot w9 z9 = true := by decide
theorem sg_w9_10 : SS.bdot w9 z10 = true := by decide
theorem sg_w9_11 : SS.bdot w9 z11 = false := by decide
theorem sg_w9_12 : SS.bdot w9 z12 = false := by decide
theorem sg_w9_13 : SS.bdot w9 z13 = true := by decide
theorem sg_w9_14 : SS.bdot w9 z14 = true := by decide
theorem sg_w9_15 : SS.bdot w9 z15 = false := by decide
theorem sg_w10_0 : SS.bdot w10 z0 = false := by decide
theorem sg_w10_1 : SS.bdot w10 z1 = false := by decide
theorem sg_w10_2 : SS.bdot w10 z2 = false := by decide
theorem sg_w10_3 : SS.bdot w10 z3 = false := by decide
theorem sg_w10_4 : SS.bdot w10 z4 = true := by decide
theorem sg_w10_5 : SS.bdot w10 z5 = true := by decide
theorem sg_w10_6 : SS.bdot w10 z6 = true := by decide
theorem sg_w10_7 : SS.bdot w10 z7 = true := by decide
theorem sg_w10_8 : SS.bdot w10 z8 = false := by decide
theorem sg_w10_9 : SS.bdot w10 z9 = false := by decide
theorem sg_w10_10 : SS.bdot w10 z10 = false := by decide
theorem sg_w10_11 : SS.bdot w10 z11 = false := by decide
theorem sg_w10_12 : SS.bdot w10 z12 = true := by decide
theorem sg_w10_13 : SS.bdot w10 z13 = true := by decide
theorem sg_w10_14 : SS.bdot w10 z14 = true := by decide
theorem sg_w10_15 : SS.bdot w10 z15 = true := by decide
theorem sg_w11_0 : SS.bdot w11 z0 = true := by decide
theorem sg_w11_1 : SS.bdot w11 z1 = false := by decide
theorem sg_w11_2 : SS.bdot w11 z2 = false := by decide
theorem sg_w11_3 : SS.bdot w11 z3 = true := by decide
theorem sg_w11_4 : SS.bdot w11 z4 = true := by decide
theorem sg_w11_5 : SS.bdot w11 z5 = false := by decide
theorem sg_w11_6 : SS.bdot w11 z6 = true := by decide
theorem sg_w11_7 : SS.bdot w11 z7 = false := by decide
theorem sg_w11_8 : SS.bdot w11 z8 = false := by decide
theorem sg_w11_9 : SS.bdot w11 z9 = true := by decide
theorem sg_w11_10 : SS.bdot w11 z10 = false := by decide
theorem sg_w11_11 : SS.bdot w11 z11 = true := by decide
theorem sg_w11_12 : SS.bdot w11 z12 = true := by decide
theorem sg_w11_13 : SS.bdot w11 z13 = false := by decide
theorem sg_w11_14 : SS.bdot w11 z14 = false := by decide
theorem sg_w11_15 : SS.bdot w11 z15 = true := by decide
theorem sg_w12_0 : SS.bdot w12 z0 = false := by decide
theorem sg_w12_1 : SS.bdot w12 z1 = true := by decide
theorem sg_w12_2 : SS.bdot w12 z2 = false := by decide
theorem sg_w12_3 : SS.bdot w12 z3 = true := by decide
theorem sg_w12_4 : SS.bdot w12 z4 = true := by decide
theorem sg_w12_5 : SS.bdot w12 z5 = false := by decide
theorem sg_w12_6 : SS.bdot w12 z6 = true := by decide
theorem sg_w12_7 : SS.bdot w12 z7 = false := by decide
theorem sg_w12_8 : SS.bdot w12 z8 = false := by decide
theorem sg_w12_9 : SS.bdot w12 z9 = true := by decide
theorem sg_w12_10 : SS.bdot w12 z10 = false := by decide
theorem sg_w12_11 : SS.bdot w12 z11 = true := by decide
theorem sg_w12_12 : SS.bdot w12 z12 = true := by decide
theorem sg_w12_13 : SS.bdot w12 z13 = false := by decide
theorem sg_w12_14 : SS.bdot w12 z14 = true := by decide
theorem sg_w12_15 : SS.bdot w12 z15 = false := by decide
theorem sg_w13_0 : SS.bdot w13 z0 = false := by decide
theorem sg_w13_1 : SS.bdot w13 z1 = false := by decide
theorem sg_w13_2 : SS.bdot w13 z2 = false := by decide
theorem sg_w13_3 : SS.bdot w13 z3 = false := by decide
theorem sg_w13_4 : SS.bdot w13 z4 = false := by decide
theorem sg_w13_5 : SS.bdot w13 z5 = false := by decide
theorem sg_w13_6 : SS.bdot w13 z6 = false := by decide
theorem sg_w13_7 : SS.bdot w13 z7 = false := by decide
theorem sg_w13_8 : SS.bdot w13 z8 = true := by decide
theorem sg_w13_9 : SS.bdot w13 z9 = true := by decide
theorem sg_w13_10 : SS.bdot w13 z10 = true := by decide
theorem sg_w13_11 : SS.bdot w13 z11 = true := by decide
theorem sg_w13_12 : SS.bdot w13 z12 = true := by decide
theorem sg_w13_13 : SS.bdot w13 z13 = true := by decide
theorem sg_w13_14 : SS.bdot w13 z14 = true := by decide
theorem sg_w13_15 : SS.bdot w13 z15 = true := by decide
theorem sg_w14_0 : SS.bdot w14 z0 = true := by decide
theorem sg_w14_1 : SS.bdot w14 z1 = false := by decide
theorem sg_w14_2 : SS.bdot w14 z2 = false := by decide
theorem sg_w14_3 : SS.bdot w14 z3 = true := by decide
theorem sg_w14_4 : SS.bdot w14 z4 = false := by decide
theorem sg_w14_5 : SS.bdot w14 z5 = true := by decide
theorem sg_w14_6 : SS.bdot w14 z6 = false := by decide
theorem sg_w14_7 : SS.bdot w14 z7 = true := by decide
theorem sg_w14_8 : SS.bdot w14 z8 = true := by decide
theorem sg_w14_9 : SS.bdot w14 z9 = false := by decide
theorem sg_w14_10 : SS.bdot w14 z10 = true := by decide
theorem sg_w14_11 : SS.bdot w14 z11 = false := by decide
theorem sg_w14_12 : SS.bdot w14 z12 = true := by decide
theorem sg_w14_13 : SS.bdot w14 z13 = false := by decide
theorem sg_w14_14 : SS.bdot w14 z14 = false := by decide
theorem sg_w14_15 : SS.bdot w14 z15 = true := by decide
theorem sg_w15_0 : SS.bdot w15 z0 = false := by decide
theorem sg_w15_1 : SS.bdot w15 z1 = true := by decide
theorem sg_w15_2 : SS.bdot w15 z2 = false := by decide
theorem sg_w15_3 : SS.bdot w15 z3 = true := by decide
theorem sg_w15_4 : SS.bdot w15 z4 = false := by decide
theorem sg_w15_5 : SS.bdot w15 z5 = true := by decide
theorem sg_w15_6 : SS.bdot w15 z6 = false := by decide
theorem sg_w15_7 : SS.bdot w15 z7 = true := by decide
theorem sg_w15_8 : SS.bdot w15 z8 = true := by decide
theorem sg_w15_9 : SS.bdot w15 z9 = false := by decide
theorem sg_w15_10 : SS.bdot w15 z10 = true := by decide
theorem sg_w15_11 : SS.bdot w15 z11 = false := by decide
theorem sg_w15_12 : SS.bdot w15 z12 = true := by decide
theorem sg_w15_13 : SS.bdot w15 z13 = false := by decide
theorem sg_w15_14 : SS.bdot w15 z14 = true := by decide
theorem sg_w15_15 : SS.bdot w15 z15 = false := by decide

/-! ## The Walsh expansions -/

def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),
      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

theorem exA_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d efA w0 =
      star (c y1) * d z0 + star (c y0) * d z1 + star (c y3) * d z2 + star (c y2) * d z3 + star (c y5) * d z4 + star (c y4) * d z5 + star (c y7) * d z6 + star (c y6) * d z7 + star (c y9) * d z8 + star (c y8) * d z9 + star (c y11) * d z10 + star (c y10) * d z11 + star (c y13) * d z12 + star (c y12) * d z13 + star (c y15) * d z14 + star (c y14) * d z15 := by
  unfold offSum
  rw [incidenceA]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flipA_0, flipA_1, flipA_2, flipA_3, flipA_4, flipA_5, flipA_6, flipA_7, flipA_8, flipA_9, flipA_10, flipA_11, flipA_12, flipA_13, flipA_14, flipA_15]
  simp only [sg_w0_0, sg_w0_1, sg_w0_2, sg_w0_3, sg_w0_4, sg_w0_5, sg_w0_6, sg_w0_7, sg_w0_8, sg_w0_9, sg_w0_10, sg_w0_11, sg_w0_12, sg_w0_13, sg_w0_14, sg_w0_15, SixQubit.signMul_false]
  try ring

theorem exA_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d efA w1 =
      - star (c y1) * d z0 + star (c y0) * d z1 + star (c y3) * d z2 - star (c y2) * d z3 + star (c y5) * d z4 - star (c y4) * d z5 + star (c y7) * d z6 - star (c y6) * d z7 + star (c y9) * d z8 - star (c y8) * d z9 + star (c y11) * d z10 - star (c y10) * d z11 + star (c y13) * d z12 - star (c y12) * d z13 - star (c y15) * d z14 + star (c y14) * d z15 := by
  unfold offSum
  rw [incidenceA]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flipA_0, flipA_1, flipA_2, flipA_3, flipA_4, flipA_5, flipA_6, flipA_7, flipA_8, flipA_9, flipA_10, flipA_11, flipA_12, flipA_13, flipA_14, flipA_15]
  simp only [sg_w1_0, sg_w1_1, sg_w1_2, sg_w1_3, sg_w1_4, sg_w1_5, sg_w1_6, sg_w1_7, sg_w1_8, sg_w1_9, sg_w1_10, sg_w1_11, sg_w1_12, sg_w1_13, sg_w1_14, sg_w1_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exA_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d efA w2 =
      star (c y1) * d z0 - star (c y0) * d z1 + star (c y3) * d z2 - star (c y2) * d z3 + star (c y5) * d z4 - star (c y4) * d z5 + star (c y7) * d z6 - star (c y6) * d z7 + star (c y9) * d z8 - star (c y8) * d z9 + star (c y11) * d z10 - star (c y10) * d z11 + star (c y13) * d z12 - star (c y12) * d z13 + star (c y15) * d z14 - star (c y14) * d z15 := by
  unfold offSum
  rw [incidenceA]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flipA_0, flipA_1, flipA_2, flipA_3, flipA_4, flipA_5, flipA_6, flipA_7, flipA_8, flipA_9, flipA_10, flipA_11, flipA_12, flipA_13, flipA_14, flipA_15]
  simp only [sg_w2_0, sg_w2_1, sg_w2_2, sg_w2_3, sg_w2_4, sg_w2_5, sg_w2_6, sg_w2_7, sg_w2_8, sg_w2_9, sg_w2_10, sg_w2_11, sg_w2_12, sg_w2_13, sg_w2_14, sg_w2_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exA_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d efA w3 =
      - star (c y1) * d z0 - star (c y0) * d z1 + star (c y3) * d z2 + star (c y2) * d z3 + star (c y5) * d z4 + star (c y4) * d z5 + star (c y7) * d z6 + star (c y6) * d z7 + star (c y9) * d z8 + star (c y8) * d z9 + star (c y11) * d z10 + star (c y10) * d z11 + star (c y13) * d z12 + star (c y12) * d z13 - star (c y15) * d z14 - star (c y14) * d z15 := by
  unfold offSum
  rw [incidenceA]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flipA_0, flipA_1, flipA_2, flipA_3, flipA_4, flipA_5, flipA_6, flipA_7, flipA_8, flipA_9, flipA_10, flipA_11, flipA_12, flipA_13, flipA_14, flipA_15]
  simp only [sg_w3_0, sg_w3_1, sg_w3_2, sg_w3_3, sg_w3_4, sg_w3_5, sg_w3_6, sg_w3_7, sg_w3_8, sg_w3_9, sg_w3_10, sg_w3_11, sg_w3_12, sg_w3_13, sg_w3_14, sg_w3_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exA_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d efA w4 =
      star (c y1) * d z0 + star (c y0) * d z1 - star (c y3) * d z2 - star (c y2) * d z3 - star (c y5) * d z4 - star (c y4) * d z5 + star (c y7) * d z6 + star (c y6) * d z7 - star (c y9) * d z8 - star (c y8) * d z9 + star (c y11) * d z10 + star (c y10) * d z11 + star (c y13) * d z12 + star (c y12) * d z13 - star (c y15) * d z14 - star (c y14) * d z15 := by
  unfold offSum
  rw [incidenceA]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flipA_0, flipA_1, flipA_2, flipA_3, flipA_4, flipA_5, flipA_6, flipA_7, flipA_8, flipA_9, flipA_10, flipA_11, flipA_12, flipA_13, flipA_14, flipA_15]
  simp only [sg_w4_0, sg_w4_1, sg_w4_2, sg_w4_3, sg_w4_4, sg_w4_5, sg_w4_6, sg_w4_7, sg_w4_8, sg_w4_9, sg_w4_10, sg_w4_11, sg_w4_12, sg_w4_13, sg_w4_14, sg_w4_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exA_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d efA w6 =
      star (c y1) * d z0 - star (c y0) * d z1 - star (c y3) * d z2 + star (c y2) * d z3 - star (c y5) * d z4 + star (c y4) * d z5 + star (c y7) * d z6 - star (c y6) * d z7 - star (c y9) * d z8 + star (c y8) * d z9 + star (c y11) * d z10 - star (c y10) * d z11 + star (c y13) * d z12 - star (c y12) * d z13 - star (c y15) * d z14 + star (c y14) * d z15 := by
  unfold offSum
  rw [incidenceA]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flipA_0, flipA_1, flipA_2, flipA_3, flipA_4, flipA_5, flipA_6, flipA_7, flipA_8, flipA_9, flipA_10, flipA_11, flipA_12, flipA_13, flipA_14, flipA_15]
  simp only [sg_w6_0, sg_w6_1, sg_w6_2, sg_w6_3, sg_w6_4, sg_w6_5, sg_w6_6, sg_w6_7, sg_w6_8, sg_w6_9, sg_w6_10, sg_w6_11, sg_w6_12, sg_w6_13, sg_w6_14, sg_w6_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exA_w7 (c d : SS.BitString 6 -> ℂ) :
    offSum c d efA w7 =
      star (c y1) * d z0 + star (c y0) * d z1 - star (c y3) * d z2 - star (c y2) * d z3 + star (c y5) * d z4 + star (c y4) * d z5 - star (c y7) * d z6 - star (c y6) * d z7 + star (c y9) * d z8 + star (c y8) * d z9 - star (c y11) * d z10 - star (c y10) * d z11 + star (c y13) * d z12 + star (c y12) * d z13 - star (c y15) * d z14 - star (c y14) * d z15 := by
  unfold offSum
  rw [incidenceA]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flipA_0, flipA_1, flipA_2, flipA_3, flipA_4, flipA_5, flipA_6, flipA_7, flipA_8, flipA_9, flipA_10, flipA_11, flipA_12, flipA_13, flipA_14, flipA_15]
  simp only [sg_w7_0, sg_w7_1, sg_w7_2, sg_w7_3, sg_w7_4, sg_w7_5, sg_w7_6, sg_w7_7, sg_w7_8, sg_w7_9, sg_w7_10, sg_w7_11, sg_w7_12, sg_w7_13, sg_w7_14, sg_w7_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exA_w9 (c d : SS.BitString 6 -> ℂ) :
    offSum c d efA w9 =
      star (c y1) * d z0 - star (c y0) * d z1 - star (c y3) * d z2 + star (c y2) * d z3 + star (c y5) * d z4 - star (c y4) * d z5 - star (c y7) * d z6 + star (c y6) * d z7 + star (c y9) * d z8 - star (c y8) * d z9 - star (c y11) * d z10 + star (c y10) * d z11 + star (c y13) * d z12 - star (c y12) * d z13 - star (c y15) * d z14 + star (c y14) * d z15 := by
  unfold offSum
  rw [incidenceA]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flipA_0, flipA_1, flipA_2, flipA_3, flipA_4, flipA_5, flipA_6, flipA_7, flipA_8, flipA_9, flipA_10, flipA_11, flipA_12, flipA_13, flipA_14, flipA_15]
  simp only [sg_w9_0, sg_w9_1, sg_w9_2, sg_w9_3, sg_w9_4, sg_w9_5, sg_w9_6, sg_w9_7, sg_w9_8, sg_w9_9, sg_w9_10, sg_w9_11, sg_w9_12, sg_w9_13, sg_w9_14, sg_w9_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exA_w10 (c d : SS.BitString 6 -> ℂ) :
    offSum c d efA w10 =
      star (c y1) * d z0 + star (c y0) * d z1 + star (c y3) * d z2 + star (c y2) * d z3 - star (c y5) * d z4 - star (c y4) * d z5 - star (c y7) * d z6 - star (c y6) * d z7 + star (c y9) * d z8 + star (c y8) * d z9 + star (c y11) * d z10 + star (c y10) * d z11 - star (c y13) * d z12 - star (c y12) * d z13 - star (c y15) * d z14 - star (c y14) * d z15 := by
  unfold offSum
  rw [incidenceA]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flipA_0, flipA_1, flipA_2, flipA_3, flipA_4, flipA_5, flipA_6, flipA_7, flipA_8, flipA_9, flipA_10, flipA_11, flipA_12, flipA_13, flipA_14, flipA_15]
  simp only [sg_w10_0, sg_w10_1, sg_w10_2, sg_w10_3, sg_w10_4, sg_w10_5, sg_w10_6, sg_w10_7, sg_w10_8, sg_w10_9, sg_w10_10, sg_w10_11, sg_w10_12, sg_w10_13, sg_w10_14, sg_w10_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exA_w12 (c d : SS.BitString 6 -> ℂ) :
    offSum c d efA w12 =
      star (c y1) * d z0 - star (c y0) * d z1 + star (c y3) * d z2 - star (c y2) * d z3 - star (c y5) * d z4 + star (c y4) * d z5 - star (c y7) * d z6 + star (c y6) * d z7 + star (c y9) * d z8 - star (c y8) * d z9 + star (c y11) * d z10 - star (c y10) * d z11 - star (c y13) * d z12 + star (c y12) * d z13 - star (c y15) * d z14 + star (c y14) * d z15 := by
  unfold offSum
  rw [incidenceA]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flipA_0, flipA_1, flipA_2, flipA_3, flipA_4, flipA_5, flipA_6, flipA_7, flipA_8, flipA_9, flipA_10, flipA_11, flipA_12, flipA_13, flipA_14, flipA_15]
  simp only [sg_w12_0, sg_w12_1, sg_w12_2, sg_w12_3, sg_w12_4, sg_w12_5, sg_w12_6, sg_w12_7, sg_w12_8, sg_w12_9, sg_w12_10, sg_w12_11, sg_w12_12, sg_w12_13, sg_w12_14, sg_w12_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exA_w13 (c d : SS.BitString 6 -> ℂ) :
    offSum c d efA w13 =
      star (c y1) * d z0 + star (c y0) * d z1 + star (c y3) * d z2 + star (c y2) * d z3 + star (c y5) * d z4 + star (c y4) * d z5 + star (c y7) * d z6 + star (c y6) * d z7 - star (c y9) * d z8 - star (c y8) * d z9 - star (c y11) * d z10 - star (c y10) * d z11 - star (c y13) * d z12 - star (c y12) * d z13 - star (c y15) * d z14 - star (c y14) * d z15 := by
  unfold offSum
  rw [incidenceA]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flipA_0, flipA_1, flipA_2, flipA_3, flipA_4, flipA_5, flipA_6, flipA_7, flipA_8, flipA_9, flipA_10, flipA_11, flipA_12, flipA_13, flipA_14, flipA_15]
  simp only [sg_w13_0, sg_w13_1, sg_w13_2, sg_w13_3, sg_w13_4, sg_w13_5, sg_w13_6, sg_w13_7, sg_w13_8, sg_w13_9, sg_w13_10, sg_w13_11, sg_w13_12, sg_w13_13, sg_w13_14, sg_w13_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exA_w15 (c d : SS.BitString 6 -> ℂ) :
    offSum c d efA w15 =
      star (c y1) * d z0 - star (c y0) * d z1 + star (c y3) * d z2 - star (c y2) * d z3 + star (c y5) * d z4 - star (c y4) * d z5 + star (c y7) * d z6 - star (c y6) * d z7 - star (c y9) * d z8 + star (c y8) * d z9 - star (c y11) * d z10 + star (c y10) * d z11 - star (c y13) * d z12 + star (c y12) * d z13 - star (c y15) * d z14 + star (c y14) * d z15 := by
  unfold offSum
  rw [incidenceA]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flipA_0, flipA_1, flipA_2, flipA_3, flipA_4, flipA_5, flipA_6, flipA_7, flipA_8, flipA_9, flipA_10, flipA_11, flipA_12, flipA_13, flipA_14, flipA_15]
  simp only [sg_w15_0, sg_w15_1, sg_w15_2, sg_w15_3, sg_w15_4, sg_w15_5, sg_w15_6, sg_w15_7, sg_w15_8, sg_w15_9, sg_w15_10, sg_w15_11, sg_w15_12, sg_w15_13, sg_w15_14, sg_w15_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exB_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d efB w0 =
      star (c y0) * d z0 + star (c y1) * d z1 + star (c y2) * d z2 + star (c y3) * d z3 + star (c y4) * d z4 + star (c y5) * d z5 + star (c y6) * d z6 + star (c y7) * d z7 + star (c y8) * d z8 + star (c y9) * d z9 + star (c y10) * d z10 + star (c y11) * d z11 + star (c y12) * d z12 + star (c y13) * d z13 + star (c y14) * d z14 + star (c y15) * d z15 := by
  unfold offSum
  rw [incidenceB]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flipB_0, flipB_1, flipB_2, flipB_3, flipB_4, flipB_5, flipB_6, flipB_7, flipB_8, flipB_9, flipB_10, flipB_11, flipB_12, flipB_13, flipB_14, flipB_15]
  simp only [sg_w0_0, sg_w0_1, sg_w0_2, sg_w0_3, sg_w0_4, sg_w0_5, sg_w0_6, sg_w0_7, sg_w0_8, sg_w0_9, sg_w0_10, sg_w0_11, sg_w0_12, sg_w0_13, sg_w0_14, sg_w0_15, SixQubit.signMul_false]
  try ring

theorem exB_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d efB w1 =
      - star (c y0) * d z0 + star (c y1) * d z1 + star (c y2) * d z2 - star (c y3) * d z3 + star (c y4) * d z4 - star (c y5) * d z5 + star (c y6) * d z6 - star (c y7) * d z7 + star (c y8) * d z8 - star (c y9) * d z9 + star (c y10) * d z10 - star (c y11) * d z11 + star (c y12) * d z12 - star (c y13) * d z13 - star (c y14) * d z14 + star (c y15) * d z15 := by
  unfold offSum
  rw [incidenceB]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flipB_0, flipB_1, flipB_2, flipB_3, flipB_4, flipB_5, flipB_6, flipB_7, flipB_8, flipB_9, flipB_10, flipB_11, flipB_12, flipB_13, flipB_14, flipB_15]
  simp only [sg_w1_0, sg_w1_1, sg_w1_2, sg_w1_3, sg_w1_4, sg_w1_5, sg_w1_6, sg_w1_7, sg_w1_8, sg_w1_9, sg_w1_10, sg_w1_11, sg_w1_12, sg_w1_13, sg_w1_14, sg_w1_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exB_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d efB w2 =
      star (c y0) * d z0 - star (c y1) * d z1 + star (c y2) * d z2 - star (c y3) * d z3 + star (c y4) * d z4 - star (c y5) * d z5 + star (c y6) * d z6 - star (c y7) * d z7 + star (c y8) * d z8 - star (c y9) * d z9 + star (c y10) * d z10 - star (c y11) * d z11 + star (c y12) * d z12 - star (c y13) * d z13 + star (c y14) * d z14 - star (c y15) * d z15 := by
  unfold offSum
  rw [incidenceB]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flipB_0, flipB_1, flipB_2, flipB_3, flipB_4, flipB_5, flipB_6, flipB_7, flipB_8, flipB_9, flipB_10, flipB_11, flipB_12, flipB_13, flipB_14, flipB_15]
  simp only [sg_w2_0, sg_w2_1, sg_w2_2, sg_w2_3, sg_w2_4, sg_w2_5, sg_w2_6, sg_w2_7, sg_w2_8, sg_w2_9, sg_w2_10, sg_w2_11, sg_w2_12, sg_w2_13, sg_w2_14, sg_w2_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exB_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d efB w3 =
      - star (c y0) * d z0 - star (c y1) * d z1 + star (c y2) * d z2 + star (c y3) * d z3 + star (c y4) * d z4 + star (c y5) * d z5 + star (c y6) * d z6 + star (c y7) * d z7 + star (c y8) * d z8 + star (c y9) * d z9 + star (c y10) * d z10 + star (c y11) * d z11 + star (c y12) * d z12 + star (c y13) * d z13 - star (c y14) * d z14 - star (c y15) * d z15 := by
  unfold offSum
  rw [incidenceB]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flipB_0, flipB_1, flipB_2, flipB_3, flipB_4, flipB_5, flipB_6, flipB_7, flipB_8, flipB_9, flipB_10, flipB_11, flipB_12, flipB_13, flipB_14, flipB_15]
  simp only [sg_w3_0, sg_w3_1, sg_w3_2, sg_w3_3, sg_w3_4, sg_w3_5, sg_w3_6, sg_w3_7, sg_w3_8, sg_w3_9, sg_w3_10, sg_w3_11, sg_w3_12, sg_w3_13, sg_w3_14, sg_w3_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exB_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d efB w4 =
      star (c y0) * d z0 + star (c y1) * d z1 - star (c y2) * d z2 - star (c y3) * d z3 - star (c y4) * d z4 - star (c y5) * d z5 + star (c y6) * d z6 + star (c y7) * d z7 - star (c y8) * d z8 - star (c y9) * d z9 + star (c y10) * d z10 + star (c y11) * d z11 + star (c y12) * d z12 + star (c y13) * d z13 - star (c y14) * d z14 - star (c y15) * d z15 := by
  unfold offSum
  rw [incidenceB]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flipB_0, flipB_1, flipB_2, flipB_3, flipB_4, flipB_5, flipB_6, flipB_7, flipB_8, flipB_9, flipB_10, flipB_11, flipB_12, flipB_13, flipB_14, flipB_15]
  simp only [sg_w4_0, sg_w4_1, sg_w4_2, sg_w4_3, sg_w4_4, sg_w4_5, sg_w4_6, sg_w4_7, sg_w4_8, sg_w4_9, sg_w4_10, sg_w4_11, sg_w4_12, sg_w4_13, sg_w4_14, sg_w4_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exB_w5 (c d : SS.BitString 6 -> ℂ) :
    offSum c d efB w5 =
      - star (c y0) * d z0 + star (c y1) * d z1 - star (c y2) * d z2 + star (c y3) * d z3 - star (c y4) * d z4 + star (c y5) * d z5 + star (c y6) * d z6 - star (c y7) * d z7 - star (c y8) * d z8 + star (c y9) * d z9 + star (c y10) * d z10 - star (c y11) * d z11 + star (c y12) * d z12 - star (c y13) * d z13 + star (c y14) * d z14 - star (c y15) * d z15 := by
  unfold offSum
  rw [incidenceB]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flipB_0, flipB_1, flipB_2, flipB_3, flipB_4, flipB_5, flipB_6, flipB_7, flipB_8, flipB_9, flipB_10, flipB_11, flipB_12, flipB_13, flipB_14, flipB_15]
  simp only [sg_w5_0, sg_w5_1, sg_w5_2, sg_w5_3, sg_w5_4, sg_w5_5, sg_w5_6, sg_w5_7, sg_w5_8, sg_w5_9, sg_w5_10, sg_w5_11, sg_w5_12, sg_w5_13, sg_w5_14, sg_w5_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exB_w7 (c d : SS.BitString 6 -> ℂ) :
    offSum c d efB w7 =
      star (c y0) * d z0 + star (c y1) * d z1 - star (c y2) * d z2 - star (c y3) * d z3 + star (c y4) * d z4 + star (c y5) * d z5 - star (c y6) * d z6 - star (c y7) * d z7 + star (c y8) * d z8 + star (c y9) * d z9 - star (c y10) * d z10 - star (c y11) * d z11 + star (c y12) * d z12 + star (c y13) * d z13 - star (c y14) * d z14 - star (c y15) * d z15 := by
  unfold offSum
  rw [incidenceB]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flipB_0, flipB_1, flipB_2, flipB_3, flipB_4, flipB_5, flipB_6, flipB_7, flipB_8, flipB_9, flipB_10, flipB_11, flipB_12, flipB_13, flipB_14, flipB_15]
  simp only [sg_w7_0, sg_w7_1, sg_w7_2, sg_w7_3, sg_w7_4, sg_w7_5, sg_w7_6, sg_w7_7, sg_w7_8, sg_w7_9, sg_w7_10, sg_w7_11, sg_w7_12, sg_w7_13, sg_w7_14, sg_w7_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exB_w8 (c d : SS.BitString 6 -> ℂ) :
    offSum c d efB w8 =
      - star (c y0) * d z0 + star (c y1) * d z1 - star (c y2) * d z2 + star (c y3) * d z3 + star (c y4) * d z4 - star (c y5) * d z5 - star (c y6) * d z6 + star (c y7) * d z7 + star (c y8) * d z8 - star (c y9) * d z9 - star (c y10) * d z10 + star (c y11) * d z11 + star (c y12) * d z12 - star (c y13) * d z13 + star (c y14) * d z14 - star (c y15) * d z15 := by
  unfold offSum
  rw [incidenceB]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flipB_0, flipB_1, flipB_2, flipB_3, flipB_4, flipB_5, flipB_6, flipB_7, flipB_8, flipB_9, flipB_10, flipB_11, flipB_12, flipB_13, flipB_14, flipB_15]
  simp only [sg_w8_0, sg_w8_1, sg_w8_2, sg_w8_3, sg_w8_4, sg_w8_5, sg_w8_6, sg_w8_7, sg_w8_8, sg_w8_9, sg_w8_10, sg_w8_11, sg_w8_12, sg_w8_13, sg_w8_14, sg_w8_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exB_w10 (c d : SS.BitString 6 -> ℂ) :
    offSum c d efB w10 =
      star (c y0) * d z0 + star (c y1) * d z1 + star (c y2) * d z2 + star (c y3) * d z3 - star (c y4) * d z4 - star (c y5) * d z5 - star (c y6) * d z6 - star (c y7) * d z7 + star (c y8) * d z8 + star (c y9) * d z9 + star (c y10) * d z10 + star (c y11) * d z11 - star (c y12) * d z12 - star (c y13) * d z13 - star (c y14) * d z14 - star (c y15) * d z15 := by
  unfold offSum
  rw [incidenceB]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flipB_0, flipB_1, flipB_2, flipB_3, flipB_4, flipB_5, flipB_6, flipB_7, flipB_8, flipB_9, flipB_10, flipB_11, flipB_12, flipB_13, flipB_14, flipB_15]
  simp only [sg_w10_0, sg_w10_1, sg_w10_2, sg_w10_3, sg_w10_4, sg_w10_5, sg_w10_6, sg_w10_7, sg_w10_8, sg_w10_9, sg_w10_10, sg_w10_11, sg_w10_12, sg_w10_13, sg_w10_14, sg_w10_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exB_w11 (c d : SS.BitString 6 -> ℂ) :
    offSum c d efB w11 =
      - star (c y0) * d z0 + star (c y1) * d z1 + star (c y2) * d z2 - star (c y3) * d z3 - star (c y4) * d z4 + star (c y5) * d z5 - star (c y6) * d z6 + star (c y7) * d z7 + star (c y8) * d z8 - star (c y9) * d z9 + star (c y10) * d z10 - star (c y11) * d z11 - star (c y12) * d z12 + star (c y13) * d z13 + star (c y14) * d z14 - star (c y15) * d z15 := by
  unfold offSum
  rw [incidenceB]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flipB_0, flipB_1, flipB_2, flipB_3, flipB_4, flipB_5, flipB_6, flipB_7, flipB_8, flipB_9, flipB_10, flipB_11, flipB_12, flipB_13, flipB_14, flipB_15]
  simp only [sg_w11_0, sg_w11_1, sg_w11_2, sg_w11_3, sg_w11_4, sg_w11_5, sg_w11_6, sg_w11_7, sg_w11_8, sg_w11_9, sg_w11_10, sg_w11_11, sg_w11_12, sg_w11_13, sg_w11_14, sg_w11_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exB_w13 (c d : SS.BitString 6 -> ℂ) :
    offSum c d efB w13 =
      star (c y0) * d z0 + star (c y1) * d z1 + star (c y2) * d z2 + star (c y3) * d z3 + star (c y4) * d z4 + star (c y5) * d z5 + star (c y6) * d z6 + star (c y7) * d z7 - star (c y8) * d z8 - star (c y9) * d z9 - star (c y10) * d z10 - star (c y11) * d z11 - star (c y12) * d z12 - star (c y13) * d z13 - star (c y14) * d z14 - star (c y15) * d z15 := by
  unfold offSum
  rw [incidenceB]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flipB_0, flipB_1, flipB_2, flipB_3, flipB_4, flipB_5, flipB_6, flipB_7, flipB_8, flipB_9, flipB_10, flipB_11, flipB_12, flipB_13, flipB_14, flipB_15]
  simp only [sg_w13_0, sg_w13_1, sg_w13_2, sg_w13_3, sg_w13_4, sg_w13_5, sg_w13_6, sg_w13_7, sg_w13_8, sg_w13_9, sg_w13_10, sg_w13_11, sg_w13_12, sg_w13_13, sg_w13_14, sg_w13_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exB_w14 (c d : SS.BitString 6 -> ℂ) :
    offSum c d efB w14 =
      - star (c y0) * d z0 + star (c y1) * d z1 + star (c y2) * d z2 - star (c y3) * d z3 + star (c y4) * d z4 - star (c y5) * d z5 + star (c y6) * d z6 - star (c y7) * d z7 - star (c y8) * d z8 + star (c y9) * d z9 - star (c y10) * d z10 + star (c y11) * d z11 - star (c y12) * d z12 + star (c y13) * d z13 + star (c y14) * d z14 - star (c y15) * d z15 := by
  unfold offSum
  rw [incidenceB]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flipB_0, flipB_1, flipB_2, flipB_3, flipB_4, flipB_5, flipB_6, flipB_7, flipB_8, flipB_9, flipB_10, flipB_11, flipB_12, flipB_13, flipB_14, flipB_15]
  simp only [sg_w14_0, sg_w14_1, sg_w14_2, sg_w14_3, sg_w14_4, sg_w14_5, sg_w14_6, sg_w14_7, sg_w14_8, sg_w14_9, sg_w14_10, sg_w14_11, sg_w14_12, sg_w14_13, sg_w14_14, sg_w14_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

/-! ## The moment system -/

/-- The two normalizations, the twenty-one moment equalities, and the
nonnegativity of every probability.  These are exactly the pure-`Z`
Knill-Laflamme rows of physical weight at most two. -/
structure MomentSystem (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real) : Prop where
  n0 : q0 + q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 + q9 + q10 + q11 + q12 + q13 + q14 + q15 = 1
  n1 : r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15 = 1
  m1 : q8 + q9 + q10 + q11 + q12 + q13 + q14 + q15 = r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15
  m2 : q4 + q5 + q6 + q7 + q12 + q13 + q14 + q15 = r4 + r5 + r6 + r7 + r12 + r13 + r14 + r15
  m3 : q2 + q3 + q6 + q7 + q10 + q11 + q14 + q15 = r2 + r3 + r6 + r7 + r10 + r11 + r14 + r15
  m4 : q2 + q3 + q4 + q5 + q8 + q9 + q14 + q15 = r2 + r3 + r4 + r5 + r8 + r9 + r14 + r15
  m5 : q1 + q3 + q5 + q7 + q9 + q11 + q13 + q15 = r1 + r3 + r5 + r7 + r9 + r11 + r13 + r15
  m6 : q1 + q2 + q4 + q6 + q8 + q10 + q12 + q15 = r0 + r3 + r5 + r7 + r9 + r11 + r13 + r14
  m12 : q12 + q13 + q14 + q15 = r12 + r13 + r14 + r15
  m13 : q10 + q11 + q14 + q15 = r10 + r11 + r14 + r15
  m14 : q8 + q9 + q14 + q15 = r8 + r9 + r14 + r15
  m15 : q9 + q11 + q13 + q15 = r9 + r11 + r13 + r15
  m16 : q8 + q10 + q12 + q15 = r9 + r11 + r13 + r14
  m23 : q6 + q7 + q14 + q15 = r6 + r7 + r14 + r15
  m24 : q4 + q5 + q14 + q15 = r4 + r5 + r14 + r15
  m25 : q5 + q7 + q13 + q15 = r5 + r7 + r13 + r15
  m26 : q4 + q6 + q12 + q15 = r5 + r7 + r13 + r14
  m34 : q2 + q3 + q14 + q15 = r2 + r3 + r14 + r15
  m35 : q3 + q7 + q11 + q15 = r3 + r7 + r11 + r15
  m36 : q2 + q6 + q10 + q15 = r3 + r7 + r11 + r14
  m45 : q3 + q5 + q9 + q15 = r3 + r5 + r9 + r15
  m46 : q2 + q4 + q8 + q15 = r3 + r5 + r9 + r14
  m56 : q1 + q15 = r3 + r5 + r7 + r9 + r11 + r13

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

/-- The anchor masses.  `P0 = Q0` and `P4 = Q4` come from the two degree-two
shell projectors `g0` and `g4`; `P0 + P4 = 1/2` comes from the indicator
`u = n5 + n6 - 2 n5 n6` of `x5 != x6`. -/
theorem MomentSystem.anchors {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real}
    (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    q0 + q1 = r0 + r1 ∧ q14 + q15 = r14 + r15 ∧ q0 + q1 + q14 + q15 = 1/2 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, m12, m13, m14, m15, m16, m23, m24, m25, m26, m34, m35, m36, m45, m46, m56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-! ## The no-go -/

/-- **Orbit 19 is impossible.** -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11)) (Complex.normSq (c y12)) (Complex.normSq (c y13)) (Complex.normSq (c y14)) (Complex.normSq (c y15))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)) (Complex.normSq (d z12)) (Complex.normSq (d z13)) (Complex.normSq (d z14)) (Complex.normSq (d z15)))
    (h0 : offSum c d efA w0 = 0)
    (h1 : offSum c d efA w1 = 0)
    (h2 : offSum c d efA w2 = 0)
    (h3 : offSum c d efA w3 = 0)
    (h4 : offSum c d efA w4 = 0)
    (h5 : offSum c d efA w6 = 0)
    (h6 : offSum c d efA w7 = 0)
    (h7 : offSum c d efA w9 = 0)
    (h8 : offSum c d efA w10 = 0)
    (h9 : offSum c d efA w12 = 0)
    (h10 : offSum c d efA w13 = 0)
    (h11 : offSum c d efA w15 = 0)
    (h12 : offSum c d efB w0 = 0)
    (h13 : offSum c d efB w1 = 0)
    (h14 : offSum c d efB w2 = 0)
    (h15 : offSum c d efB w3 = 0)
    (h16 : offSum c d efB w4 = 0)
    (h17 : offSum c d efB w5 = 0)
    (h18 : offSum c d efB w7 = 0)
    (h19 : offSum c d efB w8 = 0)
    (h20 : offSum c d efB w10 = 0)
    (h21 : offSum c d efB w11 = 0)
    (h22 : offSum c d efB w13 = 0)
    (h23 : offSum c d efB w14 = 0)
    : False := by
  rw [exA_w0] at h0
  rw [exA_w1] at h1
  rw [exA_w2] at h2
  rw [exA_w3] at h3
  rw [exA_w4] at h4
  rw [exA_w6] at h5
  rw [exA_w7] at h6
  rw [exA_w9] at h7
  rw [exA_w10] at h8
  rw [exA_w12] at h9
  rw [exA_w13] at h10
  rw [exA_w15] at h11
  rw [exB_w0] at h12
  rw [exB_w1] at h13
  rw [exB_w2] at h14
  rw [exB_w3] at h15
  rw [exB_w4] at h16
  rw [exB_w5] at h17
  rw [exB_w7] at h18
  rw [exB_w8] at h19
  rw [exB_w10] at h20
  rw [exB_w11] at h21
  rw [exB_w13] at h22
  rw [exB_w14] at h23
  have p0 : star (c y1) * d z0 = 0 := by
    linear_combination (1/8 : ℂ) * h0 + (-1/8 : ℂ) * h1 + (1/8 : ℂ) * h2 + (-1/8 : ℂ) * h3 + (1/16 : ℂ) * h4 + (1/16 : ℂ) * h5 + (1/16 : ℂ) * h6 + (1/16 : ℂ) * h7 + (1/16 : ℂ) * h8 + (1/16 : ℂ) * h9 + (1/16 : ℂ) * h10 + (1/16 : ℂ) * h11
  have p1 : star (c y0) * d z1 = 0 := by
    linear_combination (1/8 : ℂ) * h0 + (1/8 : ℂ) * h1 + (-1/8 : ℂ) * h2 + (-1/8 : ℂ) * h3 + (1/16 : ℂ) * h4 + (-1/16 : ℂ) * h5 + (1/16 : ℂ) * h6 + (-1/16 : ℂ) * h7 + (1/16 : ℂ) * h8 + (-1/16 : ℂ) * h9 + (1/16 : ℂ) * h10 + (-1/16 : ℂ) * h11
  have p2 : star (c y15) * d z14 = 0 := by
    linear_combination (1/8 : ℂ) * h0 + (-1/8 : ℂ) * h1 + (1/8 : ℂ) * h2 + (-1/8 : ℂ) * h3 + (-1/16 : ℂ) * h4 + (-1/16 : ℂ) * h5 + (-1/16 : ℂ) * h6 + (-1/16 : ℂ) * h7 + (-1/16 : ℂ) * h8 + (-1/16 : ℂ) * h9 + (-1/16 : ℂ) * h10 + (-1/16 : ℂ) * h11
  have p3 : star (c y14) * d z15 = 0 := by
    linear_combination (1/8 : ℂ) * h0 + (1/8 : ℂ) * h1 + (-1/8 : ℂ) * h2 + (-1/8 : ℂ) * h3 + (-1/16 : ℂ) * h4 + (1/16 : ℂ) * h5 + (-1/16 : ℂ) * h6 + (1/16 : ℂ) * h7 + (-1/16 : ℂ) * h8 + (1/16 : ℂ) * h9 + (-1/16 : ℂ) * h10 + (1/16 : ℂ) * h11
  have p4 : star (c y0) * d z0 = 0 := by
    linear_combination (1/8 : ℂ) * h12 + (-1/8 : ℂ) * h13 + (1/8 : ℂ) * h14 + (-1/8 : ℂ) * h15 + (1/16 : ℂ) * h16 + (-1/16 : ℂ) * h17 + (1/16 : ℂ) * h18 + (-1/16 : ℂ) * h19 + (1/16 : ℂ) * h20 + (-1/16 : ℂ) * h21 + (1/16 : ℂ) * h22 + (-1/16 : ℂ) * h23
  have p5 : star (c y1) * d z1 = 0 := by
    linear_combination (1/8 : ℂ) * h12 + (1/8 : ℂ) * h13 + (-1/8 : ℂ) * h14 + (-1/8 : ℂ) * h15 + (1/16 : ℂ) * h16 + (1/16 : ℂ) * h17 + (1/16 : ℂ) * h18 + (1/16 : ℂ) * h19 + (1/16 : ℂ) * h20 + (1/16 : ℂ) * h21 + (1/16 : ℂ) * h22 + (1/16 : ℂ) * h23
  have p6 : star (c y14) * d z14 = 0 := by
    linear_combination (1/8 : ℂ) * h12 + (-1/8 : ℂ) * h13 + (1/8 : ℂ) * h14 + (-1/8 : ℂ) * h15 + (-1/16 : ℂ) * h16 + (1/16 : ℂ) * h17 + (-1/16 : ℂ) * h18 + (1/16 : ℂ) * h19 + (-1/16 : ℂ) * h20 + (1/16 : ℂ) * h21 + (-1/16 : ℂ) * h22 + (1/16 : ℂ) * h23
  have p7 : star (c y15) * d z15 = 0 := by
    linear_combination (1/8 : ℂ) * h12 + (1/8 : ℂ) * h13 + (-1/8 : ℂ) * h14 + (-1/8 : ℂ) * h15 + (-1/16 : ℂ) * h16 + (-1/16 : ℂ) * h17 + (-1/16 : ℂ) * h18 + (-1/16 : ℂ) * h19 + (-1/16 : ℂ) * h20 + (-1/16 : ℂ) * h21 + (-1/16 : ℂ) * h22 + (-1/16 : ℂ) * h23
  have n0 : Complex.normSq (c y1) * Complex.normSq (d z0) = 0 := nsqZero p0
  have n1 : Complex.normSq (c y0) * Complex.normSq (d z1) = 0 := nsqZero p1
  have n2 : Complex.normSq (c y15) * Complex.normSq (d z14) = 0 := nsqZero p2
  have n3 : Complex.normSq (c y14) * Complex.normSq (d z15) = 0 := nsqZero p3
  have n4 : Complex.normSq (c y0) * Complex.normSq (d z0) = 0 := nsqZero p4
  have n5 : Complex.normSq (c y1) * Complex.normSq (d z1) = 0 := nsqZero p5
  have n6 : Complex.normSq (c y14) * Complex.normSq (d z14) = 0 := nsqZero p6
  have n7 : Complex.normSq (c y15) * Complex.normSq (d z15) = 0 := nsqZero p7
  obtain ⟨a0, a4, ah⟩ := hm.anchors
  have z0m : (Complex.normSq (c y0) + Complex.normSq (c y1)) *
      (Complex.normSq (d z0) + Complex.normSq (d z1)) = 0 := by
    linear_combination n4 + n1 + n0 + n5
  have z4m : (Complex.normSq (c y14) + Complex.normSq (c y15)) *
      (Complex.normSq (d z14) + Complex.normSq (d z15)) = 0 := by
    linear_combination n6 + n3 + n2 + n7
  have sq0 : (Complex.normSq (c y0) + Complex.normSq (c y1)) *
      (Complex.normSq (c y0) + Complex.normSq (c y1)) = 0 := by
    linear_combination z0m + (Complex.normSq (c y0) + Complex.normSq (c y1)) * a0
  have sq4 : (Complex.normSq (c y14) + Complex.normSq (c y15)) *
      (Complex.normSq (c y14) + Complex.normSq (c y15)) = 0 := by
    linear_combination z4m + (Complex.normSq (c y14) + Complex.normSq (c y15)) * a4
  have e0 := mul_self_eq_zero.mp sq0
  have e4 := mul_self_eq_zero.mp sq4
  linarith

end

end SixQubit.Orbit19
