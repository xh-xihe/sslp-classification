import Mathlib

import SS.FullKL
import SixQubit.Common

/-!
# Six-qubit no-go for moment orbit 56

Orbit 56 of `six_qubit_sslp_v7.tex`: q = 6, angle vector
a = (1, 2, 2, 2, 3, 3), residues 0 and 1, closed in Section 14.

There is no star point here.  The hub is the grid point `y2`, whose
probability the moment system bounds below by `1/12` on both fibers.  Six
masks of rank two tie each of `y4..y9` directly to it, so the hub lemma pairs
any two of them and the three rank-one masks collapse to cross relations.
Converted to the bottom fiber these read

    u4 u7 + u5 u6 = 0,   u4 u9 + u5 u8 = 0,   u6 u9 + u7 u8 = 0,

and their product closes an odd cycle on all six amplitudes.  Each way a
factor could vanish is ruled out by the relation containing it: it drags a
second amplitude down with it, and every such pair leaves the moment polytope
infeasible -- a `linarith` step.

Everything computational is decided by the Lean kernel; `native_decide` is
not used.
-/

namespace SixQubit.Orbit56

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]

def y0 : SS.BitString 6 := bs false false false false false false  -- 000000
def y1 : SS.BitString 6 := bs false false false false true  true   -- 000011
def y2 : SS.BitString 6 := bs false true  true  true  false false  -- 011100
def y3 : SS.BitString 6 := bs false true  true  true  true  true   -- 011111
def y4 : SS.BitString 6 := bs true  false false true  false true   -- 100101
def y5 : SS.BitString 6 := bs true  false false true  true  false  -- 100110
def y6 : SS.BitString 6 := bs true  false true  false false true   -- 101001
def y7 : SS.BitString 6 := bs true  false true  false true  false  -- 101010
def y8 : SS.BitString 6 := bs true  true  false false false true   -- 110001
def y9 : SS.BitString 6 := bs true  true  false false true  false  -- 110010

def z0 : SS.BitString 6 := bs false false true  true  false true   -- 001101
def z1 : SS.BitString 6 := bs false false true  true  true  false  -- 001110
def z2 : SS.BitString 6 := bs false true  false true  false true   -- 010101
def z3 : SS.BitString 6 := bs false true  false true  true  false  -- 010110
def z4 : SS.BitString 6 := bs false true  true  false false true   -- 011001
def z5 : SS.BitString 6 := bs false true  true  false true  false  -- 011010
def z6 : SS.BitString 6 := bs true  false false false false false  -- 100000
def z7 : SS.BitString 6 := bs true  false false false true  true   -- 100011
def z8 : SS.BitString 6 := bs true  true  true  true  false false  -- 111100
def z9 : SS.BitString 6 := bs true  true  true  true  true  true   -- 111111

def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9}
def S1 : Finset (SS.BitString 6) := {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9}

def av : Fin 6 -> ZMod 6 := ![1, 2, 2, 2, 3, 3]

/-- Each support is exactly its residue fiber, decided over all 64 strings. -/
theorem S0_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 0) = S0 := by
  decide

theorem S1_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 1) = S1 := by
  decide

def ef0 : SS.BitString 6 := bs false false false true  false true   -- mask 000101
def ef1 : SS.BitString 6 := bs false false false true  true  false  -- mask 000110
def ef2 : SS.BitString 6 := bs false false true  false false true   -- mask 001001
def ef3 : SS.BitString 6 := bs false false true  false true  false  -- mask 001010
def ef4 : SS.BitString 6 := bs false true  false false false true   -- mask 010001
def ef5 : SS.BitString 6 := bs false true  false false true  false  -- mask 010010
def ef6 : SS.BitString 6 := bs true  false false true  false false  -- mask 100100
def ef7 : SS.BitString 6 := bs true  false true  false false false  -- mask 101000
def ef8 : SS.BitString 6 := bs true  true  false false false false  -- mask 110000
def w0 : SS.BitString 6 := bs false false false false false false  -- dressing 000000
def w1 : SS.BitString 6 := bs false false false false false true   -- dressing 000001
def w2 : SS.BitString 6 := bs false false false false true  false  -- dressing 000010
def w3 : SS.BitString 6 := bs false false false true  false false  -- dressing 000100
def w4 : SS.BitString 6 := bs false false false true  false true   -- dressing 000101
def w5 : SS.BitString 6 := bs false false false true  true  false  -- dressing 000110
def w6 : SS.BitString 6 := bs false false true  false false false  -- dressing 001000
def w7 : SS.BitString 6 := bs false false true  false false true   -- dressing 001001
def w8 : SS.BitString 6 := bs false false true  false true  false  -- dressing 001010
def w9 : SS.BitString 6 := bs false true  false false false false  -- dressing 010000
def w10 : SS.BitString 6 := bs false true  false false false true   -- dressing 010001
def w11 : SS.BitString 6 := bs false true  false false true  false  -- dressing 010010
def w12 : SS.BitString 6 := bs true  false false false false false  -- dressing 100000
def w13 : SS.BitString 6 := bs true  false false true  false false  -- dressing 100100
def w14 : SS.BitString 6 := bs true  false true  false false false  -- dressing 101000
def w15 : SS.BitString 6 := bs true  true  false false false false  -- dressing 110000

theorem incidence0 :
    S1.filter (fun y => SS.bxor y ef0 ∈ S0) = {z4, z5, z6, z7} := by decide
theorem fl0_4 : SS.bxor z4 ef0 = y2 := by decide
theorem fl0_5 : SS.bxor z5 ef0 = y3 := by decide
theorem fl0_6 : SS.bxor z6 ef0 = y4 := by decide
theorem fl0_7 : SS.bxor z7 ef0 = y5 := by decide
theorem sg0_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg0_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg0_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg0_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg0_w3_4 : SS.bdot w3 z4 = false := by decide
theorem sg0_w3_5 : SS.bdot w3 z5 = false := by decide
theorem sg0_w3_6 : SS.bdot w3 z6 = false := by decide
theorem sg0_w3_7 : SS.bdot w3 z7 = false := by decide
theorem sg0_w1_4 : SS.bdot w1 z4 = true := by decide
theorem sg0_w1_5 : SS.bdot w1 z5 = false := by decide
theorem sg0_w1_6 : SS.bdot w1 z6 = false := by decide
theorem sg0_w1_7 : SS.bdot w1 z7 = true := by decide
theorem sg0_w4_4 : SS.bdot w4 z4 = true := by decide
theorem sg0_w4_5 : SS.bdot w4 z5 = false := by decide
theorem sg0_w4_6 : SS.bdot w4 z6 = false := by decide
theorem sg0_w4_7 : SS.bdot w4 z7 = true := by decide
theorem incidence1 :
    S1.filter (fun y => SS.bxor y ef1 ∈ S0) = {z4, z5, z6, z7} := by decide
theorem fl1_4 : SS.bxor z4 ef1 = y3 := by decide
theorem fl1_5 : SS.bxor z5 ef1 = y2 := by decide
theorem fl1_6 : SS.bxor z6 ef1 = y5 := by decide
theorem fl1_7 : SS.bxor z7 ef1 = y4 := by decide
theorem sg1_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg1_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg1_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg1_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg1_w3_4 : SS.bdot w3 z4 = false := by decide
theorem sg1_w3_5 : SS.bdot w3 z5 = false := by decide
theorem sg1_w3_6 : SS.bdot w3 z6 = false := by decide
theorem sg1_w3_7 : SS.bdot w3 z7 = false := by decide
theorem sg1_w2_4 : SS.bdot w2 z4 = false := by decide
theorem sg1_w2_5 : SS.bdot w2 z5 = true := by decide
theorem sg1_w2_6 : SS.bdot w2 z6 = false := by decide
theorem sg1_w2_7 : SS.bdot w2 z7 = true := by decide
theorem sg1_w5_4 : SS.bdot w5 z4 = false := by decide
theorem sg1_w5_5 : SS.bdot w5 z5 = true := by decide
theorem sg1_w5_6 : SS.bdot w5 z6 = false := by decide
theorem sg1_w5_7 : SS.bdot w5 z7 = true := by decide
theorem incidence2 :
    S1.filter (fun y => SS.bxor y ef2 ∈ S0) = {z2, z3, z6, z7} := by decide
theorem fl2_2 : SS.bxor z2 ef2 = y2 := by decide
theorem fl2_3 : SS.bxor z3 ef2 = y3 := by decide
theorem fl2_6 : SS.bxor z6 ef2 = y6 := by decide
theorem fl2_7 : SS.bxor z7 ef2 = y7 := by decide
theorem sg2_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg2_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg2_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg2_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg2_w6_2 : SS.bdot w6 z2 = false := by decide
theorem sg2_w6_3 : SS.bdot w6 z3 = false := by decide
theorem sg2_w6_6 : SS.bdot w6 z6 = false := by decide
theorem sg2_w6_7 : SS.bdot w6 z7 = false := by decide
theorem sg2_w1_2 : SS.bdot w1 z2 = true := by decide
theorem sg2_w1_3 : SS.bdot w1 z3 = false := by decide
theorem sg2_w1_6 : SS.bdot w1 z6 = false := by decide
theorem sg2_w1_7 : SS.bdot w1 z7 = true := by decide
theorem sg2_w7_2 : SS.bdot w7 z2 = true := by decide
theorem sg2_w7_3 : SS.bdot w7 z3 = false := by decide
theorem sg2_w7_6 : SS.bdot w7 z6 = false := by decide
theorem sg2_w7_7 : SS.bdot w7 z7 = true := by decide
theorem incidence3 :
    S1.filter (fun y => SS.bxor y ef3 ∈ S0) = {z2, z3, z6, z7} := by decide
theorem fl3_2 : SS.bxor z2 ef3 = y3 := by decide
theorem fl3_3 : SS.bxor z3 ef3 = y2 := by decide
theorem fl3_6 : SS.bxor z6 ef3 = y7 := by decide
theorem fl3_7 : SS.bxor z7 ef3 = y6 := by decide
theorem sg3_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg3_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg3_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg3_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg3_w6_2 : SS.bdot w6 z2 = false := by decide
theorem sg3_w6_3 : SS.bdot w6 z3 = false := by decide
theorem sg3_w6_6 : SS.bdot w6 z6 = false := by decide
theorem sg3_w6_7 : SS.bdot w6 z7 = false := by decide
theorem sg3_w2_2 : SS.bdot w2 z2 = false := by decide
theorem sg3_w2_3 : SS.bdot w2 z3 = true := by decide
theorem sg3_w2_6 : SS.bdot w2 z6 = false := by decide
theorem sg3_w2_7 : SS.bdot w2 z7 = true := by decide
theorem sg3_w8_2 : SS.bdot w8 z2 = false := by decide
theorem sg3_w8_3 : SS.bdot w8 z3 = true := by decide
theorem sg3_w8_6 : SS.bdot w8 z6 = false := by decide
theorem sg3_w8_7 : SS.bdot w8 z7 = true := by decide
theorem incidence4 :
    S1.filter (fun y => SS.bxor y ef4 ∈ S0) = {z0, z1, z6, z7} := by decide
theorem fl4_0 : SS.bxor z0 ef4 = y2 := by decide
theorem fl4_1 : SS.bxor z1 ef4 = y3 := by decide
theorem fl4_6 : SS.bxor z6 ef4 = y8 := by decide
theorem fl4_7 : SS.bxor z7 ef4 = y9 := by decide
theorem sg4_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg4_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg4_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg4_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg4_w9_0 : SS.bdot w9 z0 = false := by decide
theorem sg4_w9_1 : SS.bdot w9 z1 = false := by decide
theorem sg4_w9_6 : SS.bdot w9 z6 = false := by decide
theorem sg4_w9_7 : SS.bdot w9 z7 = false := by decide
theorem sg4_w1_0 : SS.bdot w1 z0 = true := by decide
theorem sg4_w1_1 : SS.bdot w1 z1 = false := by decide
theorem sg4_w1_6 : SS.bdot w1 z6 = false := by decide
theorem sg4_w1_7 : SS.bdot w1 z7 = true := by decide
theorem sg4_w10_0 : SS.bdot w10 z0 = true := by decide
theorem sg4_w10_1 : SS.bdot w10 z1 = false := by decide
theorem sg4_w10_6 : SS.bdot w10 z6 = false := by decide
theorem sg4_w10_7 : SS.bdot w10 z7 = true := by decide
theorem incidence5 :
    S1.filter (fun y => SS.bxor y ef5 ∈ S0) = {z0, z1, z6, z7} := by decide
theorem fl5_0 : SS.bxor z0 ef5 = y3 := by decide
theorem fl5_1 : SS.bxor z1 ef5 = y2 := by decide
theorem fl5_6 : SS.bxor z6 ef5 = y9 := by decide
theorem fl5_7 : SS.bxor z7 ef5 = y8 := by decide
theorem sg5_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg5_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg5_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg5_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg5_w9_0 : SS.bdot w9 z0 = false := by decide
theorem sg5_w9_1 : SS.bdot w9 z1 = false := by decide
theorem sg5_w9_6 : SS.bdot w9 z6 = false := by decide
theorem sg5_w9_7 : SS.bdot w9 z7 = false := by decide
theorem sg5_w2_0 : SS.bdot w2 z0 = false := by decide
theorem sg5_w2_1 : SS.bdot w2 z1 = true := by decide
theorem sg5_w2_6 : SS.bdot w2 z6 = false := by decide
theorem sg5_w2_7 : SS.bdot w2 z7 = true := by decide
theorem sg5_w11_0 : SS.bdot w11 z0 = false := by decide
theorem sg5_w11_1 : SS.bdot w11 z1 = true := by decide
theorem sg5_w11_6 : SS.bdot w11 z6 = false := by decide
theorem sg5_w11_7 : SS.bdot w11 z7 = true := by decide
theorem incidence6 :
    S1.filter (fun y => SS.bxor y ef6 ∈ S0) = {z0, z1, z2, z3} := by decide
theorem fl6_0 : SS.bxor z0 ef6 = y6 := by decide
theorem fl6_1 : SS.bxor z1 ef6 = y7 := by decide
theorem fl6_2 : SS.bxor z2 ef6 = y8 := by decide
theorem fl6_3 : SS.bxor z3 ef6 = y9 := by decide
theorem sg6_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg6_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg6_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg6_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg6_w12_0 : SS.bdot w12 z0 = false := by decide
theorem sg6_w12_1 : SS.bdot w12 z1 = false := by decide
theorem sg6_w12_2 : SS.bdot w12 z2 = false := by decide
theorem sg6_w12_3 : SS.bdot w12 z3 = false := by decide
theorem sg6_w3_0 : SS.bdot w3 z0 = true := by decide
theorem sg6_w3_1 : SS.bdot w3 z1 = true := by decide
theorem sg6_w3_2 : SS.bdot w3 z2 = true := by decide
theorem sg6_w3_3 : SS.bdot w3 z3 = true := by decide
theorem sg6_w13_0 : SS.bdot w13 z0 = true := by decide
theorem sg6_w13_1 : SS.bdot w13 z1 = true := by decide
theorem sg6_w13_2 : SS.bdot w13 z2 = true := by decide
theorem sg6_w13_3 : SS.bdot w13 z3 = true := by decide
theorem incidence7 :
    S1.filter (fun y => SS.bxor y ef7 ∈ S0) = {z0, z1, z4, z5} := by decide
theorem fl7_0 : SS.bxor z0 ef7 = y4 := by decide
theorem fl7_1 : SS.bxor z1 ef7 = y5 := by decide
theorem fl7_4 : SS.bxor z4 ef7 = y8 := by decide
theorem fl7_5 : SS.bxor z5 ef7 = y9 := by decide
theorem sg7_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg7_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg7_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg7_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg7_w12_0 : SS.bdot w12 z0 = false := by decide
theorem sg7_w12_1 : SS.bdot w12 z1 = false := by decide
theorem sg7_w12_4 : SS.bdot w12 z4 = false := by decide
theorem sg7_w12_5 : SS.bdot w12 z5 = false := by decide
theorem sg7_w6_0 : SS.bdot w6 z0 = true := by decide
theorem sg7_w6_1 : SS.bdot w6 z1 = true := by decide
theorem sg7_w6_4 : SS.bdot w6 z4 = true := by decide
theorem sg7_w6_5 : SS.bdot w6 z5 = true := by decide
theorem sg7_w14_0 : SS.bdot w14 z0 = true := by decide
theorem sg7_w14_1 : SS.bdot w14 z1 = true := by decide
theorem sg7_w14_4 : SS.bdot w14 z4 = true := by decide
theorem sg7_w14_5 : SS.bdot w14 z5 = true := by decide
theorem incidence8 :
    S1.filter (fun y => SS.bxor y ef8 ∈ S0) = {z2, z3, z4, z5} := by decide
theorem fl8_2 : SS.bxor z2 ef8 = y4 := by decide
theorem fl8_3 : SS.bxor z3 ef8 = y5 := by decide
theorem fl8_4 : SS.bxor z4 ef8 = y6 := by decide
theorem fl8_5 : SS.bxor z5 ef8 = y7 := by decide
theorem sg8_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg8_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg8_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg8_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg8_w12_2 : SS.bdot w12 z2 = false := by decide
theorem sg8_w12_3 : SS.bdot w12 z3 = false := by decide
theorem sg8_w12_4 : SS.bdot w12 z4 = false := by decide
theorem sg8_w12_5 : SS.bdot w12 z5 = false := by decide
theorem sg8_w9_2 : SS.bdot w9 z2 = true := by decide
theorem sg8_w9_3 : SS.bdot w9 z3 = true := by decide
theorem sg8_w9_4 : SS.bdot w9 z4 = true := by decide
theorem sg8_w9_5 : SS.bdot w9 z5 = true := by decide
theorem sg8_w15_2 : SS.bdot w15 z2 = true := by decide
theorem sg8_w15_3 : SS.bdot w15 z3 = true := by decide
theorem sg8_w15_4 : SS.bdot w15 z4 = true := by decide
theorem sg8_w15_5 : SS.bdot w15 z5 = true := by decide

/-! ## The moment system -/

/-- The two normalizations, the twenty-one moment equalities, and the
nonnegativity of every probability. -/
structure MomentSystem (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Real) : Prop where
  n0 : q0 + q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 + q9 = 1
  n1 : r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 = 1
  m1 : q4 + q5 + q6 + q7 + q8 + q9 = r6 + r7 + r8 + r9
  m2 : q2 + q3 + q8 + q9 = r2 + r3 + r4 + r5 + r8 + r9
  m3 : q2 + q3 + q6 + q7 = r0 + r1 + r4 + r5 + r8 + r9
  m4 : q2 + q3 + q4 + q5 = r0 + r1 + r2 + r3 + r8 + r9
  m5 : q1 + q3 + q5 + q7 + q9 = r1 + r3 + r5 + r7 + r9
  m6 : q1 + q3 + q4 + q6 + q8 = r0 + r2 + r4 + r7 + r9
  c12 : q8 + q9 = r8 + r9
  c13 : q6 + q7 = r8 + r9
  c14 : q4 + q5 = r8 + r9
  c15 : q5 + q7 + q9 = r7 + r9
  c16 : q4 + q6 + q8 = r7 + r9
  c23 : q2 + q3 = r4 + r5 + r8 + r9
  c24 : q2 + q3 = r2 + r3 + r8 + r9
  c25 : q3 + q9 = r3 + r5 + r9
  c26 : q3 + q8 = r2 + r4 + r9
  c34 : q2 + q3 = r0 + r1 + r8 + r9
  c35 : q3 + q7 = r1 + r5 + r9
  c36 : q3 + q6 = r0 + r4 + r9
  c45 : q3 + q5 = r1 + r3 + r9
  c46 : q3 + q4 = r0 + r2 + r9
  c56 : q1 + q3 = r7 + r9

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

/-- The hub carries weight on both fibers. -/
theorem MomentSystem.hubpos {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) :
    1/12 ≤ q2 ∧ 1/12 ≤ r7 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9⟩ := h
  exact ⟨by linarith, by linarith⟩

/-- The polytope has no point with both y4 and y5 silent. -/
theorem MomentSystem.pair45 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9)
    (zi : q4 = 0) (zj : q5 = 0) : False := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9⟩ := h
  linarith

/-- The polytope has no point with both y4 and y6 silent. -/
theorem MomentSystem.pair46 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9)
    (zi : q4 = 0) (zj : q6 = 0) : False := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9⟩ := h
  linarith

/-- The polytope has no point with both y4 and y8 silent. -/
theorem MomentSystem.pair48 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9)
    (zi : q4 = 0) (zj : q8 = 0) : False := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9⟩ := h
  linarith

/-- The polytope has no point with both y5 and y7 silent. -/
theorem MomentSystem.pair57 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9)
    (zi : q5 = 0) (zj : q7 = 0) : False := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9⟩ := h
  linarith

/-- The polytope has no point with both y5 and y9 silent. -/
theorem MomentSystem.pair59 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9)
    (zi : q5 = 0) (zj : q9 = 0) : False := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9⟩ := h
  linarith

/-- The polytope has no point with both y6 and y7 silent. -/
theorem MomentSystem.pair67 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9)
    (zi : q6 = 0) (zj : q7 = 0) : False := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9⟩ := h
  linarith

/-- The polytope has no point with both y8 and y9 silent. -/
theorem MomentSystem.pair89 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9)
    (zi : q8 = 0) (zj : q9 = 0) : False := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9⟩ := h
  linarith

/-! ## The Walsh equations -/

def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),
      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

theorem ex0_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w0 = star (c y2) * d z4 + star (c y3) * d z5 + star (c y4) * d z6 + star (c y5) * d z7 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_4, fl0_5, fl0_6, fl0_7]
  simp only [sg0_w0_4, sg0_w0_5, sg0_w0_6, sg0_w0_7, SixQubit.signMul_false]
  try ring

theorem ex0_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w3 = star (c y2) * d z4 + star (c y3) * d z5 + star (c y4) * d z6 + star (c y5) * d z7 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_4, fl0_5, fl0_6, fl0_7]
  simp only [sg0_w3_4, sg0_w3_5, sg0_w3_6, sg0_w3_7, SixQubit.signMul_false]
  try ring

theorem ex0_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w1 = - star (c y2) * d z4 + star (c y3) * d z5 + star (c y4) * d z6 - star (c y5) * d z7 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_4, fl0_5, fl0_6, fl0_7]
  simp only [sg0_w1_4, sg0_w1_5, sg0_w1_6, sg0_w1_7, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex0_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w4 = - star (c y2) * d z4 + star (c y3) * d z5 + star (c y4) * d z6 - star (c y5) * d z7 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_4, fl0_5, fl0_6, fl0_7]
  simp only [sg0_w4_4, sg0_w4_5, sg0_w4_6, sg0_w4_7, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex1_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w0 = star (c y3) * d z4 + star (c y2) * d z5 + star (c y5) * d z6 + star (c y4) * d z7 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_4, fl1_5, fl1_6, fl1_7]
  simp only [sg1_w0_4, sg1_w0_5, sg1_w0_6, sg1_w0_7, SixQubit.signMul_false]
  try ring

theorem ex1_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w3 = star (c y3) * d z4 + star (c y2) * d z5 + star (c y5) * d z6 + star (c y4) * d z7 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_4, fl1_5, fl1_6, fl1_7]
  simp only [sg1_w3_4, sg1_w3_5, sg1_w3_6, sg1_w3_7, SixQubit.signMul_false]
  try ring

theorem ex1_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w2 = star (c y3) * d z4 - star (c y2) * d z5 + star (c y5) * d z6 - star (c y4) * d z7 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_4, fl1_5, fl1_6, fl1_7]
  simp only [sg1_w2_4, sg1_w2_5, sg1_w2_6, sg1_w2_7, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex1_w5 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w5 = star (c y3) * d z4 - star (c y2) * d z5 + star (c y5) * d z6 - star (c y4) * d z7 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_4, fl1_5, fl1_6, fl1_7]
  simp only [sg1_w5_4, sg1_w5_5, sg1_w5_6, sg1_w5_7, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex2_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w0 = star (c y2) * d z2 + star (c y3) * d z3 + star (c y6) * d z6 + star (c y7) * d z7 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_2, fl2_3, fl2_6, fl2_7]
  simp only [sg2_w0_2, sg2_w0_3, sg2_w0_6, sg2_w0_7, SixQubit.signMul_false]
  try ring

theorem ex2_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w6 = star (c y2) * d z2 + star (c y3) * d z3 + star (c y6) * d z6 + star (c y7) * d z7 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_2, fl2_3, fl2_6, fl2_7]
  simp only [sg2_w6_2, sg2_w6_3, sg2_w6_6, sg2_w6_7, SixQubit.signMul_false]
  try ring

theorem ex2_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w1 = - star (c y2) * d z2 + star (c y3) * d z3 + star (c y6) * d z6 - star (c y7) * d z7 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_2, fl2_3, fl2_6, fl2_7]
  simp only [sg2_w1_2, sg2_w1_3, sg2_w1_6, sg2_w1_7, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex2_w7 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w7 = - star (c y2) * d z2 + star (c y3) * d z3 + star (c y6) * d z6 - star (c y7) * d z7 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_2, fl2_3, fl2_6, fl2_7]
  simp only [sg2_w7_2, sg2_w7_3, sg2_w7_6, sg2_w7_7, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex3_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w0 = star (c y3) * d z2 + star (c y2) * d z3 + star (c y7) * d z6 + star (c y6) * d z7 := by
  unfold offSum
  rw [incidence3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl3_2, fl3_3, fl3_6, fl3_7]
  simp only [sg3_w0_2, sg3_w0_3, sg3_w0_6, sg3_w0_7, SixQubit.signMul_false]
  try ring

theorem ex3_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w6 = star (c y3) * d z2 + star (c y2) * d z3 + star (c y7) * d z6 + star (c y6) * d z7 := by
  unfold offSum
  rw [incidence3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl3_2, fl3_3, fl3_6, fl3_7]
  simp only [sg3_w6_2, sg3_w6_3, sg3_w6_6, sg3_w6_7, SixQubit.signMul_false]
  try ring

theorem ex3_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w2 = star (c y3) * d z2 - star (c y2) * d z3 + star (c y7) * d z6 - star (c y6) * d z7 := by
  unfold offSum
  rw [incidence3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl3_2, fl3_3, fl3_6, fl3_7]
  simp only [sg3_w2_2, sg3_w2_3, sg3_w2_6, sg3_w2_7, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex3_w8 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w8 = star (c y3) * d z2 - star (c y2) * d z3 + star (c y7) * d z6 - star (c y6) * d z7 := by
  unfold offSum
  rw [incidence3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl3_2, fl3_3, fl3_6, fl3_7]
  simp only [sg3_w8_2, sg3_w8_3, sg3_w8_6, sg3_w8_7, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex4_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w0 = star (c y2) * d z0 + star (c y3) * d z1 + star (c y8) * d z6 + star (c y9) * d z7 := by
  unfold offSum
  rw [incidence4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl4_0, fl4_1, fl4_6, fl4_7]
  simp only [sg4_w0_0, sg4_w0_1, sg4_w0_6, sg4_w0_7, SixQubit.signMul_false]
  try ring

theorem ex4_w9 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w9 = star (c y2) * d z0 + star (c y3) * d z1 + star (c y8) * d z6 + star (c y9) * d z7 := by
  unfold offSum
  rw [incidence4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl4_0, fl4_1, fl4_6, fl4_7]
  simp only [sg4_w9_0, sg4_w9_1, sg4_w9_6, sg4_w9_7, SixQubit.signMul_false]
  try ring

theorem ex4_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w1 = - star (c y2) * d z0 + star (c y3) * d z1 + star (c y8) * d z6 - star (c y9) * d z7 := by
  unfold offSum
  rw [incidence4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl4_0, fl4_1, fl4_6, fl4_7]
  simp only [sg4_w1_0, sg4_w1_1, sg4_w1_6, sg4_w1_7, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex4_w10 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w10 = - star (c y2) * d z0 + star (c y3) * d z1 + star (c y8) * d z6 - star (c y9) * d z7 := by
  unfold offSum
  rw [incidence4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl4_0, fl4_1, fl4_6, fl4_7]
  simp only [sg4_w10_0, sg4_w10_1, sg4_w10_6, sg4_w10_7, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex5_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef5 w0 = star (c y3) * d z0 + star (c y2) * d z1 + star (c y9) * d z6 + star (c y8) * d z7 := by
  unfold offSum
  rw [incidence5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl5_0, fl5_1, fl5_6, fl5_7]
  simp only [sg5_w0_0, sg5_w0_1, sg5_w0_6, sg5_w0_7, SixQubit.signMul_false]
  try ring

theorem ex5_w9 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef5 w9 = star (c y3) * d z0 + star (c y2) * d z1 + star (c y9) * d z6 + star (c y8) * d z7 := by
  unfold offSum
  rw [incidence5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl5_0, fl5_1, fl5_6, fl5_7]
  simp only [sg5_w9_0, sg5_w9_1, sg5_w9_6, sg5_w9_7, SixQubit.signMul_false]
  try ring

theorem ex5_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef5 w2 = star (c y3) * d z0 - star (c y2) * d z1 + star (c y9) * d z6 - star (c y8) * d z7 := by
  unfold offSum
  rw [incidence5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl5_0, fl5_1, fl5_6, fl5_7]
  simp only [sg5_w2_0, sg5_w2_1, sg5_w2_6, sg5_w2_7, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex5_w11 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef5 w11 = star (c y3) * d z0 - star (c y2) * d z1 + star (c y9) * d z6 - star (c y8) * d z7 := by
  unfold offSum
  rw [incidence5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl5_0, fl5_1, fl5_6, fl5_7]
  simp only [sg5_w11_0, sg5_w11_1, sg5_w11_6, sg5_w11_7, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex6_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w0 = star (c y6) * d z0 + star (c y7) * d z1 + star (c y8) * d z2 + star (c y9) * d z3 := by
  unfold offSum
  rw [incidence6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl6_0, fl6_1, fl6_2, fl6_3]
  simp only [sg6_w0_0, sg6_w0_1, sg6_w0_2, sg6_w0_3, SixQubit.signMul_false]
  try ring

theorem ex6_w12 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w12 = star (c y6) * d z0 + star (c y7) * d z1 + star (c y8) * d z2 + star (c y9) * d z3 := by
  unfold offSum
  rw [incidence6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl6_0, fl6_1, fl6_2, fl6_3]
  simp only [sg6_w12_0, sg6_w12_1, sg6_w12_2, sg6_w12_3, SixQubit.signMul_false]
  try ring

theorem ex6_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w3 = - star (c y6) * d z0 - star (c y7) * d z1 - star (c y8) * d z2 - star (c y9) * d z3 := by
  unfold offSum
  rw [incidence6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl6_0, fl6_1, fl6_2, fl6_3]
  simp only [sg6_w3_0, sg6_w3_1, sg6_w3_2, sg6_w3_3, SixQubit.signMul_true]
  try ring

theorem ex6_w13 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w13 = - star (c y6) * d z0 - star (c y7) * d z1 - star (c y8) * d z2 - star (c y9) * d z3 := by
  unfold offSum
  rw [incidence6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl6_0, fl6_1, fl6_2, fl6_3]
  simp only [sg6_w13_0, sg6_w13_1, sg6_w13_2, sg6_w13_3, SixQubit.signMul_true]
  try ring

theorem ex7_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef7 w0 = star (c y4) * d z0 + star (c y5) * d z1 + star (c y8) * d z4 + star (c y9) * d z5 := by
  unfold offSum
  rw [incidence7]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl7_0, fl7_1, fl7_4, fl7_5]
  simp only [sg7_w0_0, sg7_w0_1, sg7_w0_4, sg7_w0_5, SixQubit.signMul_false]
  try ring

theorem ex7_w12 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef7 w12 = star (c y4) * d z0 + star (c y5) * d z1 + star (c y8) * d z4 + star (c y9) * d z5 := by
  unfold offSum
  rw [incidence7]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl7_0, fl7_1, fl7_4, fl7_5]
  simp only [sg7_w12_0, sg7_w12_1, sg7_w12_4, sg7_w12_5, SixQubit.signMul_false]
  try ring

theorem ex7_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef7 w6 = - star (c y4) * d z0 - star (c y5) * d z1 - star (c y8) * d z4 - star (c y9) * d z5 := by
  unfold offSum
  rw [incidence7]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl7_0, fl7_1, fl7_4, fl7_5]
  simp only [sg7_w6_0, sg7_w6_1, sg7_w6_4, sg7_w6_5, SixQubit.signMul_true]
  try ring

theorem ex7_w14 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef7 w14 = - star (c y4) * d z0 - star (c y5) * d z1 - star (c y8) * d z4 - star (c y9) * d z5 := by
  unfold offSum
  rw [incidence7]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl7_0, fl7_1, fl7_4, fl7_5]
  simp only [sg7_w14_0, sg7_w14_1, sg7_w14_4, sg7_w14_5, SixQubit.signMul_true]
  try ring

theorem ex8_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef8 w0 = star (c y4) * d z2 + star (c y5) * d z3 + star (c y6) * d z4 + star (c y7) * d z5 := by
  unfold offSum
  rw [incidence8]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl8_2, fl8_3, fl8_4, fl8_5]
  simp only [sg8_w0_2, sg8_w0_3, sg8_w0_4, sg8_w0_5, SixQubit.signMul_false]
  try ring

theorem ex8_w12 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef8 w12 = star (c y4) * d z2 + star (c y5) * d z3 + star (c y6) * d z4 + star (c y7) * d z5 := by
  unfold offSum
  rw [incidence8]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl8_2, fl8_3, fl8_4, fl8_5]
  simp only [sg8_w12_2, sg8_w12_3, sg8_w12_4, sg8_w12_5, SixQubit.signMul_false]
  try ring

theorem ex8_w9 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef8 w9 = - star (c y4) * d z2 - star (c y5) * d z3 - star (c y6) * d z4 - star (c y7) * d z5 := by
  unfold offSum
  rw [incidence8]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl8_2, fl8_3, fl8_4, fl8_5]
  simp only [sg8_w9_2, sg8_w9_3, sg8_w9_4, sg8_w9_5, SixQubit.signMul_true]
  try ring

theorem ex8_w15 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef8 w15 = - star (c y4) * d z2 - star (c y5) * d z3 - star (c y6) * d z4 - star (c y7) * d z5 := by
  unfold offSum
  rw [incidence8]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl8_2, fl8_3, fl8_4, fl8_5]
  simp only [sg8_w15_2, sg8_w15_3, sg8_w15_4, sg8_w15_5, SixQubit.signMul_true]
  try ring

/-! ## Hub links, pairings, and the bottom relations -/

/-- y4 is tied to the hub. -/
theorem link4 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef1 w0 = 0)
    (h1 : offSum c d ef1 w2 = 0)
    : star (c y4) * d z7 + star (c y2) * d z5 = 0 := by
  rw [ex1_w0] at h0
  rw [ex1_w2] at h1
  linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1

/-- y5 is tied to the hub. -/
theorem link5 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef0 w0 = 0)
    (h1 : offSum c d ef0 w1 = 0)
    : star (c y5) * d z7 + star (c y2) * d z4 = 0 := by
  rw [ex0_w0] at h0
  rw [ex0_w1] at h1
  linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1

/-- y6 is tied to the hub. -/
theorem link6 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef3 w0 = 0)
    (h1 : offSum c d ef3 w2 = 0)
    : star (c y6) * d z7 + star (c y2) * d z3 = 0 := by
  rw [ex3_w0] at h0
  rw [ex3_w2] at h1
  linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1

/-- y7 is tied to the hub. -/
theorem link7 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef2 w0 = 0)
    (h1 : offSum c d ef2 w1 = 0)
    : star (c y7) * d z7 + star (c y2) * d z2 = 0 := by
  rw [ex2_w0] at h0
  rw [ex2_w1] at h1
  linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1

/-- y8 is tied to the hub. -/
theorem link8 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef5 w0 = 0)
    (h1 : offSum c d ef5 w2 = 0)
    : star (c y8) * d z7 + star (c y2) * d z1 = 0 := by
  rw [ex5_w0] at h0
  rw [ex5_w2] at h1
  linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1

/-- y9 is tied to the hub. -/
theorem link9 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef4 w0 = 0)
    (h1 : offSum c d ef4 w1 = 0)
    : star (c y9) * d z7 + star (c y2) * d z0 = 0 := by
  rw [ex4_w0] at h0
  rw [ex4_w1] at h1
  linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1

/-- Two points tied to the hub have their cross products paired. -/
theorem hub (c d : SS.BitString 6 -> ℂ) (x1 x2 : SS.BitString 6)
    (yh1 yh2 : SS.BitString 6)
    (h1 : star (c x1) * d z7 + star (c y2) * d yh1 = 0)
    (h2 : star (c x2) * d z7 + star (c y2) * d yh2 = 0)
    (hs : star (c y2) * d z7 ≠ 0) :
    star (c x2) * d yh1 = star (c x1) * d yh2 := by
  have key : (star (c x2) * d yh1 - star (c x1) * d yh2) *
      (star (c y2) * d z7) = 0 := by
    linear_combination (star (c x2) * d z7) * h1 - (star (c x1) * d z7) * h2
  rcases mul_eq_zero.mp key with h | h
  · linear_combination h
  · exact absurd h hs

/-- With both partners tied to the hub, a collapsed relation descends to the
bottom fiber. -/
theorem to_bottom (c d : SS.BitString 6 -> ℂ)
    (ua ub ue uf : SS.BitString 6) (bh fh : SS.BitString 6)
    (hb : star (c ub) * d z7 + star (c y2) * d bh = 0)
    (hf : star (c uf) * d z7 + star (c y2) * d fh = 0)
    (hs : d z7 ≠ 0)
    (hperm : star (c ua) * d bh + star (c ue) * d fh = 0)
    : star (c ua) * star (c ub) + star (c ue) * star (c uf) = 0 := by
  have key : (star (c ua) * star (c ub) + star (c ue) * star (c uf)) * d z7 = 0 := by
    linear_combination (star (c ua)) * hb + (star (c ue)) * hf
      - (star (c y2)) * hperm
  rcases mul_eq_zero.mp key with h | h
  · exact h
  · exact absurd h hs

/-- The rank-one mask 100100, collapsed. -/
theorem cross6 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef6 w0 = 0)
    (s1 : star (c y9) * d z3 = star (c y6) * d z0)
    (s2 : star (c y8) * d z2 = star (c y7) * d z1)
    : star (c y6) * d z0 + star (c y7) * d z1 = 0 := by
  rw [ex6_w0] at h0
  linear_combination (1 : ℂ) / 2 * h0 - s1 / 2 - s2 / 2

/-- The rank-one mask 101000, collapsed. -/
theorem cross7 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef7 w0 = 0)
    (s1 : star (c y9) * d z5 = star (c y4) * d z0)
    (s2 : star (c y8) * d z4 = star (c y5) * d z1)
    : star (c y4) * d z0 + star (c y5) * d z1 = 0 := by
  rw [ex7_w0] at h0
  linear_combination (1 : ℂ) / 2 * h0 - s1 / 2 - s2 / 2

/-- The rank-one mask 110000, collapsed. -/
theorem cross8 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef8 w0 = 0)
    (s1 : star (c y7) * d z5 = star (c y4) * d z2)
    (s2 : star (c y6) * d z4 = star (c y5) * d z3)
    : star (c y4) * d z2 + star (c y5) * d z3 = 0 := by
  rw [ex8_w0] at h0
  linear_combination (1 : ℂ) / 2 * h0 - s1 / 2 - s2 / 2

/-! ## The no-go -/

set_option maxHeartbeats 1000000 in
/-- **Orbit 56 is impossible.** -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)))
    (E0_w0 : offSum c d ef0 w0 = 0)
    (_E0_w3 : offSum c d ef0 w3 = 0)
    (E0_w1 : offSum c d ef0 w1 = 0)
    (_E0_w4 : offSum c d ef0 w4 = 0)
    (E1_w0 : offSum c d ef1 w0 = 0)
    (_E1_w3 : offSum c d ef1 w3 = 0)
    (E1_w2 : offSum c d ef1 w2 = 0)
    (_E1_w5 : offSum c d ef1 w5 = 0)
    (E2_w0 : offSum c d ef2 w0 = 0)
    (_E2_w6 : offSum c d ef2 w6 = 0)
    (E2_w1 : offSum c d ef2 w1 = 0)
    (_E2_w7 : offSum c d ef2 w7 = 0)
    (E3_w0 : offSum c d ef3 w0 = 0)
    (_E3_w6 : offSum c d ef3 w6 = 0)
    (E3_w2 : offSum c d ef3 w2 = 0)
    (_E3_w8 : offSum c d ef3 w8 = 0)
    (E4_w0 : offSum c d ef4 w0 = 0)
    (_E4_w9 : offSum c d ef4 w9 = 0)
    (E4_w1 : offSum c d ef4 w1 = 0)
    (_E4_w10 : offSum c d ef4 w10 = 0)
    (E5_w0 : offSum c d ef5 w0 = 0)
    (_E5_w9 : offSum c d ef5 w9 = 0)
    (E5_w2 : offSum c d ef5 w2 = 0)
    (_E5_w11 : offSum c d ef5 w11 = 0)
    (E6_w0 : offSum c d ef6 w0 = 0)
    (_E6_w12 : offSum c d ef6 w12 = 0)
    (_E6_w3 : offSum c d ef6 w3 = 0)
    (_E6_w13 : offSum c d ef6 w13 = 0)
    (E7_w0 : offSum c d ef7 w0 = 0)
    (_E7_w12 : offSum c d ef7 w12 = 0)
    (_E7_w6 : offSum c d ef7 w6 = 0)
    (_E7_w14 : offSum c d ef7 w14 = 0)
    (E8_w0 : offSum c d ef8 w0 = 0)
    (_E8_w12 : offSum c d ef8 w12 = 0)
    (_E8_w9 : offSum c d ef8 w9 = 0)
    (_E8_w15 : offSum c d ef8 w15 = 0)
    : False := by
  obtain ⟨hq, hr⟩ := hm.hubpos
  have hcH : c y2 ≠ 0 := fun h => by rw [h] at hq; simp at hq; linarith
  have hdH : d z7 ≠ 0 := fun h => by rw [h] at hr; simp at hr; linarith
  have hstar : star (c y2) * d z7 ≠ 0 :=
    mul_ne_zero (star_ne_zero.mpr hcH) hdH
  have L4 := link4 c d E1_w0 E1_w2
  have L5 := link5 c d E0_w0 E0_w1
  have L6 := link6 c d E3_w0 E3_w2
  have L7 := link7 c d E2_w0 E2_w1
  have L8 := link8 c d E5_w0 E5_w2
  have L9 := link9 c d E4_w0 E4_w1
  have s0a := hub c d y6 y9 z3 z0 L6 L9 hstar
  have s0b := hub c d y7 y8 z2 z1 L7 L8 hstar
  have C0 := cross6 c d E6_w0 s0a s0b
  have B0 := to_bottom c d y6 y9 y7 y8 z0 z1 L9 L8 hdH C0
  have s1a := hub c d y4 y9 z5 z0 L4 L9 hstar
  have s1b := hub c d y5 y8 z4 z1 L5 L8 hstar
  have C1 := cross7 c d E7_w0 s1a s1b
  have B1 := to_bottom c d y4 y9 y5 y8 z0 z1 L9 L8 hdH C1
  have s2a := hub c d y4 y7 z5 z2 L4 L7 hstar
  have s2b := hub c d y5 y6 z4 z3 L5 L6 hstar
  have C2 := cross8 c d E8_w0 s2a s2b
  have B2 := to_bottom c d y4 y7 y5 y6 z2 z3 L7 L6 hdH C2
  have N4 : c y4 ≠ 0 := by
    intro hz
    have hus : star (c y4) = 0 := by rw [hz]; simp
    have hp : star (c y5) * star (c y6) = 0 := by
      rw [hus] at B2; linear_combination B2
    have zf : Complex.normSq (c y4) = 0 := by rw [hz]; simp
    rcases mul_eq_zero.mp hp with h | h
    · exact hm.pair45 zf (by rw [show c y5 = 0 from by simpa using congrArg star h]; simp)
    · exact hm.pair46 zf (by rw [show c y6 = 0 from by simpa using congrArg star h]; simp)
  have N5 : c y5 ≠ 0 := by
    intro hz
    have hus : star (c y5) = 0 := by rw [hz]; simp
    have hp : star (c y4) * star (c y7) = 0 := by
      rw [hus] at B2; linear_combination B2
    have zf : Complex.normSq (c y5) = 0 := by rw [hz]; simp
    rcases mul_eq_zero.mp hp with h | h
    · exact hm.pair45 (by rw [show c y4 = 0 from by simpa using congrArg star h]; simp) zf
    · exact hm.pair57 zf (by rw [show c y7 = 0 from by simpa using congrArg star h]; simp)
  have N6 : c y6 ≠ 0 := by
    intro hz
    have hus : star (c y6) = 0 := by rw [hz]; simp
    have hp : star (c y4) * star (c y7) = 0 := by
      rw [hus] at B2; linear_combination B2
    have zf : Complex.normSq (c y6) = 0 := by rw [hz]; simp
    rcases mul_eq_zero.mp hp with h | h
    · exact hm.pair46 (by rw [show c y4 = 0 from by simpa using congrArg star h]; simp) zf
    · exact hm.pair67 zf (by rw [show c y7 = 0 from by simpa using congrArg star h]; simp)
  have N7 : c y7 ≠ 0 := by
    intro hz
    have hus : star (c y7) = 0 := by rw [hz]; simp
    have hp : star (c y5) * star (c y6) = 0 := by
      rw [hus] at B2; linear_combination B2
    have zf : Complex.normSq (c y7) = 0 := by rw [hz]; simp
    rcases mul_eq_zero.mp hp with h | h
    · exact hm.pair57 (by rw [show c y5 = 0 from by simpa using congrArg star h]; simp) zf
    · exact hm.pair67 (by rw [show c y6 = 0 from by simpa using congrArg star h]; simp) zf
  have N8 : c y8 ≠ 0 := by
    intro hz
    have hus : star (c y8) = 0 := by rw [hz]; simp
    have hp : star (c y4) * star (c y9) = 0 := by
      rw [hus] at B1; linear_combination B1
    have zf : Complex.normSq (c y8) = 0 := by rw [hz]; simp
    rcases mul_eq_zero.mp hp with h | h
    · exact hm.pair48 (by rw [show c y4 = 0 from by simpa using congrArg star h]; simp) zf
    · exact hm.pair89 zf (by rw [show c y9 = 0 from by simpa using congrArg star h]; simp)
  have N9 : c y9 ≠ 0 := by
    intro hz
    have hus : star (c y9) = 0 := by rw [hz]; simp
    have hp : star (c y5) * star (c y8) = 0 := by
      rw [hus] at B1; linear_combination B1
    have zf : Complex.normSq (c y9) = 0 := by rw [hz]; simp
    rcases mul_eq_zero.mp hp with h | h
    · exact hm.pair59 (by rw [show c y5 = 0 from by simpa using congrArg star h]; simp) zf
    · exact hm.pair89 (by rw [show c y8 = 0 from by simpa using congrArg star h]; simp) zf
  have key : (2 : ℂ) * ((star (c y4)) * (star (c y5)) * (star (c y6)) * (star (c y7)) * (star (c y8)) * (star (c y9))) = 0 := by
    linear_combination (star (c y5) * star (c y8) * (star (c y6) * star (c y9))) * B2
      - (star (c y5) * star (c y6) * (star (c y6) * star (c y9))) * B1
      + (star (c y5) * star (c y6) * (star (c y4) * star (c y9))) * B0
  have hz : (star (c y4)) * (star (c y5)) * (star (c y6)) * (star (c y7)) * (star (c y8)) * (star (c y9)) = 0 := by linear_combination key / 2
  simp [N4, N5, N6, N7, N8, N9] at hz

end

end SixQubit.Orbit56
