import Mathlib

import SS.FullKL
import SixQubit.Common

/-!
# Six-qubit no-go for moment orbit 46

Orbit 46 of `six_qubit_sslp.tex`: q = 6, angle vector
a = (1, 2, 2, 2, 3, 3), residues 0 and 3.

The flip mask 000001 has 10 incidences, and the admissible dressings
isolate 10 of them individually.  For each isolated incidence the
moment system ties the two endpoint probabilities by a positive ratio,
so either branch of `mul_eq_zero` kills both.  The resulting vanishing
set is inconsistent with the moment system.

Everything computational is decided by the Lean kernel; `native_decide`
is not used.
-/

namespace SixQubit.Orbit46

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

/-! ## The two fibers -/

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

def z0 : SS.BitString 6 := bs false false false false false true   -- 000001
def z1 : SS.BitString 6 := bs false false false false true  false  -- 000010
def z2 : SS.BitString 6 := bs false true  true  true  false true   -- 011101
def z3 : SS.BitString 6 := bs false true  true  true  true  false  -- 011110
def z4 : SS.BitString 6 := bs true  false false true  false false  -- 100100
def z5 : SS.BitString 6 := bs true  false false true  true  true   -- 100111
def z6 : SS.BitString 6 := bs true  false true  false false false  -- 101000
def z7 : SS.BitString 6 := bs true  false true  false true  true   -- 101011
def z8 : SS.BitString 6 := bs true  true  false false false false  -- 110000
def z9 : SS.BitString 6 := bs true  true  false false true  true   -- 110011

def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9}
def S1 : Finset (SS.BitString 6) := {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9}

def av : Fin 6 -> ZMod 6 := ![1, 2, 2, 2, 3, 3]

theorem S0_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 0) = S0 := by
  decide

theorem S1_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 3) = S1 := by
  decide

/-! ## The flip mask and its incidences -/

def ef : SS.BitString 6 := bs false false false false false true   -- 000001

theorem incidence :
    S1.filter (fun y => SS.bxor y ef ∈ S0) = {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9} := by decide

theorem flip_z0 : SS.bxor z0 ef = y0 := by decide
theorem flip_z1 : SS.bxor z1 ef = y1 := by decide
theorem flip_z2 : SS.bxor z2 ef = y2 := by decide
theorem flip_z3 : SS.bxor z3 ef = y3 := by decide
theorem flip_z4 : SS.bxor z4 ef = y4 := by decide
theorem flip_z5 : SS.bxor z5 ef = y5 := by decide
theorem flip_z6 : SS.bxor z6 ef = y6 := by decide
theorem flip_z7 : SS.bxor z7 ef = y7 := by decide
theorem flip_z8 : SS.bxor z8 ef = y8 := by decide
theorem flip_z9 : SS.bxor z9 ef = y9 := by decide

def w0 : SS.BitString 6 := bs false false false false false false  -- 000000
def w1 : SS.BitString 6 := bs false false false false false true   -- 000001
def w2 : SS.BitString 6 := bs false false false false true  false  -- 000010
def w3 : SS.BitString 6 := bs false false false false true  true   -- 000011
def w4 : SS.BitString 6 := bs false false false true  false false  -- 000100
def w5 : SS.BitString 6 := bs false false false true  false true   -- 000101
def w6 : SS.BitString 6 := bs false false true  false false false  -- 001000
def w7 : SS.BitString 6 := bs false false true  false false true   -- 001001
def w8 : SS.BitString 6 := bs false true  false false false false  -- 010000
def w9 : SS.BitString 6 := bs false true  false false false true   -- 010001
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
theorem sg_w1_0 : SS.bdot w1 z0 = true := by decide
theorem sg_w1_1 : SS.bdot w1 z1 = false := by decide
theorem sg_w1_2 : SS.bdot w1 z2 = true := by decide
theorem sg_w1_3 : SS.bdot w1 z3 = false := by decide
theorem sg_w1_4 : SS.bdot w1 z4 = false := by decide
theorem sg_w1_5 : SS.bdot w1 z5 = true := by decide
theorem sg_w1_6 : SS.bdot w1 z6 = false := by decide
theorem sg_w1_7 : SS.bdot w1 z7 = true := by decide
theorem sg_w1_8 : SS.bdot w1 z8 = false := by decide
theorem sg_w1_9 : SS.bdot w1 z9 = true := by decide
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
theorem sg_w3_0 : SS.bdot w3 z0 = true := by decide
theorem sg_w3_1 : SS.bdot w3 z1 = true := by decide
theorem sg_w3_2 : SS.bdot w3 z2 = true := by decide
theorem sg_w3_3 : SS.bdot w3 z3 = true := by decide
theorem sg_w3_4 : SS.bdot w3 z4 = false := by decide
theorem sg_w3_5 : SS.bdot w3 z5 = false := by decide
theorem sg_w3_6 : SS.bdot w3 z6 = false := by decide
theorem sg_w3_7 : SS.bdot w3 z7 = false := by decide
theorem sg_w3_8 : SS.bdot w3 z8 = false := by decide
theorem sg_w3_9 : SS.bdot w3 z9 = false := by decide
theorem sg_w4_0 : SS.bdot w4 z0 = false := by decide
theorem sg_w4_1 : SS.bdot w4 z1 = false := by decide
theorem sg_w4_2 : SS.bdot w4 z2 = true := by decide
theorem sg_w4_3 : SS.bdot w4 z3 = true := by decide
theorem sg_w4_4 : SS.bdot w4 z4 = true := by decide
theorem sg_w4_5 : SS.bdot w4 z5 = true := by decide
theorem sg_w4_6 : SS.bdot w4 z6 = false := by decide
theorem sg_w4_7 : SS.bdot w4 z7 = false := by decide
theorem sg_w4_8 : SS.bdot w4 z8 = false := by decide
theorem sg_w4_9 : SS.bdot w4 z9 = false := by decide
theorem sg_w5_0 : SS.bdot w5 z0 = true := by decide
theorem sg_w5_1 : SS.bdot w5 z1 = false := by decide
theorem sg_w5_2 : SS.bdot w5 z2 = false := by decide
theorem sg_w5_3 : SS.bdot w5 z3 = true := by decide
theorem sg_w5_4 : SS.bdot w5 z4 = true := by decide
theorem sg_w5_5 : SS.bdot w5 z5 = false := by decide
theorem sg_w5_6 : SS.bdot w5 z6 = false := by decide
theorem sg_w5_7 : SS.bdot w5 z7 = true := by decide
theorem sg_w5_8 : SS.bdot w5 z8 = false := by decide
theorem sg_w5_9 : SS.bdot w5 z9 = true := by decide
theorem sg_w6_0 : SS.bdot w6 z0 = false := by decide
theorem sg_w6_1 : SS.bdot w6 z1 = false := by decide
theorem sg_w6_2 : SS.bdot w6 z2 = true := by decide
theorem sg_w6_3 : SS.bdot w6 z3 = true := by decide
theorem sg_w6_4 : SS.bdot w6 z4 = false := by decide
theorem sg_w6_5 : SS.bdot w6 z5 = false := by decide
theorem sg_w6_6 : SS.bdot w6 z6 = true := by decide
theorem sg_w6_7 : SS.bdot w6 z7 = true := by decide
theorem sg_w6_8 : SS.bdot w6 z8 = false := by decide
theorem sg_w6_9 : SS.bdot w6 z9 = false := by decide
theorem sg_w7_0 : SS.bdot w7 z0 = true := by decide
theorem sg_w7_1 : SS.bdot w7 z1 = false := by decide
theorem sg_w7_2 : SS.bdot w7 z2 = false := by decide
theorem sg_w7_3 : SS.bdot w7 z3 = true := by decide
theorem sg_w7_4 : SS.bdot w7 z4 = false := by decide
theorem sg_w7_5 : SS.bdot w7 z5 = true := by decide
theorem sg_w7_6 : SS.bdot w7 z6 = true := by decide
theorem sg_w7_7 : SS.bdot w7 z7 = false := by decide
theorem sg_w7_8 : SS.bdot w7 z8 = false := by decide
theorem sg_w7_9 : SS.bdot w7 z9 = true := by decide
theorem sg_w8_0 : SS.bdot w8 z0 = false := by decide
theorem sg_w8_1 : SS.bdot w8 z1 = false := by decide
theorem sg_w8_2 : SS.bdot w8 z2 = true := by decide
theorem sg_w8_3 : SS.bdot w8 z3 = true := by decide
theorem sg_w8_4 : SS.bdot w8 z4 = false := by decide
theorem sg_w8_5 : SS.bdot w8 z5 = false := by decide
theorem sg_w8_6 : SS.bdot w8 z6 = false := by decide
theorem sg_w8_7 : SS.bdot w8 z7 = false := by decide
theorem sg_w8_8 : SS.bdot w8 z8 = true := by decide
theorem sg_w8_9 : SS.bdot w8 z9 = true := by decide
theorem sg_w9_0 : SS.bdot w9 z0 = true := by decide
theorem sg_w9_1 : SS.bdot w9 z1 = false := by decide
theorem sg_w9_2 : SS.bdot w9 z2 = false := by decide
theorem sg_w9_3 : SS.bdot w9 z3 = true := by decide
theorem sg_w9_4 : SS.bdot w9 z4 = false := by decide
theorem sg_w9_5 : SS.bdot w9 z5 = true := by decide
theorem sg_w9_6 : SS.bdot w9 z6 = false := by decide
theorem sg_w9_7 : SS.bdot w9 z7 = true := by decide
theorem sg_w9_8 : SS.bdot w9 z8 = true := by decide
theorem sg_w9_9 : SS.bdot w9 z9 = false := by decide

/-! ## The moment system -/

structure MomentSystem (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Real) : Prop where
  n0 : q0 + q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 + q9 = 1
  n1 : r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 = 1
  m1 : q4 + q5 + q6 + q7 + q8 + q9 = r4 + r5 + r6 + r7 + r8 + r9
  m2 : q2 + q3 + q8 + q9 = r2 + r3 + r8 + r9
  m3 : q2 + q3 + q6 + q7 = r2 + r3 + r6 + r7
  m4 : q2 + q3 + q4 + q5 = r2 + r3 + r4 + r5
  m5 : q1 + q3 + q5 + q7 + q9 = r1 + r3 + r5 + r7 + r9
  m6 : q1 + q3 + q4 + q6 + q8 = r0 + r2 + r5 + r7 + r9
  m12 : q8 + q9 = r8 + r9
  m13 : q6 + q7 = r6 + r7
  m14 : q4 + q5 = r4 + r5
  m15 : q5 + q7 + q9 = r5 + r7 + r9
  m16 : q4 + q6 + q8 = r5 + r7 + r9
  m23 : q2 + q3 = r2 + r3
  m24 : q2 + q3 = r2 + r3
  m25 : q3 + q9 = r3 + r9
  m26 : q3 + q8 = r2 + r9
  m34 : q2 + q3 = r2 + r3
  m35 : q3 + q7 = r3 + r7
  m36 : q3 + q6 = r2 + r7
  m45 : q3 + q5 = r3 + r5
  m46 : q3 + q4 = r2 + r5
  m56 : q1 + q3 = r5 + r7 + r9

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

/-- Endpoint ratio at incidence 0. -/
theorem MomentSystem.ratio0 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) :
    q0 = (1) * r0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, m12, m13, m14, m15, m16, m23, m24, m25, m26, m34, m35, m36, m45, m46, m56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9⟩ := h
  linarith

/-- Endpoint ratio at incidence 1. -/
theorem MomentSystem.ratio1 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) :
    q1 = (1) * r1 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, m12, m13, m14, m15, m16, m23, m24, m25, m26, m34, m35, m36, m45, m46, m56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9⟩ := h
  linarith

/-- Endpoint ratio at incidence 2. -/
theorem MomentSystem.ratio2 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) :
    q2 = (1) * r2 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, m12, m13, m14, m15, m16, m23, m24, m25, m26, m34, m35, m36, m45, m46, m56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9⟩ := h
  linarith

/-- Endpoint ratio at incidence 3. -/
theorem MomentSystem.ratio3 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) :
    q3 = (1) * r3 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, m12, m13, m14, m15, m16, m23, m24, m25, m26, m34, m35, m36, m45, m46, m56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9⟩ := h
  linarith

/-- Endpoint ratio at incidence 4. -/
theorem MomentSystem.ratio4 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) :
    q4 = (1) * r4 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, m12, m13, m14, m15, m16, m23, m24, m25, m26, m34, m35, m36, m45, m46, m56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9⟩ := h
  linarith

/-- Endpoint ratio at incidence 5. -/
theorem MomentSystem.ratio5 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) :
    q5 = (1) * r5 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, m12, m13, m14, m15, m16, m23, m24, m25, m26, m34, m35, m36, m45, m46, m56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9⟩ := h
  linarith

/-- Endpoint ratio at incidence 6. -/
theorem MomentSystem.ratio6 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) :
    q6 = (1) * r6 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, m12, m13, m14, m15, m16, m23, m24, m25, m26, m34, m35, m36, m45, m46, m56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9⟩ := h
  linarith

/-- Endpoint ratio at incidence 7. -/
theorem MomentSystem.ratio7 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) :
    q7 = (1) * r7 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, m12, m13, m14, m15, m16, m23, m24, m25, m26, m34, m35, m36, m45, m46, m56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9⟩ := h
  linarith

/-- Endpoint ratio at incidence 8. -/
theorem MomentSystem.ratio8 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) :
    q8 = (1) * r8 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, m12, m13, m14, m15, m16, m23, m24, m25, m26, m34, m35, m36, m45, m46, m56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9⟩ := h
  linarith

/-- Endpoint ratio at incidence 9. -/
theorem MomentSystem.ratio9 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) :
    q9 = (1) * r9 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, m12, m13, m14, m15, m16, m23, m24, m25, m26, m34, m35, m36, m45, m46, m56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9⟩ := h
  linarith

/-- Every isolated bottom probability vanishing is impossible. -/
theorem MomentSystem.absurd_zero {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9)
    (v0 : q0 = 0)
    (v1 : q1 = 0)
    (v2 : q2 = 0)
    (v3 : q3 = 0)
    (v4 : q4 = 0)
    (v5 : q5 = 0)
    (v6 : q6 = 0)
    (v7 : q7 = 0)
    (v8 : q8 = 0)
    (v9 : q9 = 0)
    : False := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, m12, m13, m14, m15, m16, m23, m24, m25, m26, m34, m35, m36, m45, m46, m56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9⟩ := h
  linarith

/-! ## The Walsh expansions -/

def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),
      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

theorem ex_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef w0 = star (c y0) * d z0 + star (c y1) * d z1 + star (c y2) * d z2 + star (c y3) * d z3 + star (c y4) * d z4 + star (c y5) * d z5 + star (c y6) * d z6 + star (c y7) * d z7 + star (c y8) * d z8 + star (c y9) * d z9 := by
  unfold offSum
  rw [incidence]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_z0, flip_z1, flip_z2, flip_z3, flip_z4, flip_z5, flip_z6, flip_z7, flip_z8, flip_z9]
  simp only [sg_w0_0, sg_w0_1, sg_w0_2, sg_w0_3, sg_w0_4, sg_w0_5, sg_w0_6, sg_w0_7, sg_w0_8, sg_w0_9, SixQubit.signMul_false]
  try ring

theorem ex_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef w1 = - star (c y0) * d z0 + star (c y1) * d z1 - star (c y2) * d z2 + star (c y3) * d z3 + star (c y4) * d z4 - star (c y5) * d z5 + star (c y6) * d z6 - star (c y7) * d z7 + star (c y8) * d z8 - star (c y9) * d z9 := by
  unfold offSum
  rw [incidence]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_z0, flip_z1, flip_z2, flip_z3, flip_z4, flip_z5, flip_z6, flip_z7, flip_z8, flip_z9]
  simp only [sg_w1_0, sg_w1_1, sg_w1_2, sg_w1_3, sg_w1_4, sg_w1_5, sg_w1_6, sg_w1_7, sg_w1_8, sg_w1_9, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef w2 = star (c y0) * d z0 - star (c y1) * d z1 + star (c y2) * d z2 - star (c y3) * d z3 + star (c y4) * d z4 - star (c y5) * d z5 + star (c y6) * d z6 - star (c y7) * d z7 + star (c y8) * d z8 - star (c y9) * d z9 := by
  unfold offSum
  rw [incidence]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_z0, flip_z1, flip_z2, flip_z3, flip_z4, flip_z5, flip_z6, flip_z7, flip_z8, flip_z9]
  simp only [sg_w2_0, sg_w2_1, sg_w2_2, sg_w2_3, sg_w2_4, sg_w2_5, sg_w2_6, sg_w2_7, sg_w2_8, sg_w2_9, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef w3 = - star (c y0) * d z0 - star (c y1) * d z1 - star (c y2) * d z2 - star (c y3) * d z3 + star (c y4) * d z4 + star (c y5) * d z5 + star (c y6) * d z6 + star (c y7) * d z7 + star (c y8) * d z8 + star (c y9) * d z9 := by
  unfold offSum
  rw [incidence]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_z0, flip_z1, flip_z2, flip_z3, flip_z4, flip_z5, flip_z6, flip_z7, flip_z8, flip_z9]
  simp only [sg_w3_0, sg_w3_1, sg_w3_2, sg_w3_3, sg_w3_4, sg_w3_5, sg_w3_6, sg_w3_7, sg_w3_8, sg_w3_9, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef w4 = star (c y0) * d z0 + star (c y1) * d z1 - star (c y2) * d z2 - star (c y3) * d z3 - star (c y4) * d z4 - star (c y5) * d z5 + star (c y6) * d z6 + star (c y7) * d z7 + star (c y8) * d z8 + star (c y9) * d z9 := by
  unfold offSum
  rw [incidence]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_z0, flip_z1, flip_z2, flip_z3, flip_z4, flip_z5, flip_z6, flip_z7, flip_z8, flip_z9]
  simp only [sg_w4_0, sg_w4_1, sg_w4_2, sg_w4_3, sg_w4_4, sg_w4_5, sg_w4_6, sg_w4_7, sg_w4_8, sg_w4_9, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_w5 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef w5 = - star (c y0) * d z0 + star (c y1) * d z1 + star (c y2) * d z2 - star (c y3) * d z3 - star (c y4) * d z4 + star (c y5) * d z5 + star (c y6) * d z6 - star (c y7) * d z7 + star (c y8) * d z8 - star (c y9) * d z9 := by
  unfold offSum
  rw [incidence]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_z0, flip_z1, flip_z2, flip_z3, flip_z4, flip_z5, flip_z6, flip_z7, flip_z8, flip_z9]
  simp only [sg_w5_0, sg_w5_1, sg_w5_2, sg_w5_3, sg_w5_4, sg_w5_5, sg_w5_6, sg_w5_7, sg_w5_8, sg_w5_9, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef w6 = star (c y0) * d z0 + star (c y1) * d z1 - star (c y2) * d z2 - star (c y3) * d z3 + star (c y4) * d z4 + star (c y5) * d z5 - star (c y6) * d z6 - star (c y7) * d z7 + star (c y8) * d z8 + star (c y9) * d z9 := by
  unfold offSum
  rw [incidence]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_z0, flip_z1, flip_z2, flip_z3, flip_z4, flip_z5, flip_z6, flip_z7, flip_z8, flip_z9]
  simp only [sg_w6_0, sg_w6_1, sg_w6_2, sg_w6_3, sg_w6_4, sg_w6_5, sg_w6_6, sg_w6_7, sg_w6_8, sg_w6_9, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_w7 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef w7 = - star (c y0) * d z0 + star (c y1) * d z1 + star (c y2) * d z2 - star (c y3) * d z3 + star (c y4) * d z4 - star (c y5) * d z5 - star (c y6) * d z6 + star (c y7) * d z7 + star (c y8) * d z8 - star (c y9) * d z9 := by
  unfold offSum
  rw [incidence]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_z0, flip_z1, flip_z2, flip_z3, flip_z4, flip_z5, flip_z6, flip_z7, flip_z8, flip_z9]
  simp only [sg_w7_0, sg_w7_1, sg_w7_2, sg_w7_3, sg_w7_4, sg_w7_5, sg_w7_6, sg_w7_7, sg_w7_8, sg_w7_9, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_w8 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef w8 = star (c y0) * d z0 + star (c y1) * d z1 - star (c y2) * d z2 - star (c y3) * d z3 + star (c y4) * d z4 + star (c y5) * d z5 + star (c y6) * d z6 + star (c y7) * d z7 - star (c y8) * d z8 - star (c y9) * d z9 := by
  unfold offSum
  rw [incidence]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_z0, flip_z1, flip_z2, flip_z3, flip_z4, flip_z5, flip_z6, flip_z7, flip_z8, flip_z9]
  simp only [sg_w8_0, sg_w8_1, sg_w8_2, sg_w8_3, sg_w8_4, sg_w8_5, sg_w8_6, sg_w8_7, sg_w8_8, sg_w8_9, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_w9 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef w9 = - star (c y0) * d z0 + star (c y1) * d z1 + star (c y2) * d z2 - star (c y3) * d z3 + star (c y4) * d z4 - star (c y5) * d z5 + star (c y6) * d z6 - star (c y7) * d z7 - star (c y8) * d z8 + star (c y9) * d z9 := by
  unfold offSum
  rw [incidence]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_z0, flip_z1, flip_z2, flip_z3, flip_z4, flip_z5, flip_z6, flip_z7, flip_z8, flip_z9]
  simp only [sg_w9_0, sg_w9_1, sg_w9_2, sg_w9_3, sg_w9_4, sg_w9_5, sg_w9_6, sg_w9_7, sg_w9_8, sg_w9_9, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

/-! ## The no-go -/

/-- **Orbit 46 is impossible.** -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)))
    (h0 : offSum c d ef w0 = 0)
    (h1 : offSum c d ef w1 = 0)
    (h2 : offSum c d ef w2 = 0)
    (h3 : offSum c d ef w3 = 0)
    (h4 : offSum c d ef w4 = 0)
    (h5 : offSum c d ef w5 = 0)
    (h6 : offSum c d ef w6 = 0)
    (h7 : offSum c d ef w7 = 0)
    (h8 : offSum c d ef w8 = 0)
    (h9 : offSum c d ef w9 = 0)
    : False := by
  rw [ex_w0] at h0
  rw [ex_w1] at h1
  rw [ex_w2] at h2
  rw [ex_w3] at h3
  rw [ex_w4] at h4
  rw [ex_w5] at h5
  rw [ex_w6] at h6
  rw [ex_w7] at h7
  rw [ex_w8] at h8
  rw [ex_w9] at h9
  have key0 : star (c y0) * d z0 = 0 := by
    linear_combination (1/12 : ℂ) * h0 + (-1/12 : ℂ) * h1 + (1/6 : ℂ) * h2 + (-1/6 : ℂ) * h3 + (1/12 : ℂ) * h4 + (-1/12 : ℂ) * h5 + (1/12 : ℂ) * h6 + (-1/12 : ℂ) * h7 + (1/12 : ℂ) * h8 + (-1/12 : ℂ) * h9
  have rat0 := hm.ratio0
  have van0 : Complex.normSq (c y0) = 0 := by
    rcases mul_eq_zero.mp key0 with hh | hh
    · have : c y0 = 0 := by simpa using congrArg star hh
      simp [this]
    · have hz : Complex.normSq (d z0) = 0 := by simp [hh]
      rw [rat0, hz]; ring
  have key1 : star (c y1) * d z1 = 0 := by
    linear_combination (1/12 : ℂ) * h0 + (1/12 : ℂ) * h1 + (-1/6 : ℂ) * h2 + (-1/6 : ℂ) * h3 + (1/12 : ℂ) * h4 + (1/12 : ℂ) * h5 + (1/12 : ℂ) * h6 + (1/12 : ℂ) * h7 + (1/12 : ℂ) * h8 + (1/12 : ℂ) * h9
  have rat1 := hm.ratio1
  have van1 : Complex.normSq (c y1) = 0 := by
    rcases mul_eq_zero.mp key1 with hh | hh
    · have : c y1 = 0 := by simpa using congrArg star hh
      simp [this]
    · have hz : Complex.normSq (d z1) = 0 := by simp [hh]
      rw [rat1, hz]; ring
  have key2 : star (c y2) * d z2 = 0 := by
    linear_combination (1/6 : ℂ) * h0 + (-1/6 : ℂ) * h1 + (1/12 : ℂ) * h2 + (-1/12 : ℂ) * h3 + (-1/12 : ℂ) * h4 + (1/12 : ℂ) * h5 + (-1/12 : ℂ) * h6 + (1/12 : ℂ) * h7 + (-1/12 : ℂ) * h8 + (1/12 : ℂ) * h9
  have rat2 := hm.ratio2
  have van2 : Complex.normSq (c y2) = 0 := by
    rcases mul_eq_zero.mp key2 with hh | hh
    · have : c y2 = 0 := by simpa using congrArg star hh
      simp [this]
    · have hz : Complex.normSq (d z2) = 0 := by simp [hh]
      rw [rat2, hz]; ring
  have key3 : star (c y3) * d z3 = 0 := by
    linear_combination (1/6 : ℂ) * h0 + (1/6 : ℂ) * h1 + (-1/12 : ℂ) * h2 + (-1/12 : ℂ) * h3 + (-1/12 : ℂ) * h4 + (-1/12 : ℂ) * h5 + (-1/12 : ℂ) * h6 + (-1/12 : ℂ) * h7 + (-1/12 : ℂ) * h8 + (-1/12 : ℂ) * h9
  have rat3 := hm.ratio3
  have van3 : Complex.normSq (c y3) = 0 := by
    rcases mul_eq_zero.mp key3 with hh | hh
    · have : c y3 = 0 := by simpa using congrArg star hh
      simp [this]
    · have hz : Complex.normSq (d z3) = 0 := by simp [hh]
      rw [rat3, hz]; ring
  have key4 : star (c y4) * d z4 = 0 := by
    linear_combination (1/12 : ℂ) * h0 + (1/12 : ℂ) * h1 + (1/12 : ℂ) * h2 + (1/12 : ℂ) * h3 + (-1/6 : ℂ) * h4 + (-1/6 : ℂ) * h5 + (1/12 : ℂ) * h6 + (1/12 : ℂ) * h7 + (1/12 : ℂ) * h8 + (1/12 : ℂ) * h9
  have rat4 := hm.ratio4
  have van4 : Complex.normSq (c y4) = 0 := by
    rcases mul_eq_zero.mp key4 with hh | hh
    · have : c y4 = 0 := by simpa using congrArg star hh
      simp [this]
    · have hz : Complex.normSq (d z4) = 0 := by simp [hh]
      rw [rat4, hz]; ring
  have key5 : star (c y5) * d z5 = 0 := by
    linear_combination (1/12 : ℂ) * h0 + (-1/12 : ℂ) * h1 + (-1/12 : ℂ) * h2 + (1/12 : ℂ) * h3 + (-1/6 : ℂ) * h4 + (1/6 : ℂ) * h5 + (1/12 : ℂ) * h6 + (-1/12 : ℂ) * h7 + (1/12 : ℂ) * h8 + (-1/12 : ℂ) * h9
  have rat5 := hm.ratio5
  have van5 : Complex.normSq (c y5) = 0 := by
    rcases mul_eq_zero.mp key5 with hh | hh
    · have : c y5 = 0 := by simpa using congrArg star hh
      simp [this]
    · have hz : Complex.normSq (d z5) = 0 := by simp [hh]
      rw [rat5, hz]; ring
  have key6 : star (c y6) * d z6 = 0 := by
    linear_combination (1/12 : ℂ) * h0 + (1/12 : ℂ) * h1 + (1/12 : ℂ) * h2 + (1/12 : ℂ) * h3 + (1/12 : ℂ) * h4 + (1/12 : ℂ) * h5 + (-1/6 : ℂ) * h6 + (-1/6 : ℂ) * h7 + (1/12 : ℂ) * h8 + (1/12 : ℂ) * h9
  have rat6 := hm.ratio6
  have van6 : Complex.normSq (c y6) = 0 := by
    rcases mul_eq_zero.mp key6 with hh | hh
    · have : c y6 = 0 := by simpa using congrArg star hh
      simp [this]
    · have hz : Complex.normSq (d z6) = 0 := by simp [hh]
      rw [rat6, hz]; ring
  have key7 : star (c y7) * d z7 = 0 := by
    linear_combination (1/12 : ℂ) * h0 + (-1/12 : ℂ) * h1 + (-1/12 : ℂ) * h2 + (1/12 : ℂ) * h3 + (1/12 : ℂ) * h4 + (-1/12 : ℂ) * h5 + (-1/6 : ℂ) * h6 + (1/6 : ℂ) * h7 + (1/12 : ℂ) * h8 + (-1/12 : ℂ) * h9
  have rat7 := hm.ratio7
  have van7 : Complex.normSq (c y7) = 0 := by
    rcases mul_eq_zero.mp key7 with hh | hh
    · have : c y7 = 0 := by simpa using congrArg star hh
      simp [this]
    · have hz : Complex.normSq (d z7) = 0 := by simp [hh]
      rw [rat7, hz]; ring
  have key8 : star (c y8) * d z8 = 0 := by
    linear_combination (1/12 : ℂ) * h0 + (1/12 : ℂ) * h1 + (1/12 : ℂ) * h2 + (1/12 : ℂ) * h3 + (1/12 : ℂ) * h4 + (1/12 : ℂ) * h5 + (1/12 : ℂ) * h6 + (1/12 : ℂ) * h7 + (-1/6 : ℂ) * h8 + (-1/6 : ℂ) * h9
  have rat8 := hm.ratio8
  have van8 : Complex.normSq (c y8) = 0 := by
    rcases mul_eq_zero.mp key8 with hh | hh
    · have : c y8 = 0 := by simpa using congrArg star hh
      simp [this]
    · have hz : Complex.normSq (d z8) = 0 := by simp [hh]
      rw [rat8, hz]; ring
  have key9 : star (c y9) * d z9 = 0 := by
    linear_combination (1/12 : ℂ) * h0 + (-1/12 : ℂ) * h1 + (-1/12 : ℂ) * h2 + (1/12 : ℂ) * h3 + (1/12 : ℂ) * h4 + (-1/12 : ℂ) * h5 + (1/12 : ℂ) * h6 + (-1/12 : ℂ) * h7 + (-1/6 : ℂ) * h8 + (1/6 : ℂ) * h9
  have rat9 := hm.ratio9
  have van9 : Complex.normSq (c y9) = 0 := by
    rcases mul_eq_zero.mp key9 with hh | hh
    · have : c y9 = 0 := by simpa using congrArg star hh
      simp [this]
    · have hz : Complex.normSq (d z9) = 0 := by simp [hh]
      rw [rat9, hz]; ring
  exact hm.absurd_zero van0 van1 van2 van3 van4 van5 van6 van7 van8 van9

end

end SixQubit.Orbit46
