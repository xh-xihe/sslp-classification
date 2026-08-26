import Mathlib

import SS.FullKL
import SixQubit.Common

/-!
# Six-qubit no-go for moment orbit 18

Orbit 18 of `six_qubit_sslp.tex`: q = 4, angle vector
a = (1, 1, 1, 1, 1, 2), residues 0 and 2.

The flip mask 000001 has 16 incidences on the two fibers.  A rational
combination of 7 admissible dressings isolates the single monomial
at (000000, 000001), while the moment polytope pins its two endpoint
probabilities to 1/4 and 1/4.  Both are positive, so the isolated
monomial cannot vanish.

Everything computational is decided by the Lean kernel; `native_decide`
is not used.
-/

namespace SixQubit.Orbit18

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
def y8 : SS.BitString 6 := bs true  false false false true  true   -- 100011
def y9 : SS.BitString 6 := bs true  false false true  false true   -- 100101
def y10 : SS.BitString 6 := bs true  false true  false false true   -- 101001
def y11 : SS.BitString 6 := bs true  false true  true  true  false  -- 101110
def y12 : SS.BitString 6 := bs true  true  false false false true   -- 110001
def y13 : SS.BitString 6 := bs true  true  false true  true  false  -- 110110
def y14 : SS.BitString 6 := bs true  true  true  false true  false  -- 111010
def y15 : SS.BitString 6 := bs true  true  true  true  false false  -- 111100

def z0 : SS.BitString 6 := bs false false false false false true   -- 000001
def z1 : SS.BitString 6 := bs false false false true  true  false  -- 000110
def z2 : SS.BitString 6 := bs false false true  false true  false  -- 001010
def z3 : SS.BitString 6 := bs false false true  true  false false  -- 001100
def z4 : SS.BitString 6 := bs false true  false false true  false  -- 010010
def z5 : SS.BitString 6 := bs false true  false true  false false  -- 010100
def z6 : SS.BitString 6 := bs false true  true  false false false  -- 011000
def z7 : SS.BitString 6 := bs false true  true  true  true  true   -- 011111
def z8 : SS.BitString 6 := bs true  false false false true  false  -- 100010
def z9 : SS.BitString 6 := bs true  false false true  false false  -- 100100
def z10 : SS.BitString 6 := bs true  false true  false false false  -- 101000
def z11 : SS.BitString 6 := bs true  false true  true  true  true   -- 101111
def z12 : SS.BitString 6 := bs true  true  false false false false  -- 110000
def z13 : SS.BitString 6 := bs true  true  false true  true  true   -- 110111
def z14 : SS.BitString 6 := bs true  true  true  false true  true   -- 111011
def z15 : SS.BitString 6 := bs true  true  true  true  false true   -- 111101

def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15}
def S1 : Finset (SS.BitString 6) := {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15}

def av : Fin 6 -> ZMod 4 := ![1, 1, 1, 1, 1, 2]

theorem S0_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 0) = S0 := by
  decide

theorem S1_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 2) = S1 := by
  decide

/-! ## The flip mask and its incidences -/

def ef : SS.BitString 6 := bs false false false false false true   -- 000001

theorem incidence :
    S1.filter (fun y => SS.bxor y ef ∈ S0) = {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15} := by decide

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
theorem flip_z10 : SS.bxor z10 ef = y10 := by decide
theorem flip_z11 : SS.bxor z11 ef = y11 := by decide
theorem flip_z12 : SS.bxor z12 ef = y12 := by decide
theorem flip_z13 : SS.bxor z13 ef = y13 := by decide
theorem flip_z14 : SS.bxor z14 ef = y14 := by decide
theorem flip_z15 : SS.bxor z15 ef = y15 := by decide

def w0 : SS.BitString 6 := bs false false false false false false  -- 000000
def w1 : SS.BitString 6 := bs false false false false false true   -- 000001
def w2 : SS.BitString 6 := bs false false false false true  false  -- 000010
def w3 : SS.BitString 6 := bs false false false true  false false  -- 000100
def w4 : SS.BitString 6 := bs false false true  false false false  -- 001000
def w5 : SS.BitString 6 := bs false true  false false false false  -- 010000
def w6 : SS.BitString 6 := bs true  false false false false false  -- 100000
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
theorem sg_w1_3 : SS.bdot w1 z3 = false := by decide
theorem sg_w1_4 : SS.bdot w1 z4 = false := by decide
theorem sg_w1_5 : SS.bdot w1 z5 = false := by decide
theorem sg_w1_6 : SS.bdot w1 z6 = false := by decide
theorem sg_w1_7 : SS.bdot w1 z7 = true := by decide
theorem sg_w1_8 : SS.bdot w1 z8 = false := by decide
theorem sg_w1_9 : SS.bdot w1 z9 = false := by decide
theorem sg_w1_10 : SS.bdot w1 z10 = false := by decide
theorem sg_w1_11 : SS.bdot w1 z11 = true := by decide
theorem sg_w1_12 : SS.bdot w1 z12 = false := by decide
theorem sg_w1_13 : SS.bdot w1 z13 = true := by decide
theorem sg_w1_14 : SS.bdot w1 z14 = true := by decide
theorem sg_w1_15 : SS.bdot w1 z15 = true := by decide
theorem sg_w2_0 : SS.bdot w2 z0 = false := by decide
theorem sg_w2_1 : SS.bdot w2 z1 = true := by decide
theorem sg_w2_2 : SS.bdot w2 z2 = true := by decide
theorem sg_w2_3 : SS.bdot w2 z3 = false := by decide
theorem sg_w2_4 : SS.bdot w2 z4 = true := by decide
theorem sg_w2_5 : SS.bdot w2 z5 = false := by decide
theorem sg_w2_6 : SS.bdot w2 z6 = false := by decide
theorem sg_w2_7 : SS.bdot w2 z7 = true := by decide
theorem sg_w2_8 : SS.bdot w2 z8 = true := by decide
theorem sg_w2_9 : SS.bdot w2 z9 = false := by decide
theorem sg_w2_10 : SS.bdot w2 z10 = false := by decide
theorem sg_w2_11 : SS.bdot w2 z11 = true := by decide
theorem sg_w2_12 : SS.bdot w2 z12 = false := by decide
theorem sg_w2_13 : SS.bdot w2 z13 = true := by decide
theorem sg_w2_14 : SS.bdot w2 z14 = true := by decide
theorem sg_w2_15 : SS.bdot w2 z15 = false := by decide
theorem sg_w3_0 : SS.bdot w3 z0 = false := by decide
theorem sg_w3_1 : SS.bdot w3 z1 = true := by decide
theorem sg_w3_2 : SS.bdot w3 z2 = false := by decide
theorem sg_w3_3 : SS.bdot w3 z3 = true := by decide
theorem sg_w3_4 : SS.bdot w3 z4 = false := by decide
theorem sg_w3_5 : SS.bdot w3 z5 = true := by decide
theorem sg_w3_6 : SS.bdot w3 z6 = false := by decide
theorem sg_w3_7 : SS.bdot w3 z7 = true := by decide
theorem sg_w3_8 : SS.bdot w3 z8 = false := by decide
theorem sg_w3_9 : SS.bdot w3 z9 = true := by decide
theorem sg_w3_10 : SS.bdot w3 z10 = false := by decide
theorem sg_w3_11 : SS.bdot w3 z11 = true := by decide
theorem sg_w3_12 : SS.bdot w3 z12 = false := by decide
theorem sg_w3_13 : SS.bdot w3 z13 = true := by decide
theorem sg_w3_14 : SS.bdot w3 z14 = false := by decide
theorem sg_w3_15 : SS.bdot w3 z15 = true := by decide
theorem sg_w4_0 : SS.bdot w4 z0 = false := by decide
theorem sg_w4_1 : SS.bdot w4 z1 = false := by decide
theorem sg_w4_2 : SS.bdot w4 z2 = true := by decide
theorem sg_w4_3 : SS.bdot w4 z3 = true := by decide
theorem sg_w4_4 : SS.bdot w4 z4 = false := by decide
theorem sg_w4_5 : SS.bdot w4 z5 = false := by decide
theorem sg_w4_6 : SS.bdot w4 z6 = true := by decide
theorem sg_w4_7 : SS.bdot w4 z7 = true := by decide
theorem sg_w4_8 : SS.bdot w4 z8 = false := by decide
theorem sg_w4_9 : SS.bdot w4 z9 = false := by decide
theorem sg_w4_10 : SS.bdot w4 z10 = true := by decide
theorem sg_w4_11 : SS.bdot w4 z11 = true := by decide
theorem sg_w4_12 : SS.bdot w4 z12 = false := by decide
theorem sg_w4_13 : SS.bdot w4 z13 = false := by decide
theorem sg_w4_14 : SS.bdot w4 z14 = true := by decide
theorem sg_w4_15 : SS.bdot w4 z15 = true := by decide
theorem sg_w5_0 : SS.bdot w5 z0 = false := by decide
theorem sg_w5_1 : SS.bdot w5 z1 = false := by decide
theorem sg_w5_2 : SS.bdot w5 z2 = false := by decide
theorem sg_w5_3 : SS.bdot w5 z3 = false := by decide
theorem sg_w5_4 : SS.bdot w5 z4 = true := by decide
theorem sg_w5_5 : SS.bdot w5 z5 = true := by decide
theorem sg_w5_6 : SS.bdot w5 z6 = true := by decide
theorem sg_w5_7 : SS.bdot w5 z7 = true := by decide
theorem sg_w5_8 : SS.bdot w5 z8 = false := by decide
theorem sg_w5_9 : SS.bdot w5 z9 = false := by decide
theorem sg_w5_10 : SS.bdot w5 z10 = false := by decide
theorem sg_w5_11 : SS.bdot w5 z11 = false := by decide
theorem sg_w5_12 : SS.bdot w5 z12 = true := by decide
theorem sg_w5_13 : SS.bdot w5 z13 = true := by decide
theorem sg_w5_14 : SS.bdot w5 z14 = true := by decide
theorem sg_w5_15 : SS.bdot w5 z15 = true := by decide
theorem sg_w6_0 : SS.bdot w6 z0 = false := by decide
theorem sg_w6_1 : SS.bdot w6 z1 = false := by decide
theorem sg_w6_2 : SS.bdot w6 z2 = false := by decide
theorem sg_w6_3 : SS.bdot w6 z3 = false := by decide
theorem sg_w6_4 : SS.bdot w6 z4 = false := by decide
theorem sg_w6_5 : SS.bdot w6 z5 = false := by decide
theorem sg_w6_6 : SS.bdot w6 z6 = false := by decide
theorem sg_w6_7 : SS.bdot w6 z7 = false := by decide
theorem sg_w6_8 : SS.bdot w6 z8 = true := by decide
theorem sg_w6_9 : SS.bdot w6 z9 = true := by decide
theorem sg_w6_10 : SS.bdot w6 z10 = true := by decide
theorem sg_w6_11 : SS.bdot w6 z11 = true := by decide
theorem sg_w6_12 : SS.bdot w6 z12 = true := by decide
theorem sg_w6_13 : SS.bdot w6 z13 = true := by decide
theorem sg_w6_14 : SS.bdot w6 z14 = true := by decide
theorem sg_w6_15 : SS.bdot w6 z15 = true := by decide

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
  m5 : q1 + q2 + q4 + q7 + q8 + q11 + q13 + q14 = r1 + r2 + r4 + r7 + r8 + r11 + r13 + r14
  m6 : q1 + q2 + q3 + q4 + q5 + q6 + q8 + q9 + q10 + q12 = r0 + r7 + r11 + r13 + r14 + r15
  m12 : q12 + q13 + q14 + q15 = r12 + r13 + r14 + r15
  m13 : q10 + q11 + q14 + q15 = r10 + r11 + r14 + r15
  m14 : q9 + q11 + q13 + q15 = r9 + r11 + r13 + r15
  m15 : q8 + q11 + q13 + q14 = r8 + r11 + r13 + r14
  m16 : q8 + q9 + q10 + q12 = r11 + r13 + r14 + r15
  m23 : q6 + q7 + q14 + q15 = r6 + r7 + r14 + r15
  m24 : q5 + q7 + q13 + q15 = r5 + r7 + r13 + r15
  m25 : q4 + q7 + q13 + q14 = r4 + r7 + r13 + r14
  m26 : q4 + q5 + q6 + q12 = r7 + r13 + r14 + r15
  m34 : q3 + q7 + q11 + q15 = r3 + r7 + r11 + r15
  m35 : q2 + q7 + q11 + q14 = r2 + r7 + r11 + r14
  m36 : q2 + q3 + q6 + q10 = r7 + r11 + r14 + r15
  m45 : q1 + q7 + q11 + q13 = r1 + r7 + r11 + r13
  m46 : q1 + q3 + q5 + q9 = r7 + r11 + r13 + r15
  m56 : q1 + q2 + q4 + q8 = r7 + r11 + r13 + r14

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

/-- The two endpoint probabilities of the isolated incidence are forced. -/
theorem MomentSystem.endpoints {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real}
    (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    q0 = 1/4 ∧ r0 = 1/4 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, m12, m13, m14, m15, m16, m23, m24, m25, m26, m34, m35, m36, m45, m46, m56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  refine ⟨?_, ?_⟩ <;> linarith

/-! ## The Walsh expansions -/

def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),
      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

theorem ex_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef w0 = star (c y0) * d z0 + star (c y1) * d z1 + star (c y2) * d z2 + star (c y3) * d z3 + star (c y4) * d z4 + star (c y5) * d z5 + star (c y6) * d z6 + star (c y7) * d z7 + star (c y8) * d z8 + star (c y9) * d z9 + star (c y10) * d z10 + star (c y11) * d z11 + star (c y12) * d z12 + star (c y13) * d z13 + star (c y14) * d z14 + star (c y15) * d z15 := by
  unfold offSum
  rw [incidence]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_z0, flip_z1, flip_z2, flip_z3, flip_z4, flip_z5, flip_z6, flip_z7, flip_z8, flip_z9, flip_z10, flip_z11, flip_z12, flip_z13, flip_z14, flip_z15]
  simp only [sg_w0_0, sg_w0_1, sg_w0_2, sg_w0_3, sg_w0_4, sg_w0_5, sg_w0_6, sg_w0_7, sg_w0_8, sg_w0_9, sg_w0_10, sg_w0_11, sg_w0_12, sg_w0_13, sg_w0_14, sg_w0_15, SixQubit.signMul_false]
  try ring

theorem ex_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef w1 = - star (c y0) * d z0 + star (c y1) * d z1 + star (c y2) * d z2 + star (c y3) * d z3 + star (c y4) * d z4 + star (c y5) * d z5 + star (c y6) * d z6 - star (c y7) * d z7 + star (c y8) * d z8 + star (c y9) * d z9 + star (c y10) * d z10 - star (c y11) * d z11 + star (c y12) * d z12 - star (c y13) * d z13 - star (c y14) * d z14 - star (c y15) * d z15 := by
  unfold offSum
  rw [incidence]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_z0, flip_z1, flip_z2, flip_z3, flip_z4, flip_z5, flip_z6, flip_z7, flip_z8, flip_z9, flip_z10, flip_z11, flip_z12, flip_z13, flip_z14, flip_z15]
  simp only [sg_w1_0, sg_w1_1, sg_w1_2, sg_w1_3, sg_w1_4, sg_w1_5, sg_w1_6, sg_w1_7, sg_w1_8, sg_w1_9, sg_w1_10, sg_w1_11, sg_w1_12, sg_w1_13, sg_w1_14, sg_w1_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef w2 = star (c y0) * d z0 - star (c y1) * d z1 - star (c y2) * d z2 + star (c y3) * d z3 - star (c y4) * d z4 + star (c y5) * d z5 + star (c y6) * d z6 - star (c y7) * d z7 - star (c y8) * d z8 + star (c y9) * d z9 + star (c y10) * d z10 - star (c y11) * d z11 + star (c y12) * d z12 - star (c y13) * d z13 - star (c y14) * d z14 + star (c y15) * d z15 := by
  unfold offSum
  rw [incidence]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_z0, flip_z1, flip_z2, flip_z3, flip_z4, flip_z5, flip_z6, flip_z7, flip_z8, flip_z9, flip_z10, flip_z11, flip_z12, flip_z13, flip_z14, flip_z15]
  simp only [sg_w2_0, sg_w2_1, sg_w2_2, sg_w2_3, sg_w2_4, sg_w2_5, sg_w2_6, sg_w2_7, sg_w2_8, sg_w2_9, sg_w2_10, sg_w2_11, sg_w2_12, sg_w2_13, sg_w2_14, sg_w2_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef w3 = star (c y0) * d z0 - star (c y1) * d z1 + star (c y2) * d z2 - star (c y3) * d z3 + star (c y4) * d z4 - star (c y5) * d z5 + star (c y6) * d z6 - star (c y7) * d z7 + star (c y8) * d z8 - star (c y9) * d z9 + star (c y10) * d z10 - star (c y11) * d z11 + star (c y12) * d z12 - star (c y13) * d z13 + star (c y14) * d z14 - star (c y15) * d z15 := by
  unfold offSum
  rw [incidence]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_z0, flip_z1, flip_z2, flip_z3, flip_z4, flip_z5, flip_z6, flip_z7, flip_z8, flip_z9, flip_z10, flip_z11, flip_z12, flip_z13, flip_z14, flip_z15]
  simp only [sg_w3_0, sg_w3_1, sg_w3_2, sg_w3_3, sg_w3_4, sg_w3_5, sg_w3_6, sg_w3_7, sg_w3_8, sg_w3_9, sg_w3_10, sg_w3_11, sg_w3_12, sg_w3_13, sg_w3_14, sg_w3_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef w4 = star (c y0) * d z0 + star (c y1) * d z1 - star (c y2) * d z2 - star (c y3) * d z3 + star (c y4) * d z4 + star (c y5) * d z5 - star (c y6) * d z6 - star (c y7) * d z7 + star (c y8) * d z8 + star (c y9) * d z9 - star (c y10) * d z10 - star (c y11) * d z11 + star (c y12) * d z12 + star (c y13) * d z13 - star (c y14) * d z14 - star (c y15) * d z15 := by
  unfold offSum
  rw [incidence]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_z0, flip_z1, flip_z2, flip_z3, flip_z4, flip_z5, flip_z6, flip_z7, flip_z8, flip_z9, flip_z10, flip_z11, flip_z12, flip_z13, flip_z14, flip_z15]
  simp only [sg_w4_0, sg_w4_1, sg_w4_2, sg_w4_3, sg_w4_4, sg_w4_5, sg_w4_6, sg_w4_7, sg_w4_8, sg_w4_9, sg_w4_10, sg_w4_11, sg_w4_12, sg_w4_13, sg_w4_14, sg_w4_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_w5 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef w5 = star (c y0) * d z0 + star (c y1) * d z1 + star (c y2) * d z2 + star (c y3) * d z3 - star (c y4) * d z4 - star (c y5) * d z5 - star (c y6) * d z6 - star (c y7) * d z7 + star (c y8) * d z8 + star (c y9) * d z9 + star (c y10) * d z10 + star (c y11) * d z11 - star (c y12) * d z12 - star (c y13) * d z13 - star (c y14) * d z14 - star (c y15) * d z15 := by
  unfold offSum
  rw [incidence]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_z0, flip_z1, flip_z2, flip_z3, flip_z4, flip_z5, flip_z6, flip_z7, flip_z8, flip_z9, flip_z10, flip_z11, flip_z12, flip_z13, flip_z14, flip_z15]
  simp only [sg_w5_0, sg_w5_1, sg_w5_2, sg_w5_3, sg_w5_4, sg_w5_5, sg_w5_6, sg_w5_7, sg_w5_8, sg_w5_9, sg_w5_10, sg_w5_11, sg_w5_12, sg_w5_13, sg_w5_14, sg_w5_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef w6 = star (c y0) * d z0 + star (c y1) * d z1 + star (c y2) * d z2 + star (c y3) * d z3 + star (c y4) * d z4 + star (c y5) * d z5 + star (c y6) * d z6 + star (c y7) * d z7 - star (c y8) * d z8 - star (c y9) * d z9 - star (c y10) * d z10 - star (c y11) * d z11 - star (c y12) * d z12 - star (c y13) * d z13 - star (c y14) * d z14 - star (c y15) * d z15 := by
  unfold offSum
  rw [incidence]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_z0, flip_z1, flip_z2, flip_z3, flip_z4, flip_z5, flip_z6, flip_z7, flip_z8, flip_z9, flip_z10, flip_z11, flip_z12, flip_z13, flip_z14, flip_z15]
  simp only [sg_w6_0, sg_w6_1, sg_w6_2, sg_w6_3, sg_w6_4, sg_w6_5, sg_w6_6, sg_w6_7, sg_w6_8, sg_w6_9, sg_w6_10, sg_w6_11, sg_w6_12, sg_w6_13, sg_w6_14, sg_w6_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

/-! ## The no-go -/

/-- **Orbit 18 is impossible.** -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11)) (Complex.normSq (c y12)) (Complex.normSq (c y13)) (Complex.normSq (c y14)) (Complex.normSq (c y15))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)) (Complex.normSq (d z12)) (Complex.normSq (d z13)) (Complex.normSq (d z14)) (Complex.normSq (d z15)))
    (h0 : offSum c d ef w0 = 0)
    (h1 : offSum c d ef w1 = 0)
    (h2 : offSum c d ef w2 = 0)
    (h3 : offSum c d ef w3 = 0)
    (h4 : offSum c d ef w4 = 0)
    (h5 : offSum c d ef w5 = 0)
    (h6 : offSum c d ef w6 = 0)
    : False := by
  rw [ex_w0] at h0
  rw [ex_w1] at h1
  rw [ex_w2] at h2
  rw [ex_w3] at h3
  rw [ex_w4] at h4
  rw [ex_w5] at h5
  rw [ex_w6] at h6
  have key : star (c y0) * d z0 = 0 := by
    linear_combination (1/8 : ℂ) * h0 + (-1/4 : ℂ) * h1 + (1/8 : ℂ) * h2 + (1/8 : ℂ) * h3 + (1/8 : ℂ) * h4 + (1/8 : ℂ) * h5 + (1/8 : ℂ) * h6
  obtain ⟨hp, hq⟩ := hm.endpoints
  rcases mul_eq_zero.mp key with hh | hh
  · rw [show c y0 = 0 from by simpa using congrArg star hh] at hp
    simp at hp
  · rw [hh] at hq
    simp at hq

end

end SixQubit.Orbit18
