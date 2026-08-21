import Mathlib

import SS.FullKL
import SixQubit.Common
import SixQubit.Table31

/-!
# Six-qubit no-go for moment orbit 31

Orbit 31 of `six_qubit_sslp_v7.tex`: q = 4, angle vector a = (1, 1, 1, 2, 2, 2),
residues 0 and 1, fibers of size sixteen each and complementary.

The last three angles are all `2`, so both fibers are stabilised by the Klein
four-group on those qubits and split into four cosets of four.  The sixteen
positions form a `4 x 4` table; `SixQubit.Table31` carries the algebra.

Everything computational is decided by the Lean kernel; `native_decide` is
not used.
-/

namespace SixQubit.Orbit31

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]

def y0 : SS.BitString 6 := bs false false false false false false  -- 000000 = A0
def y1 : SS.BitString 6 := bs false false false false true  true   -- 000011 = A1
def y2 : SS.BitString 6 := bs false false false true  false true   -- 000101 = A2
def y3 : SS.BitString 6 := bs false false false true  true  false  -- 000110 = A3
def y4 : SS.BitString 6 := bs false true  true  false false true   -- 011001 = B13
def y5 : SS.BitString 6 := bs false true  true  false true  false  -- 011010 = B12
def y6 : SS.BitString 6 := bs false true  true  true  false false  -- 011100 = B11
def y7 : SS.BitString 6 := bs false true  true  true  true  true   -- 011111 = B10
def y8 : SS.BitString 6 := bs true  false true  false false true   -- 101001 = B23
def y9 : SS.BitString 6 := bs true  false true  false true  false  -- 101010 = B22
def y10 : SS.BitString 6 := bs true  false true  true  false false  -- 101100 = B21
def y11 : SS.BitString 6 := bs true  false true  true  true  true   -- 101111 = B20
def y12 : SS.BitString 6 := bs true  true  false false false true   -- 110001 = B33
def y13 : SS.BitString 6 := bs true  true  false false true  false  -- 110010 = B32
def y14 : SS.BitString 6 := bs true  true  false true  false false  -- 110100 = B31
def y15 : SS.BitString 6 := bs true  true  false true  true  true   -- 110111 = B30

def z0 : SS.BitString 6 := bs false false true  false false false  -- 001000
def z1 : SS.BitString 6 := bs false false true  false true  true   -- 001011
def z2 : SS.BitString 6 := bs false false true  true  false true   -- 001101
def z3 : SS.BitString 6 := bs false false true  true  true  false  -- 001110
def z4 : SS.BitString 6 := bs false true  false false false false  -- 010000
def z5 : SS.BitString 6 := bs false true  false false true  true   -- 010011
def z6 : SS.BitString 6 := bs false true  false true  false true   -- 010101
def z7 : SS.BitString 6 := bs false true  false true  true  false  -- 010110
def z8 : SS.BitString 6 := bs true  false false false false false  -- 100000
def z9 : SS.BitString 6 := bs true  false false false true  true   -- 100011
def z10 : SS.BitString 6 := bs true  false false true  false true   -- 100101
def z11 : SS.BitString 6 := bs true  false false true  true  false  -- 100110
def z12 : SS.BitString 6 := bs true  true  true  false false true   -- 111001
def z13 : SS.BitString 6 := bs true  true  true  false true  false  -- 111010
def z14 : SS.BitString 6 := bs true  true  true  true  false false  -- 111100
def z15 : SS.BitString 6 := bs true  true  true  true  true  true   -- 111111

def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15}
def S1 : Finset (SS.BitString 6) := {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15}

def av : Fin 6 -> ZMod 4 := ![1, 1, 1, 2, 2, 2]

/-- Each support is exactly its residue fiber, decided over all 64 strings. -/
theorem S0_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 0) = S0 := by
  decide

theorem S1_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 1) = S1 := by
  decide

/-- The complement map pairs the two fibers. -/
theorem hat0 : SS.bxor y0 (SS.ones 6) = z15 := by decide
theorem hat1 : SS.bxor y1 (SS.ones 6) = z14 := by decide
theorem hat2 : SS.bxor y2 (SS.ones 6) = z13 := by decide
theorem hat3 : SS.bxor y3 (SS.ones 6) = z12 := by decide
theorem hat4 : SS.bxor y4 (SS.ones 6) = z11 := by decide
theorem hat5 : SS.bxor y5 (SS.ones 6) = z10 := by decide
theorem hat6 : SS.bxor y6 (SS.ones 6) = z9 := by decide
theorem hat7 : SS.bxor y7 (SS.ones 6) = z8 := by decide
theorem hat8 : SS.bxor y8 (SS.ones 6) = z7 := by decide
theorem hat9 : SS.bxor y9 (SS.ones 6) = z6 := by decide
theorem hat10 : SS.bxor y10 (SS.ones 6) = z5 := by decide
theorem hat11 : SS.bxor y11 (SS.ones 6) = z4 := by decide
theorem hat12 : SS.bxor y12 (SS.ones 6) = z3 := by decide
theorem hat13 : SS.bxor y13 (SS.ones 6) = z2 := by decide
theorem hat14 : SS.bxor y14 (SS.ones 6) = z1 := by decide
theorem hat15 : SS.bxor y15 (SS.ones 6) = z0 := by decide

/-! ## The moment system -/

structure MomentSystem (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real) : Prop where
  n0 : q0 + q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 + q9 + q10 + q11 + q12 + q13 + q14 + q15 = 1
  n1 : r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15 = 1
  m1 : q8 + q9 + q10 + q11 + q12 + q13 + q14 + q15 = r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15
  m2 : q4 + q5 + q6 + q7 + q12 + q13 + q14 + q15 = r4 + r5 + r6 + r7 + r12 + r13 + r14 + r15
  m3 : q4 + q5 + q6 + q7 + q8 + q9 + q10 + q11 = r0 + r1 + r2 + r3 + r12 + r13 + r14 + r15
  m4 : q2 + q3 + q6 + q7 + q10 + q11 + q14 + q15 = r2 + r3 + r6 + r7 + r10 + r11 + r14 + r15
  m5 : q1 + q3 + q5 + q7 + q9 + q11 + q13 + q15 = r1 + r3 + r5 + r7 + r9 + r11 + r13 + r15
  m6 : q1 + q2 + q4 + q7 + q8 + q11 + q12 + q15 = r1 + r2 + r5 + r6 + r9 + r10 + r12 + r15
  c12 : q12 + q13 + q14 + q15 = r12 + r13 + r14 + r15
  c13 : q8 + q9 + q10 + q11 = r12 + r13 + r14 + r15
  c14 : q10 + q11 + q14 + q15 = r10 + r11 + r14 + r15
  c15 : q9 + q11 + q13 + q15 = r9 + r11 + r13 + r15
  c16 : q8 + q11 + q12 + q15 = r9 + r10 + r12 + r15
  c23 : q4 + q5 + q6 + q7 = r12 + r13 + r14 + r15
  c24 : q6 + q7 + q14 + q15 = r6 + r7 + r14 + r15
  c25 : q5 + q7 + q13 + q15 = r5 + r7 + r13 + r15
  c26 : q4 + q7 + q12 + q15 = r5 + r6 + r12 + r15
  c34 : q6 + q7 + q10 + q11 = r2 + r3 + r14 + r15
  c35 : q5 + q7 + q9 + q11 = r1 + r3 + r13 + r15
  c36 : q4 + q7 + q8 + q11 = r1 + r2 + r12 + r15
  c45 : q3 + q7 + q11 + q15 = r3 + r7 + r11 + r15
  c46 : q2 + q7 + q11 + q15 = r2 + r6 + r10 + r15
  c56 : q1 + q7 + q11 + q15 = r1 + r5 + r9 + r15

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

/-- The top probability at the complement of A0 equals the bottom one. -/
theorem eq0 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    -q0 + r15 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  linear_combination (-1) * n0 + (1) * n1 + (1) * m1 + (1) * m2 + (1) * m3 + (1/4) * m4 + (1/4) * m5 + (1/4) * m6 + (-1/4) * c12 + (-1/4) * c13 + (-1/2) * c14 + (-1/2) * c15 + (-1/2) * c16 + (-1/4) * c23 + (-1/2) * c24 + (-1/2) * c25 + (-1/2) * c26 + (-1/2) * c34 + (-1/2) * c35 + (-1/2) * c36 + (1/2) * c45 + (1/2) * c46 + (1/2) * c56

/-- The top probability at the complement of A1 equals the bottom one. -/
theorem eq1 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    -q1 + r14 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  linear_combination (5/4) * m4 + (-3/4) * m5 + (-3/4) * m6 + (-1/4) * c12 + (-1/4) * c13 + (-1/2) * c14 + (1/2) * c15 + (1/2) * c16 + (-1/4) * c23 + (-1/2) * c24 + (1/2) * c25 + (1/2) * c26 + (-1/2) * c34 + (1/2) * c35 + (1/2) * c36 + (-1/2) * c45 + (-1/2) * c46 + (1/2) * c56

/-- The top probability at the complement of A2 equals the bottom one. -/
theorem eq2 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    -q2 + r13 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  linear_combination (-3/4) * m4 + (5/4) * m5 + (-3/4) * m6 + (-1/4) * c12 + (-1/4) * c13 + (1/2) * c14 + (-1/2) * c15 + (1/2) * c16 + (-1/4) * c23 + (1/2) * c24 + (-1/2) * c25 + (1/2) * c26 + (1/2) * c34 + (-1/2) * c35 + (1/2) * c36 + (-1/2) * c45 + (1/2) * c46 + (-1/2) * c56

/-- The top probability at the complement of A3 equals the bottom one. -/
theorem eq3 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    -q3 + r12 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  linear_combination (-3/4) * m4 + (-3/4) * m5 + (5/4) * m6 + (-1/4) * c12 + (-1/4) * c13 + (1/2) * c14 + (1/2) * c15 + (-1/2) * c16 + (-1/4) * c23 + (1/2) * c24 + (1/2) * c25 + (-1/2) * c26 + (1/2) * c34 + (1/2) * c35 + (-1/2) * c36 + (1/2) * c45 + (-1/2) * c46 + (-1/2) * c56

/-- The top probability at the complement of B13 equals the bottom one. -/
theorem eq4 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    -q4 + r11 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  linear_combination (1/4) * m4 + (1/4) * m5 + (-3/4) * m6 + (1/4) * c12 + (1/4) * c13 + (-1/2) * c14 + (-1/2) * c15 + (1/2) * c16 + (-1/4) * c23 + (-1/2) * c45 + (1/2) * c46 + (1/2) * c56

/-- The top probability at the complement of B12 equals the bottom one. -/
theorem eq5 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    -q5 + r10 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  linear_combination (1/4) * m4 + (-3/4) * m5 + (1/4) * m6 + (1/4) * c12 + (1/4) * c13 + (-1/2) * c14 + (1/2) * c15 + (-1/2) * c16 + (-1/4) * c23 + (1/2) * c45 + (-1/2) * c46 + (1/2) * c56

/-- The top probability at the complement of B11 equals the bottom one. -/
theorem eq6 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    -q6 + r9 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  linear_combination (-3/4) * m4 + (1/4) * m5 + (1/4) * m6 + (1/4) * c12 + (1/4) * c13 + (1/2) * c14 + (-1/2) * c15 + (-1/2) * c16 + (-1/4) * c23 + (1/2) * c45 + (1/2) * c46 + (-1/2) * c56

/-- The top probability at the complement of B10 equals the bottom one. -/
theorem eq7 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    -q7 + r8 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  linear_combination (-1) * m1 + (1/4) * m4 + (1/4) * m5 + (1/4) * m6 + (1/4) * c12 + (1/4) * c13 + (1/2) * c14 + (1/2) * c15 + (1/2) * c16 + (-1/4) * c23 + (-1/2) * c45 + (-1/2) * c46 + (-1/2) * c56

/-- The top probability at the complement of B23 equals the bottom one. -/
theorem eq8 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    -q8 + r7 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  linear_combination (1/4) * m4 + (1/4) * m5 + (-3/4) * m6 + (1/4) * c12 + (-1/4) * c13 + (1/4) * c23 + (-1/2) * c24 + (-1/2) * c25 + (1/2) * c26 + (-1/2) * c45 + (1/2) * c46 + (1/2) * c56

/-- The top probability at the complement of B22 equals the bottom one. -/
theorem eq9 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    -q9 + r6 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  linear_combination (1/4) * m4 + (-3/4) * m5 + (1/4) * m6 + (1/4) * c12 + (-1/4) * c13 + (1/4) * c23 + (-1/2) * c24 + (1/2) * c25 + (-1/2) * c26 + (1/2) * c45 + (-1/2) * c46 + (1/2) * c56

/-- The top probability at the complement of B21 equals the bottom one. -/
theorem eq10 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    -q10 + r5 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  linear_combination (-3/4) * m4 + (1/4) * m5 + (1/4) * m6 + (1/4) * c12 + (-1/4) * c13 + (1/4) * c23 + (1/2) * c24 + (-1/2) * c25 + (-1/2) * c26 + (1/2) * c45 + (1/2) * c46 + (-1/2) * c56

/-- The top probability at the complement of B20 equals the bottom one. -/
theorem eq11 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    -q11 + r4 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  linear_combination (-1) * m2 + (1/4) * m4 + (1/4) * m5 + (1/4) * m6 + (1/4) * c12 + (-1/4) * c13 + (1/4) * c23 + (1/2) * c24 + (1/2) * c25 + (1/2) * c26 + (-1/2) * c45 + (-1/2) * c46 + (-1/2) * c56

/-- The top probability at the complement of B33 equals the bottom one. -/
theorem eq12 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    -q12 + r3 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  linear_combination (1/4) * m4 + (1/4) * m5 + (-3/4) * m6 + (-1/4) * c12 + (1/4) * c13 + (1/4) * c23 + (-1/2) * c34 + (-1/2) * c35 + (1/2) * c36 + (-1/2) * c45 + (1/2) * c46 + (1/2) * c56

/-- The top probability at the complement of B32 equals the bottom one. -/
theorem eq13 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    -q13 + r2 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  linear_combination (1/4) * m4 + (-3/4) * m5 + (1/4) * m6 + (-1/4) * c12 + (1/4) * c13 + (1/4) * c23 + (-1/2) * c34 + (1/2) * c35 + (-1/2) * c36 + (1/2) * c45 + (-1/2) * c46 + (1/2) * c56

/-- The top probability at the complement of B31 equals the bottom one. -/
theorem eq14 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    -q14 + r1 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  linear_combination (-3/4) * m4 + (1/4) * m5 + (1/4) * m6 + (-1/4) * c12 + (1/4) * c13 + (1/4) * c23 + (1/2) * c34 + (-1/2) * c35 + (-1/2) * c36 + (1/2) * c45 + (1/2) * c46 + (-1/2) * c56

/-- The top probability at the complement of B30 equals the bottom one. -/
theorem eq15 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    -q15 + r0 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  linear_combination (-1) * m3 + (1/4) * m4 + (1/4) * m5 + (1/4) * m6 + (-1/4) * c12 + (1/4) * c13 + (1/4) * c23 + (1/2) * c34 + (1/2) * c35 + (1/2) * c36 + (-1/2) * c45 + (-1/2) * c46 + (-1/2) * c56

/-- Row B1 carries a quarter. -/
theorem row1 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    q4 + q5 + q6 + q7 - 1/4 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  linear_combination (1/4) * n1 + (1/4) * m1 + (1/4) * m2 + (1/4) * m3 + (-1/2) * c12 + (-1/2) * c13 + (1/2) * c23

/-- Row B2 carries a quarter. -/
theorem row2 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    q10 + q11 + q8 + q9 - 1/4 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  linear_combination (1/4) * n1 + (1/4) * m1 + (1/4) * m2 + (1/4) * m3 + (-1/2) * c12 + (1/2) * c13 + (-1/2) * c23

/-- Row B3 carries a quarter. -/
theorem row3 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    q12 + q13 + q14 + q15 - 1/4 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  linear_combination (1/4) * n1 + (1/4) * m1 + (1/4) * m2 + (1/4) * m3 + (1/2) * c12 + (-1/2) * c13 + (-1/2) * c23

/-- Column 0: alpha equals the B-column total minus 1/8. -/
theorem col0 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    q0 - q11 - q15 - q7 + 1/8 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  linear_combination (1) * n0 + (-9/8) * n1 + (-9/8) * m1 + (-9/8) * m2 + (-9/8) * m3 + (1/4) * c12 + (1/4) * c13 + (1/2) * c14 + (1/2) * c15 + (1/2) * c16 + (1/4) * c23 + (1/2) * c24 + (1/2) * c25 + (1/2) * c26 + (1/2) * c34 + (1/2) * c35 + (1/2) * c36 + (-1) * c45 + (-1) * c46 + (-1) * c56

/-- Column 1: alpha equals the B-column total minus 1/8. -/
theorem col1 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    q1 - q10 - q14 - q6 + 1/8 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  linear_combination (-1/8) * n1 + (-1/8) * m1 + (-1/8) * m2 + (-1/8) * m3 + (-2) * m4 + (1) * m5 + (1) * m6 + (1/4) * c12 + (1/4) * c13 + (1/2) * c14 + (-1/2) * c15 + (-1/2) * c16 + (1/4) * c23 + (1/2) * c24 + (-1/2) * c25 + (-1/2) * c26 + (1/2) * c34 + (-1/2) * c35 + (-1/2) * c36 + (1) * c45 + (1) * c46 + (-1) * c56

/-- Column 2: alpha equals the B-column total minus 1/8. -/
theorem col2 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    -q13 + q2 - q5 - q9 + 1/8 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  linear_combination (-1/8) * n1 + (-1/8) * m1 + (-1/8) * m2 + (-1/8) * m3 + (1) * m4 + (-2) * m5 + (1) * m6 + (1/4) * c12 + (1/4) * c13 + (-1/2) * c14 + (1/2) * c15 + (-1/2) * c16 + (1/4) * c23 + (-1/2) * c24 + (1/2) * c25 + (-1/2) * c26 + (-1/2) * c34 + (1/2) * c35 + (-1/2) * c36 + (1) * c45 + (-1) * c46 + (1) * c56

/-- Column 3: alpha equals the B-column total minus 1/8. -/
theorem col3 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    -q12 + q3 - q4 - q8 + 1/8 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  linear_combination (-1/8) * n1 + (-1/8) * m1 + (-1/8) * m2 + (-1/8) * m3 + (1) * m4 + (1) * m5 + (-2) * m6 + (1/4) * c12 + (1/4) * c13 + (-1/2) * c14 + (-1/2) * c15 + (1/2) * c16 + (1/4) * c23 + (-1/2) * c24 + (-1/2) * c25 + (1/2) * c26 + (-1/2) * c34 + (-1/2) * c35 + (1/2) * c36 + (-1) * c45 + (1) * c46 + (1) * c56


/-! ## Family one: the column relation -/

def ef0 : SS.BitString 6 := bs true  false false false false false  -- mask 100000
def ef1 : SS.BitString 6 := bs false true  false false false false  -- mask 010000
def ef2 : SS.BitString 6 := bs false false true  false false false  -- mask 001000
def w0 : SS.BitString 6 := bs false false false false false false  -- dressing 000000
def w1 : SS.BitString 6 := bs false true  false false false false  -- dressing 010000
def w2 : SS.BitString 6 := bs true  false false false false false  -- dressing 100000

def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),
      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

theorem incidence0 :
    S1.filter (fun y => SS.bxor y ef0 ∈ S0) = {z8, z9, z10, z11, z12, z13, z14, z15} := by decide
theorem fl0_8 : SS.bxor z8 ef0 = y0 := by decide
theorem fl0_9 : SS.bxor z9 ef0 = y1 := by decide
theorem fl0_10 : SS.bxor z10 ef0 = y2 := by decide
theorem fl0_11 : SS.bxor z11 ef0 = y3 := by decide
theorem fl0_12 : SS.bxor z12 ef0 = y4 := by decide
theorem fl0_13 : SS.bxor z13 ef0 = y5 := by decide
theorem fl0_14 : SS.bxor z14 ef0 = y6 := by decide
theorem fl0_15 : SS.bxor z15 ef0 = y7 := by decide
theorem sg0_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg0_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg0_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg0_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg0_w0_12 : SS.bdot w0 z12 = false := by decide
theorem sg0_w0_13 : SS.bdot w0 z13 = false := by decide
theorem sg0_w0_14 : SS.bdot w0 z14 = false := by decide
theorem sg0_w0_15 : SS.bdot w0 z15 = false := by decide
theorem sg0_w1_8 : SS.bdot w1 z8 = false := by decide
theorem sg0_w1_9 : SS.bdot w1 z9 = false := by decide
theorem sg0_w1_10 : SS.bdot w1 z10 = false := by decide
theorem sg0_w1_11 : SS.bdot w1 z11 = false := by decide
theorem sg0_w1_12 : SS.bdot w1 z12 = true := by decide
theorem sg0_w1_13 : SS.bdot w1 z13 = true := by decide
theorem sg0_w1_14 : SS.bdot w1 z14 = true := by decide
theorem sg0_w1_15 : SS.bdot w1 z15 = true := by decide
theorem incidence1 :
    S1.filter (fun y => SS.bxor y ef1 ∈ S0) = {z4, z5, z6, z7, z12, z13, z14, z15} := by decide
theorem fl1_4 : SS.bxor z4 ef1 = y0 := by decide
theorem fl1_5 : SS.bxor z5 ef1 = y1 := by decide
theorem fl1_6 : SS.bxor z6 ef1 = y2 := by decide
theorem fl1_7 : SS.bxor z7 ef1 = y3 := by decide
theorem fl1_12 : SS.bxor z12 ef1 = y8 := by decide
theorem fl1_13 : SS.bxor z13 ef1 = y9 := by decide
theorem fl1_14 : SS.bxor z14 ef1 = y10 := by decide
theorem fl1_15 : SS.bxor z15 ef1 = y11 := by decide
theorem sg1_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg1_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg1_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg1_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg1_w0_12 : SS.bdot w0 z12 = false := by decide
theorem sg1_w0_13 : SS.bdot w0 z13 = false := by decide
theorem sg1_w0_14 : SS.bdot w0 z14 = false := by decide
theorem sg1_w0_15 : SS.bdot w0 z15 = false := by decide
theorem sg1_w2_4 : SS.bdot w2 z4 = false := by decide
theorem sg1_w2_5 : SS.bdot w2 z5 = false := by decide
theorem sg1_w2_6 : SS.bdot w2 z6 = false := by decide
theorem sg1_w2_7 : SS.bdot w2 z7 = false := by decide
theorem sg1_w2_12 : SS.bdot w2 z12 = true := by decide
theorem sg1_w2_13 : SS.bdot w2 z13 = true := by decide
theorem sg1_w2_14 : SS.bdot w2 z14 = true := by decide
theorem sg1_w2_15 : SS.bdot w2 z15 = true := by decide
theorem incidence2 :
    S1.filter (fun y => SS.bxor y ef2 ∈ S0) = {z0, z1, z2, z3, z12, z13, z14, z15} := by decide
theorem fl2_0 : SS.bxor z0 ef2 = y0 := by decide
theorem fl2_1 : SS.bxor z1 ef2 = y1 := by decide
theorem fl2_2 : SS.bxor z2 ef2 = y2 := by decide
theorem fl2_3 : SS.bxor z3 ef2 = y3 := by decide
theorem fl2_12 : SS.bxor z12 ef2 = y12 := by decide
theorem fl2_13 : SS.bxor z13 ef2 = y13 := by decide
theorem fl2_14 : SS.bxor z14 ef2 = y14 := by decide
theorem fl2_15 : SS.bxor z15 ef2 = y15 := by decide
theorem sg2_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg2_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg2_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg2_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg2_w0_12 : SS.bdot w0 z12 = false := by decide
theorem sg2_w0_13 : SS.bdot w0 z13 = false := by decide
theorem sg2_w0_14 : SS.bdot w0 z14 = false := by decide
theorem sg2_w0_15 : SS.bdot w0 z15 = false := by decide
theorem sg2_w2_0 : SS.bdot w2 z0 = false := by decide
theorem sg2_w2_1 : SS.bdot w2 z1 = false := by decide
theorem sg2_w2_2 : SS.bdot w2 z2 = false := by decide
theorem sg2_w2_3 : SS.bdot w2 z3 = false := by decide
theorem sg2_w2_12 : SS.bdot w2 z12 = true := by decide
theorem sg2_w2_13 : SS.bdot w2 z13 = true := by decide
theorem sg2_w2_14 : SS.bdot w2 z14 = true := by decide
theorem sg2_w2_15 : SS.bdot w2 z15 = true := by decide

theorem ex0_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w0 = star (c y0) * d z8 + star (c y1) * d z9 + star (c y2) * d z10 + star (c y3) * d z11 + star (c y4) * d z12 + star (c y5) * d z13 + star (c y6) * d z14 + star (c y7) * d z15 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_8, fl0_9, fl0_10, fl0_11, fl0_12, fl0_13, fl0_14, fl0_15]
  simp only [sg0_w0_8, sg0_w0_9, sg0_w0_10, sg0_w0_11, sg0_w0_12, sg0_w0_13, sg0_w0_14, sg0_w0_15, SixQubit.signMul_false]
  try ring

theorem ex0_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w1 = star (c y0) * d z8 + star (c y1) * d z9 + star (c y2) * d z10 + star (c y3) * d z11 - star (c y4) * d z12 - star (c y5) * d z13 - star (c y6) * d z14 - star (c y7) * d z15 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_8, fl0_9, fl0_10, fl0_11, fl0_12, fl0_13, fl0_14, fl0_15]
  simp only [sg0_w1_8, sg0_w1_9, sg0_w1_10, sg0_w1_11, sg0_w1_12, sg0_w1_13, sg0_w1_14, sg0_w1_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex1_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w0 = star (c y0) * d z4 + star (c y1) * d z5 + star (c y2) * d z6 + star (c y3) * d z7 + star (c y8) * d z12 + star (c y9) * d z13 + star (c y10) * d z14 + star (c y11) * d z15 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_4, fl1_5, fl1_6, fl1_7, fl1_12, fl1_13, fl1_14, fl1_15]
  simp only [sg1_w0_4, sg1_w0_5, sg1_w0_6, sg1_w0_7, sg1_w0_12, sg1_w0_13, sg1_w0_14, sg1_w0_15, SixQubit.signMul_false]
  try ring

theorem ex1_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w2 = star (c y0) * d z4 + star (c y1) * d z5 + star (c y2) * d z6 + star (c y3) * d z7 - star (c y8) * d z12 - star (c y9) * d z13 - star (c y10) * d z14 - star (c y11) * d z15 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_4, fl1_5, fl1_6, fl1_7, fl1_12, fl1_13, fl1_14, fl1_15]
  simp only [sg1_w2_4, sg1_w2_5, sg1_w2_6, sg1_w2_7, sg1_w2_12, sg1_w2_13, sg1_w2_14, sg1_w2_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex2_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w0 = star (c y0) * d z0 + star (c y1) * d z1 + star (c y2) * d z2 + star (c y3) * d z3 + star (c y12) * d z12 + star (c y13) * d z13 + star (c y14) * d z14 + star (c y15) * d z15 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_0, fl2_1, fl2_2, fl2_3, fl2_12, fl2_13, fl2_14, fl2_15]
  simp only [sg2_w0_0, sg2_w0_1, sg2_w0_2, sg2_w0_3, sg2_w0_12, sg2_w0_13, sg2_w0_14, sg2_w0_15, SixQubit.signMul_false]
  try ring

theorem ex2_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w2 = star (c y0) * d z0 + star (c y1) * d z1 + star (c y2) * d z2 + star (c y3) * d z3 - star (c y12) * d z12 - star (c y13) * d z13 - star (c y14) * d z14 - star (c y15) * d z15 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_0, fl2_1, fl2_2, fl2_3, fl2_12, fl2_13, fl2_14, fl2_15]
  simp only [sg2_w2_0, sg2_w2_1, sg2_w2_2, sg2_w2_3, sg2_w2_12, sg2_w2_13, sg2_w2_14, sg2_w2_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

/-- Family one at row B1: the four `B`-to-`A` incidences sum to zero. -/
theorem fam1_1 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef0 w0 = 0)
    (h1 : offSum c d ef0 w1 = 0)
    : star (c y4) * d z12 + star (c y5) * d z13 + star (c y6) * d z14 + star (c y7) * d z15 = 0 := by
  rw [ex0_w0] at h0
  rw [ex0_w1] at h1
  linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1

/-- Family one at row B2: the four `B`-to-`A` incidences sum to zero. -/
theorem fam1_2 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef1 w0 = 0)
    (h1 : offSum c d ef1 w2 = 0)
    : star (c y8) * d z12 + star (c y9) * d z13 + star (c y10) * d z14 + star (c y11) * d z15 = 0 := by
  rw [ex1_w0] at h0
  rw [ex1_w2] at h1
  linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1

/-- Family one at row B3: the four `B`-to-`A` incidences sum to zero. -/
theorem fam1_3 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef2 w0 = 0)
    (h1 : offSum c d ef2 w2 = 0)
    : star (c y12) * d z12 + star (c y13) * d z13 + star (c y14) * d z14 + star (c y15) * d z15 = 0 := by
  rw [ex2_w0] at h0
  rw [ex2_w2] at h1
  linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1


/-! ## Family two: the vanishing permanents -/

def ef3 : SS.BitString 6 := bs true  false false true  false false  -- mask 100100
def ef4 : SS.BitString 6 := bs false true  false true  false false  -- mask 010100
def ef5 : SS.BitString 6 := bs false false true  true  false false  -- mask 001100
def ef6 : SS.BitString 6 := bs true  false false false true  false  -- mask 100010
def ef7 : SS.BitString 6 := bs false true  false false true  false  -- mask 010010
def ef8 : SS.BitString 6 := bs false false true  false true  false  -- mask 001010
def ef9 : SS.BitString 6 := bs true  false false false false true   -- mask 100001
def ef10 : SS.BitString 6 := bs false true  false false false true   -- mask 010001
def ef11 : SS.BitString 6 := bs false false true  false false true   -- mask 001001
def w3 : SS.BitString 6 := bs false false false false false true   -- dressing 000001
def w4 : SS.BitString 6 := bs false false false false true  false  -- dressing 000010
def w5 : SS.BitString 6 := bs false false false true  false false  -- dressing 000100

theorem incidence3 :
    S1.filter (fun y => SS.bxor y ef3 ∈ S0) = {z0, z1, z2, z3, z4, z5, z6, z7} := by decide
theorem fl3_0 : SS.bxor z0 ef3 = y10 := by decide
theorem fl3_1 : SS.bxor z1 ef3 = y11 := by decide
theorem fl3_2 : SS.bxor z2 ef3 = y8 := by decide
theorem fl3_3 : SS.bxor z3 ef3 = y9 := by decide
theorem fl3_4 : SS.bxor z4 ef3 = y14 := by decide
theorem fl3_5 : SS.bxor z5 ef3 = y15 := by decide
theorem fl3_6 : SS.bxor z6 ef3 = y12 := by decide
theorem fl3_7 : SS.bxor z7 ef3 = y13 := by decide
theorem sg3_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg3_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg3_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg3_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg3_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg3_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg3_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg3_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg3_w5_0 : SS.bdot w5 z0 = false := by decide
theorem sg3_w5_1 : SS.bdot w5 z1 = false := by decide
theorem sg3_w5_2 : SS.bdot w5 z2 = true := by decide
theorem sg3_w5_3 : SS.bdot w5 z3 = true := by decide
theorem sg3_w5_4 : SS.bdot w5 z4 = false := by decide
theorem sg3_w5_5 : SS.bdot w5 z5 = false := by decide
theorem sg3_w5_6 : SS.bdot w5 z6 = true := by decide
theorem sg3_w5_7 : SS.bdot w5 z7 = true := by decide
theorem incidence4 :
    S1.filter (fun y => SS.bxor y ef4 ∈ S0) = {z0, z1, z2, z3, z8, z9, z10, z11} := by decide
theorem fl4_0 : SS.bxor z0 ef4 = y6 := by decide
theorem fl4_1 : SS.bxor z1 ef4 = y7 := by decide
theorem fl4_2 : SS.bxor z2 ef4 = y4 := by decide
theorem fl4_3 : SS.bxor z3 ef4 = y5 := by decide
theorem fl4_8 : SS.bxor z8 ef4 = y14 := by decide
theorem fl4_9 : SS.bxor z9 ef4 = y15 := by decide
theorem fl4_10 : SS.bxor z10 ef4 = y12 := by decide
theorem fl4_11 : SS.bxor z11 ef4 = y13 := by decide
theorem sg4_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg4_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg4_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg4_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg4_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg4_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg4_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg4_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg4_w5_0 : SS.bdot w5 z0 = false := by decide
theorem sg4_w5_1 : SS.bdot w5 z1 = false := by decide
theorem sg4_w5_2 : SS.bdot w5 z2 = true := by decide
theorem sg4_w5_3 : SS.bdot w5 z3 = true := by decide
theorem sg4_w5_8 : SS.bdot w5 z8 = false := by decide
theorem sg4_w5_9 : SS.bdot w5 z9 = false := by decide
theorem sg4_w5_10 : SS.bdot w5 z10 = true := by decide
theorem sg4_w5_11 : SS.bdot w5 z11 = true := by decide
theorem incidence5 :
    S1.filter (fun y => SS.bxor y ef5 ∈ S0) = {z4, z5, z6, z7, z8, z9, z10, z11} := by decide
theorem fl5_4 : SS.bxor z4 ef5 = y6 := by decide
theorem fl5_5 : SS.bxor z5 ef5 = y7 := by decide
theorem fl5_6 : SS.bxor z6 ef5 = y4 := by decide
theorem fl5_7 : SS.bxor z7 ef5 = y5 := by decide
theorem fl5_8 : SS.bxor z8 ef5 = y10 := by decide
theorem fl5_9 : SS.bxor z9 ef5 = y11 := by decide
theorem fl5_10 : SS.bxor z10 ef5 = y8 := by decide
theorem fl5_11 : SS.bxor z11 ef5 = y9 := by decide
theorem sg5_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg5_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg5_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg5_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg5_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg5_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg5_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg5_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg5_w5_4 : SS.bdot w5 z4 = false := by decide
theorem sg5_w5_5 : SS.bdot w5 z5 = false := by decide
theorem sg5_w5_6 : SS.bdot w5 z6 = true := by decide
theorem sg5_w5_7 : SS.bdot w5 z7 = true := by decide
theorem sg5_w5_8 : SS.bdot w5 z8 = false := by decide
theorem sg5_w5_9 : SS.bdot w5 z9 = false := by decide
theorem sg5_w5_10 : SS.bdot w5 z10 = true := by decide
theorem sg5_w5_11 : SS.bdot w5 z11 = true := by decide
theorem incidence6 :
    S1.filter (fun y => SS.bxor y ef6 ∈ S0) = {z0, z1, z2, z3, z4, z5, z6, z7} := by decide
theorem fl6_0 : SS.bxor z0 ef6 = y9 := by decide
theorem fl6_1 : SS.bxor z1 ef6 = y8 := by decide
theorem fl6_2 : SS.bxor z2 ef6 = y11 := by decide
theorem fl6_3 : SS.bxor z3 ef6 = y10 := by decide
theorem fl6_4 : SS.bxor z4 ef6 = y13 := by decide
theorem fl6_5 : SS.bxor z5 ef6 = y12 := by decide
theorem fl6_6 : SS.bxor z6 ef6 = y15 := by decide
theorem fl6_7 : SS.bxor z7 ef6 = y14 := by decide
theorem sg6_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg6_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg6_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg6_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg6_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg6_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg6_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg6_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg6_w4_0 : SS.bdot w4 z0 = false := by decide
theorem sg6_w4_1 : SS.bdot w4 z1 = true := by decide
theorem sg6_w4_2 : SS.bdot w4 z2 = false := by decide
theorem sg6_w4_3 : SS.bdot w4 z3 = true := by decide
theorem sg6_w4_4 : SS.bdot w4 z4 = false := by decide
theorem sg6_w4_5 : SS.bdot w4 z5 = true := by decide
theorem sg6_w4_6 : SS.bdot w4 z6 = false := by decide
theorem sg6_w4_7 : SS.bdot w4 z7 = true := by decide
theorem incidence7 :
    S1.filter (fun y => SS.bxor y ef7 ∈ S0) = {z0, z1, z2, z3, z8, z9, z10, z11} := by decide
theorem fl7_0 : SS.bxor z0 ef7 = y5 := by decide
theorem fl7_1 : SS.bxor z1 ef7 = y4 := by decide
theorem fl7_2 : SS.bxor z2 ef7 = y7 := by decide
theorem fl7_3 : SS.bxor z3 ef7 = y6 := by decide
theorem fl7_8 : SS.bxor z8 ef7 = y13 := by decide
theorem fl7_9 : SS.bxor z9 ef7 = y12 := by decide
theorem fl7_10 : SS.bxor z10 ef7 = y15 := by decide
theorem fl7_11 : SS.bxor z11 ef7 = y14 := by decide
theorem sg7_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg7_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg7_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg7_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg7_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg7_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg7_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg7_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg7_w4_0 : SS.bdot w4 z0 = false := by decide
theorem sg7_w4_1 : SS.bdot w4 z1 = true := by decide
theorem sg7_w4_2 : SS.bdot w4 z2 = false := by decide
theorem sg7_w4_3 : SS.bdot w4 z3 = true := by decide
theorem sg7_w4_8 : SS.bdot w4 z8 = false := by decide
theorem sg7_w4_9 : SS.bdot w4 z9 = true := by decide
theorem sg7_w4_10 : SS.bdot w4 z10 = false := by decide
theorem sg7_w4_11 : SS.bdot w4 z11 = true := by decide
theorem incidence8 :
    S1.filter (fun y => SS.bxor y ef8 ∈ S0) = {z4, z5, z6, z7, z8, z9, z10, z11} := by decide
theorem fl8_4 : SS.bxor z4 ef8 = y5 := by decide
theorem fl8_5 : SS.bxor z5 ef8 = y4 := by decide
theorem fl8_6 : SS.bxor z6 ef8 = y7 := by decide
theorem fl8_7 : SS.bxor z7 ef8 = y6 := by decide
theorem fl8_8 : SS.bxor z8 ef8 = y9 := by decide
theorem fl8_9 : SS.bxor z9 ef8 = y8 := by decide
theorem fl8_10 : SS.bxor z10 ef8 = y11 := by decide
theorem fl8_11 : SS.bxor z11 ef8 = y10 := by decide
theorem sg8_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg8_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg8_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg8_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg8_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg8_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg8_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg8_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg8_w4_4 : SS.bdot w4 z4 = false := by decide
theorem sg8_w4_5 : SS.bdot w4 z5 = true := by decide
theorem sg8_w4_6 : SS.bdot w4 z6 = false := by decide
theorem sg8_w4_7 : SS.bdot w4 z7 = true := by decide
theorem sg8_w4_8 : SS.bdot w4 z8 = false := by decide
theorem sg8_w4_9 : SS.bdot w4 z9 = true := by decide
theorem sg8_w4_10 : SS.bdot w4 z10 = false := by decide
theorem sg8_w4_11 : SS.bdot w4 z11 = true := by decide
theorem incidence9 :
    S1.filter (fun y => SS.bxor y ef9 ∈ S0) = {z0, z1, z2, z3, z4, z5, z6, z7} := by decide
theorem fl9_0 : SS.bxor z0 ef9 = y8 := by decide
theorem fl9_1 : SS.bxor z1 ef9 = y9 := by decide
theorem fl9_2 : SS.bxor z2 ef9 = y10 := by decide
theorem fl9_3 : SS.bxor z3 ef9 = y11 := by decide
theorem fl9_4 : SS.bxor z4 ef9 = y12 := by decide
theorem fl9_5 : SS.bxor z5 ef9 = y13 := by decide
theorem fl9_6 : SS.bxor z6 ef9 = y14 := by decide
theorem fl9_7 : SS.bxor z7 ef9 = y15 := by decide
theorem sg9_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg9_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg9_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg9_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg9_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg9_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg9_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg9_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg9_w3_0 : SS.bdot w3 z0 = false := by decide
theorem sg9_w3_1 : SS.bdot w3 z1 = true := by decide
theorem sg9_w3_2 : SS.bdot w3 z2 = true := by decide
theorem sg9_w3_3 : SS.bdot w3 z3 = false := by decide
theorem sg9_w3_4 : SS.bdot w3 z4 = false := by decide
theorem sg9_w3_5 : SS.bdot w3 z5 = true := by decide
theorem sg9_w3_6 : SS.bdot w3 z6 = true := by decide
theorem sg9_w3_7 : SS.bdot w3 z7 = false := by decide
theorem incidence10 :
    S1.filter (fun y => SS.bxor y ef10 ∈ S0) = {z0, z1, z2, z3, z8, z9, z10, z11} := by decide
theorem fl10_0 : SS.bxor z0 ef10 = y4 := by decide
theorem fl10_1 : SS.bxor z1 ef10 = y5 := by decide
theorem fl10_2 : SS.bxor z2 ef10 = y6 := by decide
theorem fl10_3 : SS.bxor z3 ef10 = y7 := by decide
theorem fl10_8 : SS.bxor z8 ef10 = y12 := by decide
theorem fl10_9 : SS.bxor z9 ef10 = y13 := by decide
theorem fl10_10 : SS.bxor z10 ef10 = y14 := by decide
theorem fl10_11 : SS.bxor z11 ef10 = y15 := by decide
theorem sg10_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg10_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg10_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg10_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg10_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg10_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg10_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg10_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg10_w3_0 : SS.bdot w3 z0 = false := by decide
theorem sg10_w3_1 : SS.bdot w3 z1 = true := by decide
theorem sg10_w3_2 : SS.bdot w3 z2 = true := by decide
theorem sg10_w3_3 : SS.bdot w3 z3 = false := by decide
theorem sg10_w3_8 : SS.bdot w3 z8 = false := by decide
theorem sg10_w3_9 : SS.bdot w3 z9 = true := by decide
theorem sg10_w3_10 : SS.bdot w3 z10 = true := by decide
theorem sg10_w3_11 : SS.bdot w3 z11 = false := by decide
theorem incidence11 :
    S1.filter (fun y => SS.bxor y ef11 ∈ S0) = {z4, z5, z6, z7, z8, z9, z10, z11} := by decide
theorem fl11_4 : SS.bxor z4 ef11 = y4 := by decide
theorem fl11_5 : SS.bxor z5 ef11 = y5 := by decide
theorem fl11_6 : SS.bxor z6 ef11 = y6 := by decide
theorem fl11_7 : SS.bxor z7 ef11 = y7 := by decide
theorem fl11_8 : SS.bxor z8 ef11 = y8 := by decide
theorem fl11_9 : SS.bxor z9 ef11 = y9 := by decide
theorem fl11_10 : SS.bxor z10 ef11 = y10 := by decide
theorem fl11_11 : SS.bxor z11 ef11 = y11 := by decide
theorem sg11_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg11_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg11_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg11_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg11_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg11_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg11_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg11_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg11_w3_4 : SS.bdot w3 z4 = false := by decide
theorem sg11_w3_5 : SS.bdot w3 z5 = true := by decide
theorem sg11_w3_6 : SS.bdot w3 z6 = true := by decide
theorem sg11_w3_7 : SS.bdot w3 z7 = false := by decide
theorem sg11_w3_8 : SS.bdot w3 z8 = false := by decide
theorem sg11_w3_9 : SS.bdot w3 z9 = true := by decide
theorem sg11_w3_10 : SS.bdot w3 z10 = true := by decide
theorem sg11_w3_11 : SS.bdot w3 z11 = false := by decide

theorem ex3_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w0 = star (c y10) * d z0 + star (c y11) * d z1 + star (c y8) * d z2 + star (c y9) * d z3 + star (c y14) * d z4 + star (c y15) * d z5 + star (c y12) * d z6 + star (c y13) * d z7 := by
  unfold offSum
  rw [incidence3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl3_0, fl3_1, fl3_2, fl3_3, fl3_4, fl3_5, fl3_6, fl3_7]
  simp only [sg3_w0_0, sg3_w0_1, sg3_w0_2, sg3_w0_3, sg3_w0_4, sg3_w0_5, sg3_w0_6, sg3_w0_7, SixQubit.signMul_false]
  try ring

theorem ex3_w5 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w5 = star (c y10) * d z0 + star (c y11) * d z1 - star (c y8) * d z2 - star (c y9) * d z3 + star (c y14) * d z4 + star (c y15) * d z5 - star (c y12) * d z6 - star (c y13) * d z7 := by
  unfold offSum
  rw [incidence3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl3_0, fl3_1, fl3_2, fl3_3, fl3_4, fl3_5, fl3_6, fl3_7]
  simp only [sg3_w5_0, sg3_w5_1, sg3_w5_2, sg3_w5_3, sg3_w5_4, sg3_w5_5, sg3_w5_6, sg3_w5_7, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex4_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w0 = star (c y6) * d z0 + star (c y7) * d z1 + star (c y4) * d z2 + star (c y5) * d z3 + star (c y14) * d z8 + star (c y15) * d z9 + star (c y12) * d z10 + star (c y13) * d z11 := by
  unfold offSum
  rw [incidence4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl4_0, fl4_1, fl4_2, fl4_3, fl4_8, fl4_9, fl4_10, fl4_11]
  simp only [sg4_w0_0, sg4_w0_1, sg4_w0_2, sg4_w0_3, sg4_w0_8, sg4_w0_9, sg4_w0_10, sg4_w0_11, SixQubit.signMul_false]
  try ring

theorem ex4_w5 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w5 = star (c y6) * d z0 + star (c y7) * d z1 - star (c y4) * d z2 - star (c y5) * d z3 + star (c y14) * d z8 + star (c y15) * d z9 - star (c y12) * d z10 - star (c y13) * d z11 := by
  unfold offSum
  rw [incidence4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl4_0, fl4_1, fl4_2, fl4_3, fl4_8, fl4_9, fl4_10, fl4_11]
  simp only [sg4_w5_0, sg4_w5_1, sg4_w5_2, sg4_w5_3, sg4_w5_8, sg4_w5_9, sg4_w5_10, sg4_w5_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex5_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef5 w0 = star (c y6) * d z4 + star (c y7) * d z5 + star (c y4) * d z6 + star (c y5) * d z7 + star (c y10) * d z8 + star (c y11) * d z9 + star (c y8) * d z10 + star (c y9) * d z11 := by
  unfold offSum
  rw [incidence5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl5_4, fl5_5, fl5_6, fl5_7, fl5_8, fl5_9, fl5_10, fl5_11]
  simp only [sg5_w0_4, sg5_w0_5, sg5_w0_6, sg5_w0_7, sg5_w0_8, sg5_w0_9, sg5_w0_10, sg5_w0_11, SixQubit.signMul_false]
  try ring

theorem ex5_w5 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef5 w5 = star (c y6) * d z4 + star (c y7) * d z5 - star (c y4) * d z6 - star (c y5) * d z7 + star (c y10) * d z8 + star (c y11) * d z9 - star (c y8) * d z10 - star (c y9) * d z11 := by
  unfold offSum
  rw [incidence5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl5_4, fl5_5, fl5_6, fl5_7, fl5_8, fl5_9, fl5_10, fl5_11]
  simp only [sg5_w5_4, sg5_w5_5, sg5_w5_6, sg5_w5_7, sg5_w5_8, sg5_w5_9, sg5_w5_10, sg5_w5_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex6_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w0 = star (c y9) * d z0 + star (c y8) * d z1 + star (c y11) * d z2 + star (c y10) * d z3 + star (c y13) * d z4 + star (c y12) * d z5 + star (c y15) * d z6 + star (c y14) * d z7 := by
  unfold offSum
  rw [incidence6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl6_0, fl6_1, fl6_2, fl6_3, fl6_4, fl6_5, fl6_6, fl6_7]
  simp only [sg6_w0_0, sg6_w0_1, sg6_w0_2, sg6_w0_3, sg6_w0_4, sg6_w0_5, sg6_w0_6, sg6_w0_7, SixQubit.signMul_false]
  try ring

theorem ex6_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w4 = star (c y9) * d z0 - star (c y8) * d z1 + star (c y11) * d z2 - star (c y10) * d z3 + star (c y13) * d z4 - star (c y12) * d z5 + star (c y15) * d z6 - star (c y14) * d z7 := by
  unfold offSum
  rw [incidence6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl6_0, fl6_1, fl6_2, fl6_3, fl6_4, fl6_5, fl6_6, fl6_7]
  simp only [sg6_w4_0, sg6_w4_1, sg6_w4_2, sg6_w4_3, sg6_w4_4, sg6_w4_5, sg6_w4_6, sg6_w4_7, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex7_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef7 w0 = star (c y5) * d z0 + star (c y4) * d z1 + star (c y7) * d z2 + star (c y6) * d z3 + star (c y13) * d z8 + star (c y12) * d z9 + star (c y15) * d z10 + star (c y14) * d z11 := by
  unfold offSum
  rw [incidence7]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl7_0, fl7_1, fl7_2, fl7_3, fl7_8, fl7_9, fl7_10, fl7_11]
  simp only [sg7_w0_0, sg7_w0_1, sg7_w0_2, sg7_w0_3, sg7_w0_8, sg7_w0_9, sg7_w0_10, sg7_w0_11, SixQubit.signMul_false]
  try ring

theorem ex7_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef7 w4 = star (c y5) * d z0 - star (c y4) * d z1 + star (c y7) * d z2 - star (c y6) * d z3 + star (c y13) * d z8 - star (c y12) * d z9 + star (c y15) * d z10 - star (c y14) * d z11 := by
  unfold offSum
  rw [incidence7]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl7_0, fl7_1, fl7_2, fl7_3, fl7_8, fl7_9, fl7_10, fl7_11]
  simp only [sg7_w4_0, sg7_w4_1, sg7_w4_2, sg7_w4_3, sg7_w4_8, sg7_w4_9, sg7_w4_10, sg7_w4_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex8_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef8 w0 = star (c y5) * d z4 + star (c y4) * d z5 + star (c y7) * d z6 + star (c y6) * d z7 + star (c y9) * d z8 + star (c y8) * d z9 + star (c y11) * d z10 + star (c y10) * d z11 := by
  unfold offSum
  rw [incidence8]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl8_4, fl8_5, fl8_6, fl8_7, fl8_8, fl8_9, fl8_10, fl8_11]
  simp only [sg8_w0_4, sg8_w0_5, sg8_w0_6, sg8_w0_7, sg8_w0_8, sg8_w0_9, sg8_w0_10, sg8_w0_11, SixQubit.signMul_false]
  try ring

theorem ex8_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef8 w4 = star (c y5) * d z4 - star (c y4) * d z5 + star (c y7) * d z6 - star (c y6) * d z7 + star (c y9) * d z8 - star (c y8) * d z9 + star (c y11) * d z10 - star (c y10) * d z11 := by
  unfold offSum
  rw [incidence8]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl8_4, fl8_5, fl8_6, fl8_7, fl8_8, fl8_9, fl8_10, fl8_11]
  simp only [sg8_w4_4, sg8_w4_5, sg8_w4_6, sg8_w4_7, sg8_w4_8, sg8_w4_9, sg8_w4_10, sg8_w4_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex9_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef9 w0 = star (c y8) * d z0 + star (c y9) * d z1 + star (c y10) * d z2 + star (c y11) * d z3 + star (c y12) * d z4 + star (c y13) * d z5 + star (c y14) * d z6 + star (c y15) * d z7 := by
  unfold offSum
  rw [incidence9]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl9_0, fl9_1, fl9_2, fl9_3, fl9_4, fl9_5, fl9_6, fl9_7]
  simp only [sg9_w0_0, sg9_w0_1, sg9_w0_2, sg9_w0_3, sg9_w0_4, sg9_w0_5, sg9_w0_6, sg9_w0_7, SixQubit.signMul_false]
  try ring

theorem ex9_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef9 w3 = star (c y8) * d z0 - star (c y9) * d z1 - star (c y10) * d z2 + star (c y11) * d z3 + star (c y12) * d z4 - star (c y13) * d z5 - star (c y14) * d z6 + star (c y15) * d z7 := by
  unfold offSum
  rw [incidence9]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl9_0, fl9_1, fl9_2, fl9_3, fl9_4, fl9_5, fl9_6, fl9_7]
  simp only [sg9_w3_0, sg9_w3_1, sg9_w3_2, sg9_w3_3, sg9_w3_4, sg9_w3_5, sg9_w3_6, sg9_w3_7, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex10_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef10 w0 = star (c y4) * d z0 + star (c y5) * d z1 + star (c y6) * d z2 + star (c y7) * d z3 + star (c y12) * d z8 + star (c y13) * d z9 + star (c y14) * d z10 + star (c y15) * d z11 := by
  unfold offSum
  rw [incidence10]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl10_0, fl10_1, fl10_2, fl10_3, fl10_8, fl10_9, fl10_10, fl10_11]
  simp only [sg10_w0_0, sg10_w0_1, sg10_w0_2, sg10_w0_3, sg10_w0_8, sg10_w0_9, sg10_w0_10, sg10_w0_11, SixQubit.signMul_false]
  try ring

theorem ex10_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef10 w3 = star (c y4) * d z0 - star (c y5) * d z1 - star (c y6) * d z2 + star (c y7) * d z3 + star (c y12) * d z8 - star (c y13) * d z9 - star (c y14) * d z10 + star (c y15) * d z11 := by
  unfold offSum
  rw [incidence10]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl10_0, fl10_1, fl10_2, fl10_3, fl10_8, fl10_9, fl10_10, fl10_11]
  simp only [sg10_w3_0, sg10_w3_1, sg10_w3_2, sg10_w3_3, sg10_w3_8, sg10_w3_9, sg10_w3_10, sg10_w3_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex11_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef11 w0 = star (c y4) * d z4 + star (c y5) * d z5 + star (c y6) * d z6 + star (c y7) * d z7 + star (c y8) * d z8 + star (c y9) * d z9 + star (c y10) * d z10 + star (c y11) * d z11 := by
  unfold offSum
  rw [incidence11]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl11_4, fl11_5, fl11_6, fl11_7, fl11_8, fl11_9, fl11_10, fl11_11]
  simp only [sg11_w0_4, sg11_w0_5, sg11_w0_6, sg11_w0_7, sg11_w0_8, sg11_w0_9, sg11_w0_10, sg11_w0_11, SixQubit.signMul_false]
  try ring

theorem ex11_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef11 w3 = star (c y4) * d z4 - star (c y5) * d z5 - star (c y6) * d z6 + star (c y7) * d z7 + star (c y8) * d z8 - star (c y9) * d z9 - star (c y10) * d z10 + star (c y11) * d z11 := by
  unfold offSum
  rw [incidence11]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl11_4, fl11_5, fl11_6, fl11_7, fl11_8, fl11_9, fl11_10, fl11_11]
  simp only [sg11_w3_4, sg11_w3_5, sg11_w3_6, sg11_w3_7, sg11_w3_8, sg11_w3_9, sg11_w3_10, sg11_w3_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

/-- Family two, mask 100100, columns (0, 1). -/
theorem fam2_0 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef3 w0 = 0)
    (h1 : offSum c d ef3 w5 = 0)
    : star (c y10) * d z0 + star (c y11) * d z1 + star (c y14) * d z4 + star (c y15) * d z5 = 0 := by
  rw [ex3_w0] at h0
  rw [ex3_w5] at h1
  linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- Family two, mask 100100, columns (2, 3). -/
theorem fam2_1 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef3 w0 = 0)
    (h1 : offSum c d ef3 w5 = 0)
    : star (c y8) * d z2 + star (c y9) * d z3 + star (c y12) * d z6 + star (c y13) * d z7 = 0 := by
  rw [ex3_w0] at h0
  rw [ex3_w5] at h1
  linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1

/-- Family two, mask 010100, columns (0, 1). -/
theorem fam2_2 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef4 w0 = 0)
    (h1 : offSum c d ef4 w5 = 0)
    : star (c y6) * d z0 + star (c y7) * d z1 + star (c y14) * d z8 + star (c y15) * d z9 = 0 := by
  rw [ex4_w0] at h0
  rw [ex4_w5] at h1
  linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- Family two, mask 010100, columns (2, 3). -/
theorem fam2_3 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef4 w0 = 0)
    (h1 : offSum c d ef4 w5 = 0)
    : star (c y4) * d z2 + star (c y5) * d z3 + star (c y12) * d z10 + star (c y13) * d z11 = 0 := by
  rw [ex4_w0] at h0
  rw [ex4_w5] at h1
  linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1

/-- Family two, mask 001100, columns (0, 1). -/
theorem fam2_4 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef5 w0 = 0)
    (h1 : offSum c d ef5 w5 = 0)
    : star (c y6) * d z4 + star (c y7) * d z5 + star (c y10) * d z8 + star (c y11) * d z9 = 0 := by
  rw [ex5_w0] at h0
  rw [ex5_w5] at h1
  linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- Family two, mask 001100, columns (2, 3). -/
theorem fam2_5 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef5 w0 = 0)
    (h1 : offSum c d ef5 w5 = 0)
    : star (c y4) * d z6 + star (c y5) * d z7 + star (c y8) * d z10 + star (c y9) * d z11 = 0 := by
  rw [ex5_w0] at h0
  rw [ex5_w5] at h1
  linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1

/-- Family two, mask 100010, columns (0, 2). -/
theorem fam2_6 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef6 w0 = 0)
    (h1 : offSum c d ef6 w4 = 0)
    : star (c y9) * d z0 + star (c y11) * d z2 + star (c y13) * d z4 + star (c y15) * d z6 = 0 := by
  rw [ex6_w0] at h0
  rw [ex6_w4] at h1
  linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- Family two, mask 100010, columns (1, 3). -/
theorem fam2_7 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef6 w0 = 0)
    (h1 : offSum c d ef6 w4 = 0)
    : star (c y8) * d z1 + star (c y10) * d z3 + star (c y12) * d z5 + star (c y14) * d z7 = 0 := by
  rw [ex6_w0] at h0
  rw [ex6_w4] at h1
  linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1

/-- Family two, mask 010010, columns (0, 2). -/
theorem fam2_8 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef7 w0 = 0)
    (h1 : offSum c d ef7 w4 = 0)
    : star (c y5) * d z0 + star (c y7) * d z2 + star (c y13) * d z8 + star (c y15) * d z10 = 0 := by
  rw [ex7_w0] at h0
  rw [ex7_w4] at h1
  linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- Family two, mask 010010, columns (1, 3). -/
theorem fam2_9 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef7 w0 = 0)
    (h1 : offSum c d ef7 w4 = 0)
    : star (c y4) * d z1 + star (c y6) * d z3 + star (c y12) * d z9 + star (c y14) * d z11 = 0 := by
  rw [ex7_w0] at h0
  rw [ex7_w4] at h1
  linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1

/-- Family two, mask 001010, columns (0, 2). -/
theorem fam2_10 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef8 w0 = 0)
    (h1 : offSum c d ef8 w4 = 0)
    : star (c y5) * d z4 + star (c y7) * d z6 + star (c y9) * d z8 + star (c y11) * d z10 = 0 := by
  rw [ex8_w0] at h0
  rw [ex8_w4] at h1
  linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- Family two, mask 001010, columns (1, 3). -/
theorem fam2_11 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef8 w0 = 0)
    (h1 : offSum c d ef8 w4 = 0)
    : star (c y4) * d z5 + star (c y6) * d z7 + star (c y8) * d z9 + star (c y10) * d z11 = 0 := by
  rw [ex8_w0] at h0
  rw [ex8_w4] at h1
  linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1

/-- Family two, mask 100001, columns (0, 3). -/
theorem fam2_12 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef9 w0 = 0)
    (h1 : offSum c d ef9 w3 = 0)
    : star (c y8) * d z0 + star (c y11) * d z3 + star (c y12) * d z4 + star (c y15) * d z7 = 0 := by
  rw [ex9_w0] at h0
  rw [ex9_w3] at h1
  linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- Family two, mask 100001, columns (1, 2). -/
theorem fam2_13 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef9 w0 = 0)
    (h1 : offSum c d ef9 w3 = 0)
    : star (c y9) * d z1 + star (c y10) * d z2 + star (c y13) * d z5 + star (c y14) * d z6 = 0 := by
  rw [ex9_w0] at h0
  rw [ex9_w3] at h1
  linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1

/-- Family two, mask 010001, columns (0, 3). -/
theorem fam2_14 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef10 w0 = 0)
    (h1 : offSum c d ef10 w3 = 0)
    : star (c y4) * d z0 + star (c y7) * d z3 + star (c y12) * d z8 + star (c y15) * d z11 = 0 := by
  rw [ex10_w0] at h0
  rw [ex10_w3] at h1
  linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- Family two, mask 010001, columns (1, 2). -/
theorem fam2_15 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef10 w0 = 0)
    (h1 : offSum c d ef10 w3 = 0)
    : star (c y5) * d z1 + star (c y6) * d z2 + star (c y13) * d z9 + star (c y14) * d z10 = 0 := by
  rw [ex10_w0] at h0
  rw [ex10_w3] at h1
  linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1

/-- Family two, mask 001001, columns (0, 3). -/
theorem fam2_16 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef11 w0 = 0)
    (h1 : offSum c d ef11 w3 = 0)
    : star (c y4) * d z4 + star (c y7) * d z7 + star (c y8) * d z8 + star (c y11) * d z11 = 0 := by
  rw [ex11_w0] at h0
  rw [ex11_w3] at h1
  linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- Family two, mask 001001, columns (1, 2). -/
theorem fam2_17 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef11 w0 = 0)
    (h1 : offSum c d ef11 w3 = 0)
    : star (c y5) * d z5 + star (c y6) * d z6 + star (c y9) * d z9 + star (c y10) * d z10 = 0 := by
  rw [ex11_w0] at h0
  rw [ex11_w3] at h1
  linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1


/-! ## Family three: the Klein-mask diagonal conditions -/

/-- `<0_L| X^e Z^z |0_L>` with the global prefactor omitted. -/
def diagBot (c : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ x ∈ S0.filter (fun x => SS.bxor x e ∈ S0),
      SixQubit.signMul (SS.bdot z x) (star (c (SS.bxor x e)) * c x)

/-- `<1_L| X^e Z^z |1_L>`. -/
def diagTop (d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S1),
      SixQubit.signMul (SS.bdot z y) (star (d (SS.bxor y e)) * d y)

def ef12 : SS.BitString 6 := bs false false false false true  true   -- Klein mask 000011
def ef13 : SS.BitString 6 := bs false false false true  false true   -- Klein mask 000101
def ef14 : SS.BitString 6 := bs false false false true  true  false  -- Klein mask 000110
def w6 : SS.BitString 6 := bs false false false false true  true   -- dressing 000011
def w7 : SS.BitString 6 := bs false false false true  false true   -- dressing 000101
def w8 : SS.BitString 6 := bs false false false true  true  false  -- dressing 000110

theorem diagB12 :
    S0.filter (fun x => SS.bxor x ef12 ∈ S0) = {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15} := by decide
theorem diagT12 :
    S1.filter (fun y => SS.bxor y ef12 ∈ S1) = {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15} := by decide
theorem dfb12_0 : SS.bxor y0 ef12 = y1 := by decide
theorem dfb12_1 : SS.bxor y1 ef12 = y0 := by decide
theorem dfb12_2 : SS.bxor y2 ef12 = y3 := by decide
theorem dfb12_3 : SS.bxor y3 ef12 = y2 := by decide
theorem dfb12_4 : SS.bxor y4 ef12 = y5 := by decide
theorem dfb12_5 : SS.bxor y5 ef12 = y4 := by decide
theorem dfb12_6 : SS.bxor y6 ef12 = y7 := by decide
theorem dfb12_7 : SS.bxor y7 ef12 = y6 := by decide
theorem dfb12_8 : SS.bxor y8 ef12 = y9 := by decide
theorem dfb12_9 : SS.bxor y9 ef12 = y8 := by decide
theorem dfb12_10 : SS.bxor y10 ef12 = y11 := by decide
theorem dfb12_11 : SS.bxor y11 ef12 = y10 := by decide
theorem dfb12_12 : SS.bxor y12 ef12 = y13 := by decide
theorem dfb12_13 : SS.bxor y13 ef12 = y12 := by decide
theorem dfb12_14 : SS.bxor y14 ef12 = y15 := by decide
theorem dfb12_15 : SS.bxor y15 ef12 = y14 := by decide
theorem dft12_0 : SS.bxor z0 ef12 = z1 := by decide
theorem dft12_1 : SS.bxor z1 ef12 = z0 := by decide
theorem dft12_2 : SS.bxor z2 ef12 = z3 := by decide
theorem dft12_3 : SS.bxor z3 ef12 = z2 := by decide
theorem dft12_4 : SS.bxor z4 ef12 = z5 := by decide
theorem dft12_5 : SS.bxor z5 ef12 = z4 := by decide
theorem dft12_6 : SS.bxor z6 ef12 = z7 := by decide
theorem dft12_7 : SS.bxor z7 ef12 = z6 := by decide
theorem dft12_8 : SS.bxor z8 ef12 = z9 := by decide
theorem dft12_9 : SS.bxor z9 ef12 = z8 := by decide
theorem dft12_10 : SS.bxor z10 ef12 = z11 := by decide
theorem dft12_11 : SS.bxor z11 ef12 = z10 := by decide
theorem dft12_12 : SS.bxor z12 ef12 = z13 := by decide
theorem dft12_13 : SS.bxor z13 ef12 = z12 := by decide
theorem dft12_14 : SS.bxor z14 ef12 = z15 := by decide
theorem dft12_15 : SS.bxor z15 ef12 = z14 := by decide
theorem dsb12_w0_0 : SS.bdot w0 y0 = false := by decide
theorem dsb12_w0_1 : SS.bdot w0 y1 = false := by decide
theorem dsb12_w0_2 : SS.bdot w0 y2 = false := by decide
theorem dsb12_w0_3 : SS.bdot w0 y3 = false := by decide
theorem dsb12_w0_4 : SS.bdot w0 y4 = false := by decide
theorem dsb12_w0_5 : SS.bdot w0 y5 = false := by decide
theorem dsb12_w0_6 : SS.bdot w0 y6 = false := by decide
theorem dsb12_w0_7 : SS.bdot w0 y7 = false := by decide
theorem dsb12_w0_8 : SS.bdot w0 y8 = false := by decide
theorem dsb12_w0_9 : SS.bdot w0 y9 = false := by decide
theorem dsb12_w0_10 : SS.bdot w0 y10 = false := by decide
theorem dsb12_w0_11 : SS.bdot w0 y11 = false := by decide
theorem dsb12_w0_12 : SS.bdot w0 y12 = false := by decide
theorem dsb12_w0_13 : SS.bdot w0 y13 = false := by decide
theorem dsb12_w0_14 : SS.bdot w0 y14 = false := by decide
theorem dsb12_w0_15 : SS.bdot w0 y15 = false := by decide
theorem dst12_w0_0 : SS.bdot w0 z0 = false := by decide
theorem dst12_w0_1 : SS.bdot w0 z1 = false := by decide
theorem dst12_w0_2 : SS.bdot w0 z2 = false := by decide
theorem dst12_w0_3 : SS.bdot w0 z3 = false := by decide
theorem dst12_w0_4 : SS.bdot w0 z4 = false := by decide
theorem dst12_w0_5 : SS.bdot w0 z5 = false := by decide
theorem dst12_w0_6 : SS.bdot w0 z6 = false := by decide
theorem dst12_w0_7 : SS.bdot w0 z7 = false := by decide
theorem dst12_w0_8 : SS.bdot w0 z8 = false := by decide
theorem dst12_w0_9 : SS.bdot w0 z9 = false := by decide
theorem dst12_w0_10 : SS.bdot w0 z10 = false := by decide
theorem dst12_w0_11 : SS.bdot w0 z11 = false := by decide
theorem dst12_w0_12 : SS.bdot w0 z12 = false := by decide
theorem dst12_w0_13 : SS.bdot w0 z13 = false := by decide
theorem dst12_w0_14 : SS.bdot w0 z14 = false := by decide
theorem dst12_w0_15 : SS.bdot w0 z15 = false := by decide
theorem dsb12_w4_0 : SS.bdot w4 y0 = false := by decide
theorem dsb12_w4_1 : SS.bdot w4 y1 = true := by decide
theorem dsb12_w4_2 : SS.bdot w4 y2 = false := by decide
theorem dsb12_w4_3 : SS.bdot w4 y3 = true := by decide
theorem dsb12_w4_4 : SS.bdot w4 y4 = false := by decide
theorem dsb12_w4_5 : SS.bdot w4 y5 = true := by decide
theorem dsb12_w4_6 : SS.bdot w4 y6 = false := by decide
theorem dsb12_w4_7 : SS.bdot w4 y7 = true := by decide
theorem dsb12_w4_8 : SS.bdot w4 y8 = false := by decide
theorem dsb12_w4_9 : SS.bdot w4 y9 = true := by decide
theorem dsb12_w4_10 : SS.bdot w4 y10 = false := by decide
theorem dsb12_w4_11 : SS.bdot w4 y11 = true := by decide
theorem dsb12_w4_12 : SS.bdot w4 y12 = false := by decide
theorem dsb12_w4_13 : SS.bdot w4 y13 = true := by decide
theorem dsb12_w4_14 : SS.bdot w4 y14 = false := by decide
theorem dsb12_w4_15 : SS.bdot w4 y15 = true := by decide
theorem dst12_w4_0 : SS.bdot w4 z0 = false := by decide
theorem dst12_w4_1 : SS.bdot w4 z1 = true := by decide
theorem dst12_w4_2 : SS.bdot w4 z2 = false := by decide
theorem dst12_w4_3 : SS.bdot w4 z3 = true := by decide
theorem dst12_w4_4 : SS.bdot w4 z4 = false := by decide
theorem dst12_w4_5 : SS.bdot w4 z5 = true := by decide
theorem dst12_w4_6 : SS.bdot w4 z6 = false := by decide
theorem dst12_w4_7 : SS.bdot w4 z7 = true := by decide
theorem dst12_w4_8 : SS.bdot w4 z8 = false := by decide
theorem dst12_w4_9 : SS.bdot w4 z9 = true := by decide
theorem dst12_w4_10 : SS.bdot w4 z10 = false := by decide
theorem dst12_w4_11 : SS.bdot w4 z11 = true := by decide
theorem dst12_w4_12 : SS.bdot w4 z12 = false := by decide
theorem dst12_w4_13 : SS.bdot w4 z13 = true := by decide
theorem dst12_w4_14 : SS.bdot w4 z14 = false := by decide
theorem dst12_w4_15 : SS.bdot w4 z15 = true := by decide
theorem dsb12_w3_0 : SS.bdot w3 y0 = false := by decide
theorem dsb12_w3_1 : SS.bdot w3 y1 = true := by decide
theorem dsb12_w3_2 : SS.bdot w3 y2 = true := by decide
theorem dsb12_w3_3 : SS.bdot w3 y3 = false := by decide
theorem dsb12_w3_4 : SS.bdot w3 y4 = true := by decide
theorem dsb12_w3_5 : SS.bdot w3 y5 = false := by decide
theorem dsb12_w3_6 : SS.bdot w3 y6 = false := by decide
theorem dsb12_w3_7 : SS.bdot w3 y7 = true := by decide
theorem dsb12_w3_8 : SS.bdot w3 y8 = true := by decide
theorem dsb12_w3_9 : SS.bdot w3 y9 = false := by decide
theorem dsb12_w3_10 : SS.bdot w3 y10 = false := by decide
theorem dsb12_w3_11 : SS.bdot w3 y11 = true := by decide
theorem dsb12_w3_12 : SS.bdot w3 y12 = true := by decide
theorem dsb12_w3_13 : SS.bdot w3 y13 = false := by decide
theorem dsb12_w3_14 : SS.bdot w3 y14 = false := by decide
theorem dsb12_w3_15 : SS.bdot w3 y15 = true := by decide
theorem dst12_w3_0 : SS.bdot w3 z0 = false := by decide
theorem dst12_w3_1 : SS.bdot w3 z1 = true := by decide
theorem dst12_w3_2 : SS.bdot w3 z2 = true := by decide
theorem dst12_w3_3 : SS.bdot w3 z3 = false := by decide
theorem dst12_w3_4 : SS.bdot w3 z4 = false := by decide
theorem dst12_w3_5 : SS.bdot w3 z5 = true := by decide
theorem dst12_w3_6 : SS.bdot w3 z6 = true := by decide
theorem dst12_w3_7 : SS.bdot w3 z7 = false := by decide
theorem dst12_w3_8 : SS.bdot w3 z8 = false := by decide
theorem dst12_w3_9 : SS.bdot w3 z9 = true := by decide
theorem dst12_w3_10 : SS.bdot w3 z10 = true := by decide
theorem dst12_w3_11 : SS.bdot w3 z11 = false := by decide
theorem dst12_w3_12 : SS.bdot w3 z12 = true := by decide
theorem dst12_w3_13 : SS.bdot w3 z13 = false := by decide
theorem dst12_w3_14 : SS.bdot w3 z14 = false := by decide
theorem dst12_w3_15 : SS.bdot w3 z15 = true := by decide
theorem dsb12_w6_0 : SS.bdot w6 y0 = false := by decide
theorem dsb12_w6_1 : SS.bdot w6 y1 = false := by decide
theorem dsb12_w6_2 : SS.bdot w6 y2 = true := by decide
theorem dsb12_w6_3 : SS.bdot w6 y3 = true := by decide
theorem dsb12_w6_4 : SS.bdot w6 y4 = true := by decide
theorem dsb12_w6_5 : SS.bdot w6 y5 = true := by decide
theorem dsb12_w6_6 : SS.bdot w6 y6 = false := by decide
theorem dsb12_w6_7 : SS.bdot w6 y7 = false := by decide
theorem dsb12_w6_8 : SS.bdot w6 y8 = true := by decide
theorem dsb12_w6_9 : SS.bdot w6 y9 = true := by decide
theorem dsb12_w6_10 : SS.bdot w6 y10 = false := by decide
theorem dsb12_w6_11 : SS.bdot w6 y11 = false := by decide
theorem dsb12_w6_12 : SS.bdot w6 y12 = true := by decide
theorem dsb12_w6_13 : SS.bdot w6 y13 = true := by decide
theorem dsb12_w6_14 : SS.bdot w6 y14 = false := by decide
theorem dsb12_w6_15 : SS.bdot w6 y15 = false := by decide
theorem dst12_w6_0 : SS.bdot w6 z0 = false := by decide
theorem dst12_w6_1 : SS.bdot w6 z1 = false := by decide
theorem dst12_w6_2 : SS.bdot w6 z2 = true := by decide
theorem dst12_w6_3 : SS.bdot w6 z3 = true := by decide
theorem dst12_w6_4 : SS.bdot w6 z4 = false := by decide
theorem dst12_w6_5 : SS.bdot w6 z5 = false := by decide
theorem dst12_w6_6 : SS.bdot w6 z6 = true := by decide
theorem dst12_w6_7 : SS.bdot w6 z7 = true := by decide
theorem dst12_w6_8 : SS.bdot w6 z8 = false := by decide
theorem dst12_w6_9 : SS.bdot w6 z9 = false := by decide
theorem dst12_w6_10 : SS.bdot w6 z10 = true := by decide
theorem dst12_w6_11 : SS.bdot w6 z11 = true := by decide
theorem dst12_w6_12 : SS.bdot w6 z12 = true := by decide
theorem dst12_w6_13 : SS.bdot w6 z13 = true := by decide
theorem dst12_w6_14 : SS.bdot w6 z14 = false := by decide
theorem dst12_w6_15 : SS.bdot w6 z15 = false := by decide
theorem diagB13 :
    S0.filter (fun x => SS.bxor x ef13 ∈ S0) = {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15} := by decide
theorem diagT13 :
    S1.filter (fun y => SS.bxor y ef13 ∈ S1) = {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15} := by decide
theorem dfb13_0 : SS.bxor y0 ef13 = y2 := by decide
theorem dfb13_1 : SS.bxor y1 ef13 = y3 := by decide
theorem dfb13_2 : SS.bxor y2 ef13 = y0 := by decide
theorem dfb13_3 : SS.bxor y3 ef13 = y1 := by decide
theorem dfb13_4 : SS.bxor y4 ef13 = y6 := by decide
theorem dfb13_5 : SS.bxor y5 ef13 = y7 := by decide
theorem dfb13_6 : SS.bxor y6 ef13 = y4 := by decide
theorem dfb13_7 : SS.bxor y7 ef13 = y5 := by decide
theorem dfb13_8 : SS.bxor y8 ef13 = y10 := by decide
theorem dfb13_9 : SS.bxor y9 ef13 = y11 := by decide
theorem dfb13_10 : SS.bxor y10 ef13 = y8 := by decide
theorem dfb13_11 : SS.bxor y11 ef13 = y9 := by decide
theorem dfb13_12 : SS.bxor y12 ef13 = y14 := by decide
theorem dfb13_13 : SS.bxor y13 ef13 = y15 := by decide
theorem dfb13_14 : SS.bxor y14 ef13 = y12 := by decide
theorem dfb13_15 : SS.bxor y15 ef13 = y13 := by decide
theorem dft13_0 : SS.bxor z0 ef13 = z2 := by decide
theorem dft13_1 : SS.bxor z1 ef13 = z3 := by decide
theorem dft13_2 : SS.bxor z2 ef13 = z0 := by decide
theorem dft13_3 : SS.bxor z3 ef13 = z1 := by decide
theorem dft13_4 : SS.bxor z4 ef13 = z6 := by decide
theorem dft13_5 : SS.bxor z5 ef13 = z7 := by decide
theorem dft13_6 : SS.bxor z6 ef13 = z4 := by decide
theorem dft13_7 : SS.bxor z7 ef13 = z5 := by decide
theorem dft13_8 : SS.bxor z8 ef13 = z10 := by decide
theorem dft13_9 : SS.bxor z9 ef13 = z11 := by decide
theorem dft13_10 : SS.bxor z10 ef13 = z8 := by decide
theorem dft13_11 : SS.bxor z11 ef13 = z9 := by decide
theorem dft13_12 : SS.bxor z12 ef13 = z14 := by decide
theorem dft13_13 : SS.bxor z13 ef13 = z15 := by decide
theorem dft13_14 : SS.bxor z14 ef13 = z12 := by decide
theorem dft13_15 : SS.bxor z15 ef13 = z13 := by decide
theorem dsb13_w0_0 : SS.bdot w0 y0 = false := by decide
theorem dsb13_w0_1 : SS.bdot w0 y1 = false := by decide
theorem dsb13_w0_2 : SS.bdot w0 y2 = false := by decide
theorem dsb13_w0_3 : SS.bdot w0 y3 = false := by decide
theorem dsb13_w0_4 : SS.bdot w0 y4 = false := by decide
theorem dsb13_w0_5 : SS.bdot w0 y5 = false := by decide
theorem dsb13_w0_6 : SS.bdot w0 y6 = false := by decide
theorem dsb13_w0_7 : SS.bdot w0 y7 = false := by decide
theorem dsb13_w0_8 : SS.bdot w0 y8 = false := by decide
theorem dsb13_w0_9 : SS.bdot w0 y9 = false := by decide
theorem dsb13_w0_10 : SS.bdot w0 y10 = false := by decide
theorem dsb13_w0_11 : SS.bdot w0 y11 = false := by decide
theorem dsb13_w0_12 : SS.bdot w0 y12 = false := by decide
theorem dsb13_w0_13 : SS.bdot w0 y13 = false := by decide
theorem dsb13_w0_14 : SS.bdot w0 y14 = false := by decide
theorem dsb13_w0_15 : SS.bdot w0 y15 = false := by decide
theorem dst13_w0_0 : SS.bdot w0 z0 = false := by decide
theorem dst13_w0_1 : SS.bdot w0 z1 = false := by decide
theorem dst13_w0_2 : SS.bdot w0 z2 = false := by decide
theorem dst13_w0_3 : SS.bdot w0 z3 = false := by decide
theorem dst13_w0_4 : SS.bdot w0 z4 = false := by decide
theorem dst13_w0_5 : SS.bdot w0 z5 = false := by decide
theorem dst13_w0_6 : SS.bdot w0 z6 = false := by decide
theorem dst13_w0_7 : SS.bdot w0 z7 = false := by decide
theorem dst13_w0_8 : SS.bdot w0 z8 = false := by decide
theorem dst13_w0_9 : SS.bdot w0 z9 = false := by decide
theorem dst13_w0_10 : SS.bdot w0 z10 = false := by decide
theorem dst13_w0_11 : SS.bdot w0 z11 = false := by decide
theorem dst13_w0_12 : SS.bdot w0 z12 = false := by decide
theorem dst13_w0_13 : SS.bdot w0 z13 = false := by decide
theorem dst13_w0_14 : SS.bdot w0 z14 = false := by decide
theorem dst13_w0_15 : SS.bdot w0 z15 = false := by decide
theorem dsb13_w5_0 : SS.bdot w5 y0 = false := by decide
theorem dsb13_w5_1 : SS.bdot w5 y1 = false := by decide
theorem dsb13_w5_2 : SS.bdot w5 y2 = true := by decide
theorem dsb13_w5_3 : SS.bdot w5 y3 = true := by decide
theorem dsb13_w5_4 : SS.bdot w5 y4 = false := by decide
theorem dsb13_w5_5 : SS.bdot w5 y5 = false := by decide
theorem dsb13_w5_6 : SS.bdot w5 y6 = true := by decide
theorem dsb13_w5_7 : SS.bdot w5 y7 = true := by decide
theorem dsb13_w5_8 : SS.bdot w5 y8 = false := by decide
theorem dsb13_w5_9 : SS.bdot w5 y9 = false := by decide
theorem dsb13_w5_10 : SS.bdot w5 y10 = true := by decide
theorem dsb13_w5_11 : SS.bdot w5 y11 = true := by decide
theorem dsb13_w5_12 : SS.bdot w5 y12 = false := by decide
theorem dsb13_w5_13 : SS.bdot w5 y13 = false := by decide
theorem dsb13_w5_14 : SS.bdot w5 y14 = true := by decide
theorem dsb13_w5_15 : SS.bdot w5 y15 = true := by decide
theorem dst13_w5_0 : SS.bdot w5 z0 = false := by decide
theorem dst13_w5_1 : SS.bdot w5 z1 = false := by decide
theorem dst13_w5_2 : SS.bdot w5 z2 = true := by decide
theorem dst13_w5_3 : SS.bdot w5 z3 = true := by decide
theorem dst13_w5_4 : SS.bdot w5 z4 = false := by decide
theorem dst13_w5_5 : SS.bdot w5 z5 = false := by decide
theorem dst13_w5_6 : SS.bdot w5 z6 = true := by decide
theorem dst13_w5_7 : SS.bdot w5 z7 = true := by decide
theorem dst13_w5_8 : SS.bdot w5 z8 = false := by decide
theorem dst13_w5_9 : SS.bdot w5 z9 = false := by decide
theorem dst13_w5_10 : SS.bdot w5 z10 = true := by decide
theorem dst13_w5_11 : SS.bdot w5 z11 = true := by decide
theorem dst13_w5_12 : SS.bdot w5 z12 = false := by decide
theorem dst13_w5_13 : SS.bdot w5 z13 = false := by decide
theorem dst13_w5_14 : SS.bdot w5 z14 = true := by decide
theorem dst13_w5_15 : SS.bdot w5 z15 = true := by decide
theorem dsb13_w3_0 : SS.bdot w3 y0 = false := by decide
theorem dsb13_w3_1 : SS.bdot w3 y1 = true := by decide
theorem dsb13_w3_2 : SS.bdot w3 y2 = true := by decide
theorem dsb13_w3_3 : SS.bdot w3 y3 = false := by decide
theorem dsb13_w3_4 : SS.bdot w3 y4 = true := by decide
theorem dsb13_w3_5 : SS.bdot w3 y5 = false := by decide
theorem dsb13_w3_6 : SS.bdot w3 y6 = false := by decide
theorem dsb13_w3_7 : SS.bdot w3 y7 = true := by decide
theorem dsb13_w3_8 : SS.bdot w3 y8 = true := by decide
theorem dsb13_w3_9 : SS.bdot w3 y9 = false := by decide
theorem dsb13_w3_10 : SS.bdot w3 y10 = false := by decide
theorem dsb13_w3_11 : SS.bdot w3 y11 = true := by decide
theorem dsb13_w3_12 : SS.bdot w3 y12 = true := by decide
theorem dsb13_w3_13 : SS.bdot w3 y13 = false := by decide
theorem dsb13_w3_14 : SS.bdot w3 y14 = false := by decide
theorem dsb13_w3_15 : SS.bdot w3 y15 = true := by decide
theorem dst13_w3_0 : SS.bdot w3 z0 = false := by decide
theorem dst13_w3_1 : SS.bdot w3 z1 = true := by decide
theorem dst13_w3_2 : SS.bdot w3 z2 = true := by decide
theorem dst13_w3_3 : SS.bdot w3 z3 = false := by decide
theorem dst13_w3_4 : SS.bdot w3 z4 = false := by decide
theorem dst13_w3_5 : SS.bdot w3 z5 = true := by decide
theorem dst13_w3_6 : SS.bdot w3 z6 = true := by decide
theorem dst13_w3_7 : SS.bdot w3 z7 = false := by decide
theorem dst13_w3_8 : SS.bdot w3 z8 = false := by decide
theorem dst13_w3_9 : SS.bdot w3 z9 = true := by decide
theorem dst13_w3_10 : SS.bdot w3 z10 = true := by decide
theorem dst13_w3_11 : SS.bdot w3 z11 = false := by decide
theorem dst13_w3_12 : SS.bdot w3 z12 = true := by decide
theorem dst13_w3_13 : SS.bdot w3 z13 = false := by decide
theorem dst13_w3_14 : SS.bdot w3 z14 = false := by decide
theorem dst13_w3_15 : SS.bdot w3 z15 = true := by decide
theorem dsb13_w7_0 : SS.bdot w7 y0 = false := by decide
theorem dsb13_w7_1 : SS.bdot w7 y1 = true := by decide
theorem dsb13_w7_2 : SS.bdot w7 y2 = false := by decide
theorem dsb13_w7_3 : SS.bdot w7 y3 = true := by decide
theorem dsb13_w7_4 : SS.bdot w7 y4 = true := by decide
theorem dsb13_w7_5 : SS.bdot w7 y5 = false := by decide
theorem dsb13_w7_6 : SS.bdot w7 y6 = true := by decide
theorem dsb13_w7_7 : SS.bdot w7 y7 = false := by decide
theorem dsb13_w7_8 : SS.bdot w7 y8 = true := by decide
theorem dsb13_w7_9 : SS.bdot w7 y9 = false := by decide
theorem dsb13_w7_10 : SS.bdot w7 y10 = true := by decide
theorem dsb13_w7_11 : SS.bdot w7 y11 = false := by decide
theorem dsb13_w7_12 : SS.bdot w7 y12 = true := by decide
theorem dsb13_w7_13 : SS.bdot w7 y13 = false := by decide
theorem dsb13_w7_14 : SS.bdot w7 y14 = true := by decide
theorem dsb13_w7_15 : SS.bdot w7 y15 = false := by decide
theorem dst13_w7_0 : SS.bdot w7 z0 = false := by decide
theorem dst13_w7_1 : SS.bdot w7 z1 = true := by decide
theorem dst13_w7_2 : SS.bdot w7 z2 = false := by decide
theorem dst13_w7_3 : SS.bdot w7 z3 = true := by decide
theorem dst13_w7_4 : SS.bdot w7 z4 = false := by decide
theorem dst13_w7_5 : SS.bdot w7 z5 = true := by decide
theorem dst13_w7_6 : SS.bdot w7 z6 = false := by decide
theorem dst13_w7_7 : SS.bdot w7 z7 = true := by decide
theorem dst13_w7_8 : SS.bdot w7 z8 = false := by decide
theorem dst13_w7_9 : SS.bdot w7 z9 = true := by decide
theorem dst13_w7_10 : SS.bdot w7 z10 = false := by decide
theorem dst13_w7_11 : SS.bdot w7 z11 = true := by decide
theorem dst13_w7_12 : SS.bdot w7 z12 = true := by decide
theorem dst13_w7_13 : SS.bdot w7 z13 = false := by decide
theorem dst13_w7_14 : SS.bdot w7 z14 = true := by decide
theorem dst13_w7_15 : SS.bdot w7 z15 = false := by decide
theorem diagB14 :
    S0.filter (fun x => SS.bxor x ef14 ∈ S0) = {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15} := by decide
theorem diagT14 :
    S1.filter (fun y => SS.bxor y ef14 ∈ S1) = {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15} := by decide
theorem dfb14_0 : SS.bxor y0 ef14 = y3 := by decide
theorem dfb14_1 : SS.bxor y1 ef14 = y2 := by decide
theorem dfb14_2 : SS.bxor y2 ef14 = y1 := by decide
theorem dfb14_3 : SS.bxor y3 ef14 = y0 := by decide
theorem dfb14_4 : SS.bxor y4 ef14 = y7 := by decide
theorem dfb14_5 : SS.bxor y5 ef14 = y6 := by decide
theorem dfb14_6 : SS.bxor y6 ef14 = y5 := by decide
theorem dfb14_7 : SS.bxor y7 ef14 = y4 := by decide
theorem dfb14_8 : SS.bxor y8 ef14 = y11 := by decide
theorem dfb14_9 : SS.bxor y9 ef14 = y10 := by decide
theorem dfb14_10 : SS.bxor y10 ef14 = y9 := by decide
theorem dfb14_11 : SS.bxor y11 ef14 = y8 := by decide
theorem dfb14_12 : SS.bxor y12 ef14 = y15 := by decide
theorem dfb14_13 : SS.bxor y13 ef14 = y14 := by decide
theorem dfb14_14 : SS.bxor y14 ef14 = y13 := by decide
theorem dfb14_15 : SS.bxor y15 ef14 = y12 := by decide
theorem dft14_0 : SS.bxor z0 ef14 = z3 := by decide
theorem dft14_1 : SS.bxor z1 ef14 = z2 := by decide
theorem dft14_2 : SS.bxor z2 ef14 = z1 := by decide
theorem dft14_3 : SS.bxor z3 ef14 = z0 := by decide
theorem dft14_4 : SS.bxor z4 ef14 = z7 := by decide
theorem dft14_5 : SS.bxor z5 ef14 = z6 := by decide
theorem dft14_6 : SS.bxor z6 ef14 = z5 := by decide
theorem dft14_7 : SS.bxor z7 ef14 = z4 := by decide
theorem dft14_8 : SS.bxor z8 ef14 = z11 := by decide
theorem dft14_9 : SS.bxor z9 ef14 = z10 := by decide
theorem dft14_10 : SS.bxor z10 ef14 = z9 := by decide
theorem dft14_11 : SS.bxor z11 ef14 = z8 := by decide
theorem dft14_12 : SS.bxor z12 ef14 = z15 := by decide
theorem dft14_13 : SS.bxor z13 ef14 = z14 := by decide
theorem dft14_14 : SS.bxor z14 ef14 = z13 := by decide
theorem dft14_15 : SS.bxor z15 ef14 = z12 := by decide
theorem dsb14_w0_0 : SS.bdot w0 y0 = false := by decide
theorem dsb14_w0_1 : SS.bdot w0 y1 = false := by decide
theorem dsb14_w0_2 : SS.bdot w0 y2 = false := by decide
theorem dsb14_w0_3 : SS.bdot w0 y3 = false := by decide
theorem dsb14_w0_4 : SS.bdot w0 y4 = false := by decide
theorem dsb14_w0_5 : SS.bdot w0 y5 = false := by decide
theorem dsb14_w0_6 : SS.bdot w0 y6 = false := by decide
theorem dsb14_w0_7 : SS.bdot w0 y7 = false := by decide
theorem dsb14_w0_8 : SS.bdot w0 y8 = false := by decide
theorem dsb14_w0_9 : SS.bdot w0 y9 = false := by decide
theorem dsb14_w0_10 : SS.bdot w0 y10 = false := by decide
theorem dsb14_w0_11 : SS.bdot w0 y11 = false := by decide
theorem dsb14_w0_12 : SS.bdot w0 y12 = false := by decide
theorem dsb14_w0_13 : SS.bdot w0 y13 = false := by decide
theorem dsb14_w0_14 : SS.bdot w0 y14 = false := by decide
theorem dsb14_w0_15 : SS.bdot w0 y15 = false := by decide
theorem dst14_w0_0 : SS.bdot w0 z0 = false := by decide
theorem dst14_w0_1 : SS.bdot w0 z1 = false := by decide
theorem dst14_w0_2 : SS.bdot w0 z2 = false := by decide
theorem dst14_w0_3 : SS.bdot w0 z3 = false := by decide
theorem dst14_w0_4 : SS.bdot w0 z4 = false := by decide
theorem dst14_w0_5 : SS.bdot w0 z5 = false := by decide
theorem dst14_w0_6 : SS.bdot w0 z6 = false := by decide
theorem dst14_w0_7 : SS.bdot w0 z7 = false := by decide
theorem dst14_w0_8 : SS.bdot w0 z8 = false := by decide
theorem dst14_w0_9 : SS.bdot w0 z9 = false := by decide
theorem dst14_w0_10 : SS.bdot w0 z10 = false := by decide
theorem dst14_w0_11 : SS.bdot w0 z11 = false := by decide
theorem dst14_w0_12 : SS.bdot w0 z12 = false := by decide
theorem dst14_w0_13 : SS.bdot w0 z13 = false := by decide
theorem dst14_w0_14 : SS.bdot w0 z14 = false := by decide
theorem dst14_w0_15 : SS.bdot w0 z15 = false := by decide
theorem dsb14_w5_0 : SS.bdot w5 y0 = false := by decide
theorem dsb14_w5_1 : SS.bdot w5 y1 = false := by decide
theorem dsb14_w5_2 : SS.bdot w5 y2 = true := by decide
theorem dsb14_w5_3 : SS.bdot w5 y3 = true := by decide
theorem dsb14_w5_4 : SS.bdot w5 y4 = false := by decide
theorem dsb14_w5_5 : SS.bdot w5 y5 = false := by decide
theorem dsb14_w5_6 : SS.bdot w5 y6 = true := by decide
theorem dsb14_w5_7 : SS.bdot w5 y7 = true := by decide
theorem dsb14_w5_8 : SS.bdot w5 y8 = false := by decide
theorem dsb14_w5_9 : SS.bdot w5 y9 = false := by decide
theorem dsb14_w5_10 : SS.bdot w5 y10 = true := by decide
theorem dsb14_w5_11 : SS.bdot w5 y11 = true := by decide
theorem dsb14_w5_12 : SS.bdot w5 y12 = false := by decide
theorem dsb14_w5_13 : SS.bdot w5 y13 = false := by decide
theorem dsb14_w5_14 : SS.bdot w5 y14 = true := by decide
theorem dsb14_w5_15 : SS.bdot w5 y15 = true := by decide
theorem dst14_w5_0 : SS.bdot w5 z0 = false := by decide
theorem dst14_w5_1 : SS.bdot w5 z1 = false := by decide
theorem dst14_w5_2 : SS.bdot w5 z2 = true := by decide
theorem dst14_w5_3 : SS.bdot w5 z3 = true := by decide
theorem dst14_w5_4 : SS.bdot w5 z4 = false := by decide
theorem dst14_w5_5 : SS.bdot w5 z5 = false := by decide
theorem dst14_w5_6 : SS.bdot w5 z6 = true := by decide
theorem dst14_w5_7 : SS.bdot w5 z7 = true := by decide
theorem dst14_w5_8 : SS.bdot w5 z8 = false := by decide
theorem dst14_w5_9 : SS.bdot w5 z9 = false := by decide
theorem dst14_w5_10 : SS.bdot w5 z10 = true := by decide
theorem dst14_w5_11 : SS.bdot w5 z11 = true := by decide
theorem dst14_w5_12 : SS.bdot w5 z12 = false := by decide
theorem dst14_w5_13 : SS.bdot w5 z13 = false := by decide
theorem dst14_w5_14 : SS.bdot w5 z14 = true := by decide
theorem dst14_w5_15 : SS.bdot w5 z15 = true := by decide
theorem dsb14_w4_0 : SS.bdot w4 y0 = false := by decide
theorem dsb14_w4_1 : SS.bdot w4 y1 = true := by decide
theorem dsb14_w4_2 : SS.bdot w4 y2 = false := by decide
theorem dsb14_w4_3 : SS.bdot w4 y3 = true := by decide
theorem dsb14_w4_4 : SS.bdot w4 y4 = false := by decide
theorem dsb14_w4_5 : SS.bdot w4 y5 = true := by decide
theorem dsb14_w4_6 : SS.bdot w4 y6 = false := by decide
theorem dsb14_w4_7 : SS.bdot w4 y7 = true := by decide
theorem dsb14_w4_8 : SS.bdot w4 y8 = false := by decide
theorem dsb14_w4_9 : SS.bdot w4 y9 = true := by decide
theorem dsb14_w4_10 : SS.bdot w4 y10 = false := by decide
theorem dsb14_w4_11 : SS.bdot w4 y11 = true := by decide
theorem dsb14_w4_12 : SS.bdot w4 y12 = false := by decide
theorem dsb14_w4_13 : SS.bdot w4 y13 = true := by decide
theorem dsb14_w4_14 : SS.bdot w4 y14 = false := by decide
theorem dsb14_w4_15 : SS.bdot w4 y15 = true := by decide
theorem dst14_w4_0 : SS.bdot w4 z0 = false := by decide
theorem dst14_w4_1 : SS.bdot w4 z1 = true := by decide
theorem dst14_w4_2 : SS.bdot w4 z2 = false := by decide
theorem dst14_w4_3 : SS.bdot w4 z3 = true := by decide
theorem dst14_w4_4 : SS.bdot w4 z4 = false := by decide
theorem dst14_w4_5 : SS.bdot w4 z5 = true := by decide
theorem dst14_w4_6 : SS.bdot w4 z6 = false := by decide
theorem dst14_w4_7 : SS.bdot w4 z7 = true := by decide
theorem dst14_w4_8 : SS.bdot w4 z8 = false := by decide
theorem dst14_w4_9 : SS.bdot w4 z9 = true := by decide
theorem dst14_w4_10 : SS.bdot w4 z10 = false := by decide
theorem dst14_w4_11 : SS.bdot w4 z11 = true := by decide
theorem dst14_w4_12 : SS.bdot w4 z12 = false := by decide
theorem dst14_w4_13 : SS.bdot w4 z13 = true := by decide
theorem dst14_w4_14 : SS.bdot w4 z14 = false := by decide
theorem dst14_w4_15 : SS.bdot w4 z15 = true := by decide
theorem dsb14_w8_0 : SS.bdot w8 y0 = false := by decide
theorem dsb14_w8_1 : SS.bdot w8 y1 = true := by decide
theorem dsb14_w8_2 : SS.bdot w8 y2 = true := by decide
theorem dsb14_w8_3 : SS.bdot w8 y3 = false := by decide
theorem dsb14_w8_4 : SS.bdot w8 y4 = false := by decide
theorem dsb14_w8_5 : SS.bdot w8 y5 = true := by decide
theorem dsb14_w8_6 : SS.bdot w8 y6 = true := by decide
theorem dsb14_w8_7 : SS.bdot w8 y7 = false := by decide
theorem dsb14_w8_8 : SS.bdot w8 y8 = false := by decide
theorem dsb14_w8_9 : SS.bdot w8 y9 = true := by decide
theorem dsb14_w8_10 : SS.bdot w8 y10 = true := by decide
theorem dsb14_w8_11 : SS.bdot w8 y11 = false := by decide
theorem dsb14_w8_12 : SS.bdot w8 y12 = false := by decide
theorem dsb14_w8_13 : SS.bdot w8 y13 = true := by decide
theorem dsb14_w8_14 : SS.bdot w8 y14 = true := by decide
theorem dsb14_w8_15 : SS.bdot w8 y15 = false := by decide
theorem dst14_w8_0 : SS.bdot w8 z0 = false := by decide
theorem dst14_w8_1 : SS.bdot w8 z1 = true := by decide
theorem dst14_w8_2 : SS.bdot w8 z2 = true := by decide
theorem dst14_w8_3 : SS.bdot w8 z3 = false := by decide
theorem dst14_w8_4 : SS.bdot w8 z4 = false := by decide
theorem dst14_w8_5 : SS.bdot w8 z5 = true := by decide
theorem dst14_w8_6 : SS.bdot w8 z6 = true := by decide
theorem dst14_w8_7 : SS.bdot w8 z7 = false := by decide
theorem dst14_w8_8 : SS.bdot w8 z8 = false := by decide
theorem dst14_w8_9 : SS.bdot w8 z9 = true := by decide
theorem dst14_w8_10 : SS.bdot w8 z10 = true := by decide
theorem dst14_w8_11 : SS.bdot w8 z11 = false := by decide
theorem dst14_w8_12 : SS.bdot w8 z12 = false := by decide
theorem dst14_w8_13 : SS.bdot w8 z13 = true := by decide
theorem dst14_w8_14 : SS.bdot w8 z14 = true := by decide
theorem dst14_w8_15 : SS.bdot w8 z15 = false := by decide

theorem dbot12_w0 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef12 w0 = star (c y1) * c y0 + star (c y0) * c y1 + star (c y3) * c y2 + star (c y2) * c y3 + star (c y5) * c y4 + star (c y4) * c y5 + star (c y7) * c y6 + star (c y6) * c y7 + star (c y9) * c y8 + star (c y8) * c y9 + star (c y11) * c y10 + star (c y10) * c y11 + star (c y13) * c y12 + star (c y12) * c y13 + star (c y15) * c y14 + star (c y14) * c y15 := by
  unfold diagBot
  rw [diagB12]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfb12_0, dfb12_1, dfb12_2, dfb12_3, dfb12_4, dfb12_5, dfb12_6, dfb12_7, dfb12_8, dfb12_9, dfb12_10, dfb12_11, dfb12_12, dfb12_13, dfb12_14, dfb12_15]
  simp only [dsb12_w0_0, dsb12_w0_1, dsb12_w0_2, dsb12_w0_3, dsb12_w0_4, dsb12_w0_5, dsb12_w0_6, dsb12_w0_7, dsb12_w0_8, dsb12_w0_9, dsb12_w0_10, dsb12_w0_11, dsb12_w0_12, dsb12_w0_13, dsb12_w0_14, dsb12_w0_15, SixQubit.signMul_false]
  try ring

theorem dtop12_w0 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef12 w0 = star (d z1) * d z0 + star (d z0) * d z1 + star (d z3) * d z2 + star (d z2) * d z3 + star (d z5) * d z4 + star (d z4) * d z5 + star (d z7) * d z6 + star (d z6) * d z7 + star (d z9) * d z8 + star (d z8) * d z9 + star (d z11) * d z10 + star (d z10) * d z11 + star (d z13) * d z12 + star (d z12) * d z13 + star (d z15) * d z14 + star (d z14) * d z15 := by
  unfold diagTop
  rw [diagT12]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dft12_0, dft12_1, dft12_2, dft12_3, dft12_4, dft12_5, dft12_6, dft12_7, dft12_8, dft12_9, dft12_10, dft12_11, dft12_12, dft12_13, dft12_14, dft12_15]
  simp only [dst12_w0_0, dst12_w0_1, dst12_w0_2, dst12_w0_3, dst12_w0_4, dst12_w0_5, dst12_w0_6, dst12_w0_7, dst12_w0_8, dst12_w0_9, dst12_w0_10, dst12_w0_11, dst12_w0_12, dst12_w0_13, dst12_w0_14, dst12_w0_15, SixQubit.signMul_false]
  try ring

theorem dbot12_w4 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef12 w4 = star (c y1) * c y0 - star (c y0) * c y1 + star (c y3) * c y2 - star (c y2) * c y3 + star (c y5) * c y4 - star (c y4) * c y5 + star (c y7) * c y6 - star (c y6) * c y7 + star (c y9) * c y8 - star (c y8) * c y9 + star (c y11) * c y10 - star (c y10) * c y11 + star (c y13) * c y12 - star (c y12) * c y13 + star (c y15) * c y14 - star (c y14) * c y15 := by
  unfold diagBot
  rw [diagB12]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfb12_0, dfb12_1, dfb12_2, dfb12_3, dfb12_4, dfb12_5, dfb12_6, dfb12_7, dfb12_8, dfb12_9, dfb12_10, dfb12_11, dfb12_12, dfb12_13, dfb12_14, dfb12_15]
  simp only [dsb12_w4_0, dsb12_w4_1, dsb12_w4_2, dsb12_w4_3, dsb12_w4_4, dsb12_w4_5, dsb12_w4_6, dsb12_w4_7, dsb12_w4_8, dsb12_w4_9, dsb12_w4_10, dsb12_w4_11, dsb12_w4_12, dsb12_w4_13, dsb12_w4_14, dsb12_w4_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dtop12_w4 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef12 w4 = star (d z1) * d z0 - star (d z0) * d z1 + star (d z3) * d z2 - star (d z2) * d z3 + star (d z5) * d z4 - star (d z4) * d z5 + star (d z7) * d z6 - star (d z6) * d z7 + star (d z9) * d z8 - star (d z8) * d z9 + star (d z11) * d z10 - star (d z10) * d z11 + star (d z13) * d z12 - star (d z12) * d z13 + star (d z15) * d z14 - star (d z14) * d z15 := by
  unfold diagTop
  rw [diagT12]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dft12_0, dft12_1, dft12_2, dft12_3, dft12_4, dft12_5, dft12_6, dft12_7, dft12_8, dft12_9, dft12_10, dft12_11, dft12_12, dft12_13, dft12_14, dft12_15]
  simp only [dst12_w4_0, dst12_w4_1, dst12_w4_2, dst12_w4_3, dst12_w4_4, dst12_w4_5, dst12_w4_6, dst12_w4_7, dst12_w4_8, dst12_w4_9, dst12_w4_10, dst12_w4_11, dst12_w4_12, dst12_w4_13, dst12_w4_14, dst12_w4_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dbot12_w3 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef12 w3 = star (c y1) * c y0 - star (c y0) * c y1 - star (c y3) * c y2 + star (c y2) * c y3 - star (c y5) * c y4 + star (c y4) * c y5 + star (c y7) * c y6 - star (c y6) * c y7 - star (c y9) * c y8 + star (c y8) * c y9 + star (c y11) * c y10 - star (c y10) * c y11 - star (c y13) * c y12 + star (c y12) * c y13 + star (c y15) * c y14 - star (c y14) * c y15 := by
  unfold diagBot
  rw [diagB12]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfb12_0, dfb12_1, dfb12_2, dfb12_3, dfb12_4, dfb12_5, dfb12_6, dfb12_7, dfb12_8, dfb12_9, dfb12_10, dfb12_11, dfb12_12, dfb12_13, dfb12_14, dfb12_15]
  simp only [dsb12_w3_0, dsb12_w3_1, dsb12_w3_2, dsb12_w3_3, dsb12_w3_4, dsb12_w3_5, dsb12_w3_6, dsb12_w3_7, dsb12_w3_8, dsb12_w3_9, dsb12_w3_10, dsb12_w3_11, dsb12_w3_12, dsb12_w3_13, dsb12_w3_14, dsb12_w3_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dtop12_w3 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef12 w3 = star (d z1) * d z0 - star (d z0) * d z1 - star (d z3) * d z2 + star (d z2) * d z3 + star (d z5) * d z4 - star (d z4) * d z5 - star (d z7) * d z6 + star (d z6) * d z7 + star (d z9) * d z8 - star (d z8) * d z9 - star (d z11) * d z10 + star (d z10) * d z11 - star (d z13) * d z12 + star (d z12) * d z13 + star (d z15) * d z14 - star (d z14) * d z15 := by
  unfold diagTop
  rw [diagT12]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dft12_0, dft12_1, dft12_2, dft12_3, dft12_4, dft12_5, dft12_6, dft12_7, dft12_8, dft12_9, dft12_10, dft12_11, dft12_12, dft12_13, dft12_14, dft12_15]
  simp only [dst12_w3_0, dst12_w3_1, dst12_w3_2, dst12_w3_3, dst12_w3_4, dst12_w3_5, dst12_w3_6, dst12_w3_7, dst12_w3_8, dst12_w3_9, dst12_w3_10, dst12_w3_11, dst12_w3_12, dst12_w3_13, dst12_w3_14, dst12_w3_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dbot12_w6 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef12 w6 = star (c y1) * c y0 + star (c y0) * c y1 - star (c y3) * c y2 - star (c y2) * c y3 - star (c y5) * c y4 - star (c y4) * c y5 + star (c y7) * c y6 + star (c y6) * c y7 - star (c y9) * c y8 - star (c y8) * c y9 + star (c y11) * c y10 + star (c y10) * c y11 - star (c y13) * c y12 - star (c y12) * c y13 + star (c y15) * c y14 + star (c y14) * c y15 := by
  unfold diagBot
  rw [diagB12]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfb12_0, dfb12_1, dfb12_2, dfb12_3, dfb12_4, dfb12_5, dfb12_6, dfb12_7, dfb12_8, dfb12_9, dfb12_10, dfb12_11, dfb12_12, dfb12_13, dfb12_14, dfb12_15]
  simp only [dsb12_w6_0, dsb12_w6_1, dsb12_w6_2, dsb12_w6_3, dsb12_w6_4, dsb12_w6_5, dsb12_w6_6, dsb12_w6_7, dsb12_w6_8, dsb12_w6_9, dsb12_w6_10, dsb12_w6_11, dsb12_w6_12, dsb12_w6_13, dsb12_w6_14, dsb12_w6_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dtop12_w6 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef12 w6 = star (d z1) * d z0 + star (d z0) * d z1 - star (d z3) * d z2 - star (d z2) * d z3 + star (d z5) * d z4 + star (d z4) * d z5 - star (d z7) * d z6 - star (d z6) * d z7 + star (d z9) * d z8 + star (d z8) * d z9 - star (d z11) * d z10 - star (d z10) * d z11 - star (d z13) * d z12 - star (d z12) * d z13 + star (d z15) * d z14 + star (d z14) * d z15 := by
  unfold diagTop
  rw [diagT12]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dft12_0, dft12_1, dft12_2, dft12_3, dft12_4, dft12_5, dft12_6, dft12_7, dft12_8, dft12_9, dft12_10, dft12_11, dft12_12, dft12_13, dft12_14, dft12_15]
  simp only [dst12_w6_0, dst12_w6_1, dst12_w6_2, dst12_w6_3, dst12_w6_4, dst12_w6_5, dst12_w6_6, dst12_w6_7, dst12_w6_8, dst12_w6_9, dst12_w6_10, dst12_w6_11, dst12_w6_12, dst12_w6_13, dst12_w6_14, dst12_w6_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dbot13_w0 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef13 w0 = star (c y2) * c y0 + star (c y3) * c y1 + star (c y0) * c y2 + star (c y1) * c y3 + star (c y6) * c y4 + star (c y7) * c y5 + star (c y4) * c y6 + star (c y5) * c y7 + star (c y10) * c y8 + star (c y11) * c y9 + star (c y8) * c y10 + star (c y9) * c y11 + star (c y14) * c y12 + star (c y15) * c y13 + star (c y12) * c y14 + star (c y13) * c y15 := by
  unfold diagBot
  rw [diagB13]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfb13_0, dfb13_1, dfb13_2, dfb13_3, dfb13_4, dfb13_5, dfb13_6, dfb13_7, dfb13_8, dfb13_9, dfb13_10, dfb13_11, dfb13_12, dfb13_13, dfb13_14, dfb13_15]
  simp only [dsb13_w0_0, dsb13_w0_1, dsb13_w0_2, dsb13_w0_3, dsb13_w0_4, dsb13_w0_5, dsb13_w0_6, dsb13_w0_7, dsb13_w0_8, dsb13_w0_9, dsb13_w0_10, dsb13_w0_11, dsb13_w0_12, dsb13_w0_13, dsb13_w0_14, dsb13_w0_15, SixQubit.signMul_false]
  try ring

theorem dtop13_w0 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef13 w0 = star (d z2) * d z0 + star (d z3) * d z1 + star (d z0) * d z2 + star (d z1) * d z3 + star (d z6) * d z4 + star (d z7) * d z5 + star (d z4) * d z6 + star (d z5) * d z7 + star (d z10) * d z8 + star (d z11) * d z9 + star (d z8) * d z10 + star (d z9) * d z11 + star (d z14) * d z12 + star (d z15) * d z13 + star (d z12) * d z14 + star (d z13) * d z15 := by
  unfold diagTop
  rw [diagT13]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dft13_0, dft13_1, dft13_2, dft13_3, dft13_4, dft13_5, dft13_6, dft13_7, dft13_8, dft13_9, dft13_10, dft13_11, dft13_12, dft13_13, dft13_14, dft13_15]
  simp only [dst13_w0_0, dst13_w0_1, dst13_w0_2, dst13_w0_3, dst13_w0_4, dst13_w0_5, dst13_w0_6, dst13_w0_7, dst13_w0_8, dst13_w0_9, dst13_w0_10, dst13_w0_11, dst13_w0_12, dst13_w0_13, dst13_w0_14, dst13_w0_15, SixQubit.signMul_false]
  try ring

theorem dbot13_w5 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef13 w5 = star (c y2) * c y0 + star (c y3) * c y1 - star (c y0) * c y2 - star (c y1) * c y3 + star (c y6) * c y4 + star (c y7) * c y5 - star (c y4) * c y6 - star (c y5) * c y7 + star (c y10) * c y8 + star (c y11) * c y9 - star (c y8) * c y10 - star (c y9) * c y11 + star (c y14) * c y12 + star (c y15) * c y13 - star (c y12) * c y14 - star (c y13) * c y15 := by
  unfold diagBot
  rw [diagB13]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfb13_0, dfb13_1, dfb13_2, dfb13_3, dfb13_4, dfb13_5, dfb13_6, dfb13_7, dfb13_8, dfb13_9, dfb13_10, dfb13_11, dfb13_12, dfb13_13, dfb13_14, dfb13_15]
  simp only [dsb13_w5_0, dsb13_w5_1, dsb13_w5_2, dsb13_w5_3, dsb13_w5_4, dsb13_w5_5, dsb13_w5_6, dsb13_w5_7, dsb13_w5_8, dsb13_w5_9, dsb13_w5_10, dsb13_w5_11, dsb13_w5_12, dsb13_w5_13, dsb13_w5_14, dsb13_w5_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dtop13_w5 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef13 w5 = star (d z2) * d z0 + star (d z3) * d z1 - star (d z0) * d z2 - star (d z1) * d z3 + star (d z6) * d z4 + star (d z7) * d z5 - star (d z4) * d z6 - star (d z5) * d z7 + star (d z10) * d z8 + star (d z11) * d z9 - star (d z8) * d z10 - star (d z9) * d z11 + star (d z14) * d z12 + star (d z15) * d z13 - star (d z12) * d z14 - star (d z13) * d z15 := by
  unfold diagTop
  rw [diagT13]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dft13_0, dft13_1, dft13_2, dft13_3, dft13_4, dft13_5, dft13_6, dft13_7, dft13_8, dft13_9, dft13_10, dft13_11, dft13_12, dft13_13, dft13_14, dft13_15]
  simp only [dst13_w5_0, dst13_w5_1, dst13_w5_2, dst13_w5_3, dst13_w5_4, dst13_w5_5, dst13_w5_6, dst13_w5_7, dst13_w5_8, dst13_w5_9, dst13_w5_10, dst13_w5_11, dst13_w5_12, dst13_w5_13, dst13_w5_14, dst13_w5_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dbot13_w3 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef13 w3 = star (c y2) * c y0 - star (c y3) * c y1 - star (c y0) * c y2 + star (c y1) * c y3 - star (c y6) * c y4 + star (c y7) * c y5 + star (c y4) * c y6 - star (c y5) * c y7 - star (c y10) * c y8 + star (c y11) * c y9 + star (c y8) * c y10 - star (c y9) * c y11 - star (c y14) * c y12 + star (c y15) * c y13 + star (c y12) * c y14 - star (c y13) * c y15 := by
  unfold diagBot
  rw [diagB13]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfb13_0, dfb13_1, dfb13_2, dfb13_3, dfb13_4, dfb13_5, dfb13_6, dfb13_7, dfb13_8, dfb13_9, dfb13_10, dfb13_11, dfb13_12, dfb13_13, dfb13_14, dfb13_15]
  simp only [dsb13_w3_0, dsb13_w3_1, dsb13_w3_2, dsb13_w3_3, dsb13_w3_4, dsb13_w3_5, dsb13_w3_6, dsb13_w3_7, dsb13_w3_8, dsb13_w3_9, dsb13_w3_10, dsb13_w3_11, dsb13_w3_12, dsb13_w3_13, dsb13_w3_14, dsb13_w3_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dtop13_w3 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef13 w3 = star (d z2) * d z0 - star (d z3) * d z1 - star (d z0) * d z2 + star (d z1) * d z3 + star (d z6) * d z4 - star (d z7) * d z5 - star (d z4) * d z6 + star (d z5) * d z7 + star (d z10) * d z8 - star (d z11) * d z9 - star (d z8) * d z10 + star (d z9) * d z11 - star (d z14) * d z12 + star (d z15) * d z13 + star (d z12) * d z14 - star (d z13) * d z15 := by
  unfold diagTop
  rw [diagT13]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dft13_0, dft13_1, dft13_2, dft13_3, dft13_4, dft13_5, dft13_6, dft13_7, dft13_8, dft13_9, dft13_10, dft13_11, dft13_12, dft13_13, dft13_14, dft13_15]
  simp only [dst13_w3_0, dst13_w3_1, dst13_w3_2, dst13_w3_3, dst13_w3_4, dst13_w3_5, dst13_w3_6, dst13_w3_7, dst13_w3_8, dst13_w3_9, dst13_w3_10, dst13_w3_11, dst13_w3_12, dst13_w3_13, dst13_w3_14, dst13_w3_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dbot13_w7 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef13 w7 = star (c y2) * c y0 - star (c y3) * c y1 + star (c y0) * c y2 - star (c y1) * c y3 - star (c y6) * c y4 + star (c y7) * c y5 - star (c y4) * c y6 + star (c y5) * c y7 - star (c y10) * c y8 + star (c y11) * c y9 - star (c y8) * c y10 + star (c y9) * c y11 - star (c y14) * c y12 + star (c y15) * c y13 - star (c y12) * c y14 + star (c y13) * c y15 := by
  unfold diagBot
  rw [diagB13]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfb13_0, dfb13_1, dfb13_2, dfb13_3, dfb13_4, dfb13_5, dfb13_6, dfb13_7, dfb13_8, dfb13_9, dfb13_10, dfb13_11, dfb13_12, dfb13_13, dfb13_14, dfb13_15]
  simp only [dsb13_w7_0, dsb13_w7_1, dsb13_w7_2, dsb13_w7_3, dsb13_w7_4, dsb13_w7_5, dsb13_w7_6, dsb13_w7_7, dsb13_w7_8, dsb13_w7_9, dsb13_w7_10, dsb13_w7_11, dsb13_w7_12, dsb13_w7_13, dsb13_w7_14, dsb13_w7_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dtop13_w7 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef13 w7 = star (d z2) * d z0 - star (d z3) * d z1 + star (d z0) * d z2 - star (d z1) * d z3 + star (d z6) * d z4 - star (d z7) * d z5 + star (d z4) * d z6 - star (d z5) * d z7 + star (d z10) * d z8 - star (d z11) * d z9 + star (d z8) * d z10 - star (d z9) * d z11 - star (d z14) * d z12 + star (d z15) * d z13 - star (d z12) * d z14 + star (d z13) * d z15 := by
  unfold diagTop
  rw [diagT13]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dft13_0, dft13_1, dft13_2, dft13_3, dft13_4, dft13_5, dft13_6, dft13_7, dft13_8, dft13_9, dft13_10, dft13_11, dft13_12, dft13_13, dft13_14, dft13_15]
  simp only [dst13_w7_0, dst13_w7_1, dst13_w7_2, dst13_w7_3, dst13_w7_4, dst13_w7_5, dst13_w7_6, dst13_w7_7, dst13_w7_8, dst13_w7_9, dst13_w7_10, dst13_w7_11, dst13_w7_12, dst13_w7_13, dst13_w7_14, dst13_w7_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dbot14_w0 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef14 w0 = star (c y3) * c y0 + star (c y2) * c y1 + star (c y1) * c y2 + star (c y0) * c y3 + star (c y7) * c y4 + star (c y6) * c y5 + star (c y5) * c y6 + star (c y4) * c y7 + star (c y11) * c y8 + star (c y10) * c y9 + star (c y9) * c y10 + star (c y8) * c y11 + star (c y15) * c y12 + star (c y14) * c y13 + star (c y13) * c y14 + star (c y12) * c y15 := by
  unfold diagBot
  rw [diagB14]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfb14_0, dfb14_1, dfb14_2, dfb14_3, dfb14_4, dfb14_5, dfb14_6, dfb14_7, dfb14_8, dfb14_9, dfb14_10, dfb14_11, dfb14_12, dfb14_13, dfb14_14, dfb14_15]
  simp only [dsb14_w0_0, dsb14_w0_1, dsb14_w0_2, dsb14_w0_3, dsb14_w0_4, dsb14_w0_5, dsb14_w0_6, dsb14_w0_7, dsb14_w0_8, dsb14_w0_9, dsb14_w0_10, dsb14_w0_11, dsb14_w0_12, dsb14_w0_13, dsb14_w0_14, dsb14_w0_15, SixQubit.signMul_false]
  try ring

theorem dtop14_w0 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef14 w0 = star (d z3) * d z0 + star (d z2) * d z1 + star (d z1) * d z2 + star (d z0) * d z3 + star (d z7) * d z4 + star (d z6) * d z5 + star (d z5) * d z6 + star (d z4) * d z7 + star (d z11) * d z8 + star (d z10) * d z9 + star (d z9) * d z10 + star (d z8) * d z11 + star (d z15) * d z12 + star (d z14) * d z13 + star (d z13) * d z14 + star (d z12) * d z15 := by
  unfold diagTop
  rw [diagT14]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dft14_0, dft14_1, dft14_2, dft14_3, dft14_4, dft14_5, dft14_6, dft14_7, dft14_8, dft14_9, dft14_10, dft14_11, dft14_12, dft14_13, dft14_14, dft14_15]
  simp only [dst14_w0_0, dst14_w0_1, dst14_w0_2, dst14_w0_3, dst14_w0_4, dst14_w0_5, dst14_w0_6, dst14_w0_7, dst14_w0_8, dst14_w0_9, dst14_w0_10, dst14_w0_11, dst14_w0_12, dst14_w0_13, dst14_w0_14, dst14_w0_15, SixQubit.signMul_false]
  try ring

theorem dbot14_w5 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef14 w5 = star (c y3) * c y0 + star (c y2) * c y1 - star (c y1) * c y2 - star (c y0) * c y3 + star (c y7) * c y4 + star (c y6) * c y5 - star (c y5) * c y6 - star (c y4) * c y7 + star (c y11) * c y8 + star (c y10) * c y9 - star (c y9) * c y10 - star (c y8) * c y11 + star (c y15) * c y12 + star (c y14) * c y13 - star (c y13) * c y14 - star (c y12) * c y15 := by
  unfold diagBot
  rw [diagB14]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfb14_0, dfb14_1, dfb14_2, dfb14_3, dfb14_4, dfb14_5, dfb14_6, dfb14_7, dfb14_8, dfb14_9, dfb14_10, dfb14_11, dfb14_12, dfb14_13, dfb14_14, dfb14_15]
  simp only [dsb14_w5_0, dsb14_w5_1, dsb14_w5_2, dsb14_w5_3, dsb14_w5_4, dsb14_w5_5, dsb14_w5_6, dsb14_w5_7, dsb14_w5_8, dsb14_w5_9, dsb14_w5_10, dsb14_w5_11, dsb14_w5_12, dsb14_w5_13, dsb14_w5_14, dsb14_w5_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dtop14_w5 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef14 w5 = star (d z3) * d z0 + star (d z2) * d z1 - star (d z1) * d z2 - star (d z0) * d z3 + star (d z7) * d z4 + star (d z6) * d z5 - star (d z5) * d z6 - star (d z4) * d z7 + star (d z11) * d z8 + star (d z10) * d z9 - star (d z9) * d z10 - star (d z8) * d z11 + star (d z15) * d z12 + star (d z14) * d z13 - star (d z13) * d z14 - star (d z12) * d z15 := by
  unfold diagTop
  rw [diagT14]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dft14_0, dft14_1, dft14_2, dft14_3, dft14_4, dft14_5, dft14_6, dft14_7, dft14_8, dft14_9, dft14_10, dft14_11, dft14_12, dft14_13, dft14_14, dft14_15]
  simp only [dst14_w5_0, dst14_w5_1, dst14_w5_2, dst14_w5_3, dst14_w5_4, dst14_w5_5, dst14_w5_6, dst14_w5_7, dst14_w5_8, dst14_w5_9, dst14_w5_10, dst14_w5_11, dst14_w5_12, dst14_w5_13, dst14_w5_14, dst14_w5_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dbot14_w4 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef14 w4 = star (c y3) * c y0 - star (c y2) * c y1 + star (c y1) * c y2 - star (c y0) * c y3 + star (c y7) * c y4 - star (c y6) * c y5 + star (c y5) * c y6 - star (c y4) * c y7 + star (c y11) * c y8 - star (c y10) * c y9 + star (c y9) * c y10 - star (c y8) * c y11 + star (c y15) * c y12 - star (c y14) * c y13 + star (c y13) * c y14 - star (c y12) * c y15 := by
  unfold diagBot
  rw [diagB14]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfb14_0, dfb14_1, dfb14_2, dfb14_3, dfb14_4, dfb14_5, dfb14_6, dfb14_7, dfb14_8, dfb14_9, dfb14_10, dfb14_11, dfb14_12, dfb14_13, dfb14_14, dfb14_15]
  simp only [dsb14_w4_0, dsb14_w4_1, dsb14_w4_2, dsb14_w4_3, dsb14_w4_4, dsb14_w4_5, dsb14_w4_6, dsb14_w4_7, dsb14_w4_8, dsb14_w4_9, dsb14_w4_10, dsb14_w4_11, dsb14_w4_12, dsb14_w4_13, dsb14_w4_14, dsb14_w4_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dtop14_w4 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef14 w4 = star (d z3) * d z0 - star (d z2) * d z1 + star (d z1) * d z2 - star (d z0) * d z3 + star (d z7) * d z4 - star (d z6) * d z5 + star (d z5) * d z6 - star (d z4) * d z7 + star (d z11) * d z8 - star (d z10) * d z9 + star (d z9) * d z10 - star (d z8) * d z11 + star (d z15) * d z12 - star (d z14) * d z13 + star (d z13) * d z14 - star (d z12) * d z15 := by
  unfold diagTop
  rw [diagT14]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dft14_0, dft14_1, dft14_2, dft14_3, dft14_4, dft14_5, dft14_6, dft14_7, dft14_8, dft14_9, dft14_10, dft14_11, dft14_12, dft14_13, dft14_14, dft14_15]
  simp only [dst14_w4_0, dst14_w4_1, dst14_w4_2, dst14_w4_3, dst14_w4_4, dst14_w4_5, dst14_w4_6, dst14_w4_7, dst14_w4_8, dst14_w4_9, dst14_w4_10, dst14_w4_11, dst14_w4_12, dst14_w4_13, dst14_w4_14, dst14_w4_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dbot14_w8 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef14 w8 = star (c y3) * c y0 - star (c y2) * c y1 - star (c y1) * c y2 + star (c y0) * c y3 + star (c y7) * c y4 - star (c y6) * c y5 - star (c y5) * c y6 + star (c y4) * c y7 + star (c y11) * c y8 - star (c y10) * c y9 - star (c y9) * c y10 + star (c y8) * c y11 + star (c y15) * c y12 - star (c y14) * c y13 - star (c y13) * c y14 + star (c y12) * c y15 := by
  unfold diagBot
  rw [diagB14]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfb14_0, dfb14_1, dfb14_2, dfb14_3, dfb14_4, dfb14_5, dfb14_6, dfb14_7, dfb14_8, dfb14_9, dfb14_10, dfb14_11, dfb14_12, dfb14_13, dfb14_14, dfb14_15]
  simp only [dsb14_w8_0, dsb14_w8_1, dsb14_w8_2, dsb14_w8_3, dsb14_w8_4, dsb14_w8_5, dsb14_w8_6, dsb14_w8_7, dsb14_w8_8, dsb14_w8_9, dsb14_w8_10, dsb14_w8_11, dsb14_w8_12, dsb14_w8_13, dsb14_w8_14, dsb14_w8_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dtop14_w8 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef14 w8 = star (d z3) * d z0 - star (d z2) * d z1 - star (d z1) * d z2 + star (d z0) * d z3 + star (d z7) * d z4 - star (d z6) * d z5 - star (d z5) * d z6 + star (d z4) * d z7 + star (d z11) * d z8 - star (d z10) * d z9 - star (d z9) * d z10 + star (d z8) * d z11 + star (d z15) * d z12 - star (d z14) * d z13 - star (d z13) * d z14 + star (d z12) * d z15 := by
  unfold diagTop
  rw [diagT14]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dft14_0, dft14_1, dft14_2, dft14_3, dft14_4, dft14_5, dft14_6, dft14_7, dft14_8, dft14_9, dft14_10, dft14_11, dft14_12, dft14_13, dft14_14, dft14_15]
  simp only [dst14_w8_0, dst14_w8_1, dst14_w8_2, dst14_w8_3, dst14_w8_4, dst14_w8_5, dst14_w8_6, dst14_w8_7, dst14_w8_8, dst14_w8_9, dst14_w8_10, dst14_w8_11, dst14_w8_12, dst14_w8_13, dst14_w8_14, dst14_w8_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring



/-! ### Extra dressings for the twelve two-term column relations -/

theorem sg0_w3_8 : SS.bdot w3 z8 = false := by decide
theorem sg0_w3_9 : SS.bdot w3 z9 = true := by decide
theorem sg0_w3_10 : SS.bdot w3 z10 = true := by decide
theorem sg0_w3_11 : SS.bdot w3 z11 = false := by decide
theorem sg0_w3_12 : SS.bdot w3 z12 = true := by decide
theorem sg0_w3_13 : SS.bdot w3 z13 = false := by decide
theorem sg0_w3_14 : SS.bdot w3 z14 = false := by decide
theorem sg0_w3_15 : SS.bdot w3 z15 = true := by decide
theorem sg0_w4_8 : SS.bdot w4 z8 = false := by decide
theorem sg0_w4_9 : SS.bdot w4 z9 = true := by decide
theorem sg0_w4_10 : SS.bdot w4 z10 = false := by decide
theorem sg0_w4_11 : SS.bdot w4 z11 = true := by decide
theorem sg0_w4_12 : SS.bdot w4 z12 = false := by decide
theorem sg0_w4_13 : SS.bdot w4 z13 = true := by decide
theorem sg0_w4_14 : SS.bdot w4 z14 = false := by decide
theorem sg0_w4_15 : SS.bdot w4 z15 = true := by decide
theorem sg0_w5_8 : SS.bdot w5 z8 = false := by decide
theorem sg0_w5_9 : SS.bdot w5 z9 = false := by decide
theorem sg0_w5_10 : SS.bdot w5 z10 = true := by decide
theorem sg0_w5_11 : SS.bdot w5 z11 = true := by decide
theorem sg0_w5_12 : SS.bdot w5 z12 = false := by decide
theorem sg0_w5_13 : SS.bdot w5 z13 = false := by decide
theorem sg0_w5_14 : SS.bdot w5 z14 = true := by decide
theorem sg0_w5_15 : SS.bdot w5 z15 = true := by decide

theorem sg1_w3_4 : SS.bdot w3 z4 = false := by decide
theorem sg1_w3_5 : SS.bdot w3 z5 = true := by decide
theorem sg1_w3_6 : SS.bdot w3 z6 = true := by decide
theorem sg1_w3_7 : SS.bdot w3 z7 = false := by decide
theorem sg1_w3_12 : SS.bdot w3 z12 = true := by decide
theorem sg1_w3_13 : SS.bdot w3 z13 = false := by decide
theorem sg1_w3_14 : SS.bdot w3 z14 = false := by decide
theorem sg1_w3_15 : SS.bdot w3 z15 = true := by decide
theorem sg1_w4_4 : SS.bdot w4 z4 = false := by decide
theorem sg1_w4_5 : SS.bdot w4 z5 = true := by decide
theorem sg1_w4_6 : SS.bdot w4 z6 = false := by decide
theorem sg1_w4_7 : SS.bdot w4 z7 = true := by decide
theorem sg1_w4_12 : SS.bdot w4 z12 = false := by decide
theorem sg1_w4_13 : SS.bdot w4 z13 = true := by decide
theorem sg1_w4_14 : SS.bdot w4 z14 = false := by decide
theorem sg1_w4_15 : SS.bdot w4 z15 = true := by decide
theorem sg1_w5_4 : SS.bdot w5 z4 = false := by decide
theorem sg1_w5_5 : SS.bdot w5 z5 = false := by decide
theorem sg1_w5_6 : SS.bdot w5 z6 = true := by decide
theorem sg1_w5_7 : SS.bdot w5 z7 = true := by decide
theorem sg1_w5_12 : SS.bdot w5 z12 = false := by decide
theorem sg1_w5_13 : SS.bdot w5 z13 = false := by decide
theorem sg1_w5_14 : SS.bdot w5 z14 = true := by decide
theorem sg1_w5_15 : SS.bdot w5 z15 = true := by decide

theorem sg2_w3_0 : SS.bdot w3 z0 = false := by decide
theorem sg2_w3_1 : SS.bdot w3 z1 = true := by decide
theorem sg2_w3_2 : SS.bdot w3 z2 = true := by decide
theorem sg2_w3_3 : SS.bdot w3 z3 = false := by decide
theorem sg2_w3_12 : SS.bdot w3 z12 = true := by decide
theorem sg2_w3_13 : SS.bdot w3 z13 = false := by decide
theorem sg2_w3_14 : SS.bdot w3 z14 = false := by decide
theorem sg2_w3_15 : SS.bdot w3 z15 = true := by decide
theorem sg2_w4_0 : SS.bdot w4 z0 = false := by decide
theorem sg2_w4_1 : SS.bdot w4 z1 = true := by decide
theorem sg2_w4_2 : SS.bdot w4 z2 = false := by decide
theorem sg2_w4_3 : SS.bdot w4 z3 = true := by decide
theorem sg2_w4_12 : SS.bdot w4 z12 = false := by decide
theorem sg2_w4_13 : SS.bdot w4 z13 = true := by decide
theorem sg2_w4_14 : SS.bdot w4 z14 = false := by decide
theorem sg2_w4_15 : SS.bdot w4 z15 = true := by decide
theorem sg2_w5_0 : SS.bdot w5 z0 = false := by decide
theorem sg2_w5_1 : SS.bdot w5 z1 = false := by decide
theorem sg2_w5_2 : SS.bdot w5 z2 = true := by decide
theorem sg2_w5_3 : SS.bdot w5 z3 = true := by decide
theorem sg2_w5_12 : SS.bdot w5 z12 = false := by decide
theorem sg2_w5_13 : SS.bdot w5 z13 = false := by decide
theorem sg2_w5_14 : SS.bdot w5 z14 = true := by decide
theorem sg2_w5_15 : SS.bdot w5 z15 = true := by decide

theorem ex0_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w3 = star (c y0) * d z8 - star (c y1) * d z9 - star (c y2) * d z10 + star (c y3) * d z11 - star (c y4) * d z12 + star (c y5) * d z13 + star (c y6) * d z14 - star (c y7) * d z15 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_8, fl0_9, fl0_10, fl0_11, fl0_12, fl0_13, fl0_14, fl0_15]
  simp only [sg0_w3_8, sg0_w3_9, sg0_w3_10, sg0_w3_11, sg0_w3_12, sg0_w3_13, sg0_w3_14, sg0_w3_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex0_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w4 = star (c y0) * d z8 - star (c y1) * d z9 + star (c y2) * d z10 - star (c y3) * d z11 + star (c y4) * d z12 - star (c y5) * d z13 + star (c y6) * d z14 - star (c y7) * d z15 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_8, fl0_9, fl0_10, fl0_11, fl0_12, fl0_13, fl0_14, fl0_15]
  simp only [sg0_w4_8, sg0_w4_9, sg0_w4_10, sg0_w4_11, sg0_w4_12, sg0_w4_13, sg0_w4_14, sg0_w4_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex0_w5 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w5 = star (c y0) * d z8 + star (c y1) * d z9 - star (c y2) * d z10 - star (c y3) * d z11 + star (c y4) * d z12 + star (c y5) * d z13 - star (c y6) * d z14 - star (c y7) * d z15 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_8, fl0_9, fl0_10, fl0_11, fl0_12, fl0_13, fl0_14, fl0_15]
  simp only [sg0_w5_8, sg0_w5_9, sg0_w5_10, sg0_w5_11, sg0_w5_12, sg0_w5_13, sg0_w5_14, sg0_w5_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex1_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w3 = star (c y0) * d z4 - star (c y1) * d z5 - star (c y2) * d z6 + star (c y3) * d z7 - star (c y8) * d z12 + star (c y9) * d z13 + star (c y10) * d z14 - star (c y11) * d z15 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_4, fl1_5, fl1_6, fl1_7, fl1_12, fl1_13, fl1_14, fl1_15]
  simp only [sg1_w3_4, sg1_w3_5, sg1_w3_6, sg1_w3_7, sg1_w3_12, sg1_w3_13, sg1_w3_14, sg1_w3_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex1_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w4 = star (c y0) * d z4 - star (c y1) * d z5 + star (c y2) * d z6 - star (c y3) * d z7 + star (c y8) * d z12 - star (c y9) * d z13 + star (c y10) * d z14 - star (c y11) * d z15 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_4, fl1_5, fl1_6, fl1_7, fl1_12, fl1_13, fl1_14, fl1_15]
  simp only [sg1_w4_4, sg1_w4_5, sg1_w4_6, sg1_w4_7, sg1_w4_12, sg1_w4_13, sg1_w4_14, sg1_w4_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex1_w5 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w5 = star (c y0) * d z4 + star (c y1) * d z5 - star (c y2) * d z6 - star (c y3) * d z7 + star (c y8) * d z12 + star (c y9) * d z13 - star (c y10) * d z14 - star (c y11) * d z15 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_4, fl1_5, fl1_6, fl1_7, fl1_12, fl1_13, fl1_14, fl1_15]
  simp only [sg1_w5_4, sg1_w5_5, sg1_w5_6, sg1_w5_7, sg1_w5_12, sg1_w5_13, sg1_w5_14, sg1_w5_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex2_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w3 = star (c y0) * d z0 - star (c y1) * d z1 - star (c y2) * d z2 + star (c y3) * d z3 - star (c y12) * d z12 + star (c y13) * d z13 + star (c y14) * d z14 - star (c y15) * d z15 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_0, fl2_1, fl2_2, fl2_3, fl2_12, fl2_13, fl2_14, fl2_15]
  simp only [sg2_w3_0, sg2_w3_1, sg2_w3_2, sg2_w3_3, sg2_w3_12, sg2_w3_13, sg2_w3_14, sg2_w3_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex2_w4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w4 = star (c y0) * d z0 - star (c y1) * d z1 + star (c y2) * d z2 - star (c y3) * d z3 + star (c y12) * d z12 - star (c y13) * d z13 + star (c y14) * d z14 - star (c y15) * d z15 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_0, fl2_1, fl2_2, fl2_3, fl2_12, fl2_13, fl2_14, fl2_15]
  simp only [sg2_w4_0, sg2_w4_1, sg2_w4_2, sg2_w4_3, sg2_w4_12, sg2_w4_13, sg2_w4_14, sg2_w4_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex2_w5 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w5 = star (c y0) * d z0 + star (c y1) * d z1 - star (c y2) * d z2 - star (c y3) * d z3 + star (c y12) * d z12 + star (c y13) * d z13 - star (c y14) * d z14 - star (c y15) * d z15 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_0, fl2_1, fl2_2, fl2_3, fl2_12, fl2_13, fl2_14, fl2_15]
  simp only [sg2_w5_0, sg2_w5_1, sg2_w5_2, sg2_w5_3, sg2_w5_12, sg2_w5_13, sg2_w5_14, sg2_w5_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring


/-! ### The twelve two-term column relations, in conjugated form -/

/-- Column relation: row `B1`, column `0`. -/
theorem hcol_1_0 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef0 w1 = 0)
    (h1 : offSum c d ef0 w5 = 0)
    (h2 : offSum c d ef0 w4 = 0)
    (h3 : offSum c d ef0 w3 = 0)
    : star (d z8) * c y0 = star (d z15) * c y7 := by
  rw [ex0_w1] at h0
  rw [ex0_w5] at h1
  rw [ex0_w4] at h2
  rw [ex0_w3] at h3
  have hh : star (c y0) * d z8 = star (c y7) * d z15 := by
    linear_combination (1/4 : ℂ) * h0 + (1/4 : ℂ) * h1 + (1/4 : ℂ) * h2 + (1/4 : ℂ) * h3
  have h2 := congrArg star hh
  simp only [star_mul', star_star] at h2
  linear_combination h2

/-- Column relation: row `B1`, column `1`. -/
theorem hcol_1_1 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef0 w1 = 0)
    (h1 : offSum c d ef0 w5 = 0)
    (h2 : offSum c d ef0 w4 = 0)
    (h3 : offSum c d ef0 w3 = 0)
    : star (d z9) * c y1 = star (d z14) * c y6 := by
  rw [ex0_w1] at h0
  rw [ex0_w5] at h1
  rw [ex0_w4] at h2
  rw [ex0_w3] at h3
  have hh : star (c y1) * d z9 = star (c y6) * d z14 := by
    linear_combination (1/4 : ℂ) * h0 + (1/4 : ℂ) * h1 + (-1/4 : ℂ) * h2 + (-1/4 : ℂ) * h3
  have h2 := congrArg star hh
  simp only [star_mul', star_star] at h2
  linear_combination h2

/-- Column relation: row `B1`, column `2`. -/
theorem hcol_1_2 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef0 w1 = 0)
    (h1 : offSum c d ef0 w5 = 0)
    (h2 : offSum c d ef0 w4 = 0)
    (h3 : offSum c d ef0 w3 = 0)
    : star (d z10) * c y2 = star (d z13) * c y5 := by
  rw [ex0_w1] at h0
  rw [ex0_w5] at h1
  rw [ex0_w4] at h2
  rw [ex0_w3] at h3
  have hh : star (c y2) * d z10 = star (c y5) * d z13 := by
    linear_combination (1/4 : ℂ) * h0 + (-1/4 : ℂ) * h1 + (1/4 : ℂ) * h2 + (-1/4 : ℂ) * h3
  have h2 := congrArg star hh
  simp only [star_mul', star_star] at h2
  linear_combination h2

/-- Column relation: row `B1`, column `3`. -/
theorem hcol_1_3 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef0 w1 = 0)
    (h1 : offSum c d ef0 w5 = 0)
    (h2 : offSum c d ef0 w4 = 0)
    (h3 : offSum c d ef0 w3 = 0)
    : star (d z11) * c y3 = star (d z12) * c y4 := by
  rw [ex0_w1] at h0
  rw [ex0_w5] at h1
  rw [ex0_w4] at h2
  rw [ex0_w3] at h3
  have hh : star (c y3) * d z11 = star (c y4) * d z12 := by
    linear_combination (1/4 : ℂ) * h0 + (-1/4 : ℂ) * h1 + (-1/4 : ℂ) * h2 + (1/4 : ℂ) * h3
  have h2 := congrArg star hh
  simp only [star_mul', star_star] at h2
  linear_combination h2

/-- Column relation: row `B2`, column `0`. -/
theorem hcol_2_0 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef1 w2 = 0)
    (h1 : offSum c d ef1 w5 = 0)
    (h2 : offSum c d ef1 w4 = 0)
    (h3 : offSum c d ef1 w3 = 0)
    : star (d z4) * c y0 = star (d z15) * c y11 := by
  rw [ex1_w2] at h0
  rw [ex1_w5] at h1
  rw [ex1_w4] at h2
  rw [ex1_w3] at h3
  have hh : star (c y0) * d z4 = star (c y11) * d z15 := by
    linear_combination (1/4 : ℂ) * h0 + (1/4 : ℂ) * h1 + (1/4 : ℂ) * h2 + (1/4 : ℂ) * h3
  have h2 := congrArg star hh
  simp only [star_mul', star_star] at h2
  linear_combination h2

/-- Column relation: row `B2`, column `1`. -/
theorem hcol_2_1 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef1 w2 = 0)
    (h1 : offSum c d ef1 w5 = 0)
    (h2 : offSum c d ef1 w4 = 0)
    (h3 : offSum c d ef1 w3 = 0)
    : star (d z5) * c y1 = star (d z14) * c y10 := by
  rw [ex1_w2] at h0
  rw [ex1_w5] at h1
  rw [ex1_w4] at h2
  rw [ex1_w3] at h3
  have hh : star (c y1) * d z5 = star (c y10) * d z14 := by
    linear_combination (1/4 : ℂ) * h0 + (1/4 : ℂ) * h1 + (-1/4 : ℂ) * h2 + (-1/4 : ℂ) * h3
  have h2 := congrArg star hh
  simp only [star_mul', star_star] at h2
  linear_combination h2

/-- Column relation: row `B2`, column `2`. -/
theorem hcol_2_2 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef1 w2 = 0)
    (h1 : offSum c d ef1 w5 = 0)
    (h2 : offSum c d ef1 w4 = 0)
    (h3 : offSum c d ef1 w3 = 0)
    : star (d z6) * c y2 = star (d z13) * c y9 := by
  rw [ex1_w2] at h0
  rw [ex1_w5] at h1
  rw [ex1_w4] at h2
  rw [ex1_w3] at h3
  have hh : star (c y2) * d z6 = star (c y9) * d z13 := by
    linear_combination (1/4 : ℂ) * h0 + (-1/4 : ℂ) * h1 + (1/4 : ℂ) * h2 + (-1/4 : ℂ) * h3
  have h2 := congrArg star hh
  simp only [star_mul', star_star] at h2
  linear_combination h2

/-- Column relation: row `B2`, column `3`. -/
theorem hcol_2_3 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef1 w2 = 0)
    (h1 : offSum c d ef1 w5 = 0)
    (h2 : offSum c d ef1 w4 = 0)
    (h3 : offSum c d ef1 w3 = 0)
    : star (d z7) * c y3 = star (d z12) * c y8 := by
  rw [ex1_w2] at h0
  rw [ex1_w5] at h1
  rw [ex1_w4] at h2
  rw [ex1_w3] at h3
  have hh : star (c y3) * d z7 = star (c y8) * d z12 := by
    linear_combination (1/4 : ℂ) * h0 + (-1/4 : ℂ) * h1 + (-1/4 : ℂ) * h2 + (1/4 : ℂ) * h3
  have h2 := congrArg star hh
  simp only [star_mul', star_star] at h2
  linear_combination h2

/-- Column relation: row `B3`, column `0`. -/
theorem hcol_3_0 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef2 w2 = 0)
    (h1 : offSum c d ef2 w5 = 0)
    (h2 : offSum c d ef2 w4 = 0)
    (h3 : offSum c d ef2 w3 = 0)
    : star (d z0) * c y0 = star (d z15) * c y15 := by
  rw [ex2_w2] at h0
  rw [ex2_w5] at h1
  rw [ex2_w4] at h2
  rw [ex2_w3] at h3
  have hh : star (c y0) * d z0 = star (c y15) * d z15 := by
    linear_combination (1/4 : ℂ) * h0 + (1/4 : ℂ) * h1 + (1/4 : ℂ) * h2 + (1/4 : ℂ) * h3
  have h2 := congrArg star hh
  simp only [star_mul', star_star] at h2
  linear_combination h2

/-- Column relation: row `B3`, column `1`. -/
theorem hcol_3_1 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef2 w2 = 0)
    (h1 : offSum c d ef2 w5 = 0)
    (h2 : offSum c d ef2 w4 = 0)
    (h3 : offSum c d ef2 w3 = 0)
    : star (d z1) * c y1 = star (d z14) * c y14 := by
  rw [ex2_w2] at h0
  rw [ex2_w5] at h1
  rw [ex2_w4] at h2
  rw [ex2_w3] at h3
  have hh : star (c y1) * d z1 = star (c y14) * d z14 := by
    linear_combination (1/4 : ℂ) * h0 + (1/4 : ℂ) * h1 + (-1/4 : ℂ) * h2 + (-1/4 : ℂ) * h3
  have h2 := congrArg star hh
  simp only [star_mul', star_star] at h2
  linear_combination h2

/-- Column relation: row `B3`, column `2`. -/
theorem hcol_3_2 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef2 w2 = 0)
    (h1 : offSum c d ef2 w5 = 0)
    (h2 : offSum c d ef2 w4 = 0)
    (h3 : offSum c d ef2 w3 = 0)
    : star (d z2) * c y2 = star (d z13) * c y13 := by
  rw [ex2_w2] at h0
  rw [ex2_w5] at h1
  rw [ex2_w4] at h2
  rw [ex2_w3] at h3
  have hh : star (c y2) * d z2 = star (c y13) * d z13 := by
    linear_combination (1/4 : ℂ) * h0 + (-1/4 : ℂ) * h1 + (1/4 : ℂ) * h2 + (-1/4 : ℂ) * h3
  have h2 := congrArg star hh
  simp only [star_mul', star_star] at h2
  linear_combination h2

/-- Column relation: row `B3`, column `3`. -/
theorem hcol_3_3 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef2 w2 = 0)
    (h1 : offSum c d ef2 w5 = 0)
    (h2 : offSum c d ef2 w4 = 0)
    (h3 : offSum c d ef2 w3 = 0)
    : star (d z3) * c y3 = star (d z12) * c y12 := by
  rw [ex2_w2] at h0
  rw [ex2_w5] at h1
  rw [ex2_w4] at h2
  rw [ex2_w3] at h3
  have hh : star (c y3) * d z3 = star (c y12) * d z12 := by
    linear_combination (1/4 : ℂ) * h0 + (-1/4 : ℂ) * h1 + (-1/4 : ℂ) * h2 + (1/4 : ℂ) * h3
  have h2 := congrArg star hh
  simp only [star_mul', star_star] at h2
  linear_combination h2


/-! ### Family three: the twelve ordered-pair Gram identities -/

/-- Family three for the ordered column pair `(1, 0)`. -/
theorem fam3_1_0 (c d : SS.BitString 6 -> ℂ)
    (h0 : diagBot c ef12 w0 = diagTop d ef12 w0)
    (h1 : diagBot c ef12 w4 = diagTop d ef12 w4)
    (h2 : diagBot c ef12 w3 = diagTop d ef12 w3)
    (h3 : diagBot c ef12 w6 = diagTop d ef12 w6)
    : c y6 * star (c y7) + c y10 * star (c y11) + c y14 * star (c y15) + star (c y1) * c y0
      = star (d z9) * d z8 + star (d z5) * d z4 + star (d z1) * d z0 + d z14 * star (d z15) := by
  rw [dbot12_w0, dtop12_w0] at h0
  rw [dbot12_w4, dtop12_w4] at h1
  rw [dbot12_w3, dtop12_w3] at h2
  rw [dbot12_w6, dtop12_w6] at h3
  linear_combination (1/4 : ℂ) * h0 + (1/4 : ℂ) * h1 + (1/4 : ℂ) * h2 + (1/4 : ℂ) * h3

/-- Family three for the ordered column pair `(3, 2)`. -/
theorem fam3_3_2 (c d : SS.BitString 6 -> ℂ)
    (h0 : diagBot c ef12 w0 = diagTop d ef12 w0)
    (h1 : diagBot c ef12 w4 = diagTop d ef12 w4)
    (h2 : diagBot c ef12 w3 = diagTop d ef12 w3)
    (h3 : diagBot c ef12 w6 = diagTop d ef12 w6)
    : c y4 * star (c y5) + c y8 * star (c y9) + c y12 * star (c y13) + star (c y3) * c y2
      = star (d z11) * d z10 + star (d z7) * d z6 + star (d z3) * d z2 + d z12 * star (d z13) := by
  rw [dbot12_w0, dtop12_w0] at h0
  rw [dbot12_w4, dtop12_w4] at h1
  rw [dbot12_w3, dtop12_w3] at h2
  rw [dbot12_w6, dtop12_w6] at h3
  linear_combination (1/4 : ℂ) * h0 + (1/4 : ℂ) * h1 + (-1/4 : ℂ) * h2 + (-1/4 : ℂ) * h3

/-- Family three for the ordered column pair `(2, 3)`. -/
theorem fam3_2_3 (c d : SS.BitString 6 -> ℂ)
    (h0 : diagBot c ef12 w0 = diagTop d ef12 w0)
    (h1 : diagBot c ef12 w4 = diagTop d ef12 w4)
    (h2 : diagBot c ef12 w3 = diagTop d ef12 w3)
    (h3 : diagBot c ef12 w6 = diagTop d ef12 w6)
    : c y5 * star (c y4) + c y9 * star (c y8) + c y13 * star (c y12) + star (c y2) * c y3
      = star (d z10) * d z11 + star (d z6) * d z7 + star (d z2) * d z3 + d z13 * star (d z12) := by
  rw [dbot12_w0, dtop12_w0] at h0
  rw [dbot12_w4, dtop12_w4] at h1
  rw [dbot12_w3, dtop12_w3] at h2
  rw [dbot12_w6, dtop12_w6] at h3
  linear_combination (1/4 : ℂ) * h0 + (-1/4 : ℂ) * h1 + (1/4 : ℂ) * h2 + (-1/4 : ℂ) * h3

/-- Family three for the ordered column pair `(0, 1)`. -/
theorem fam3_0_1 (c d : SS.BitString 6 -> ℂ)
    (h0 : diagBot c ef12 w0 = diagTop d ef12 w0)
    (h1 : diagBot c ef12 w4 = diagTop d ef12 w4)
    (h2 : diagBot c ef12 w3 = diagTop d ef12 w3)
    (h3 : diagBot c ef12 w6 = diagTop d ef12 w6)
    : c y7 * star (c y6) + c y11 * star (c y10) + c y15 * star (c y14) + star (c y0) * c y1
      = star (d z8) * d z9 + star (d z4) * d z5 + star (d z0) * d z1 + d z15 * star (d z14) := by
  rw [dbot12_w0, dtop12_w0] at h0
  rw [dbot12_w4, dtop12_w4] at h1
  rw [dbot12_w3, dtop12_w3] at h2
  rw [dbot12_w6, dtop12_w6] at h3
  linear_combination (1/4 : ℂ) * h0 + (-1/4 : ℂ) * h1 + (-1/4 : ℂ) * h2 + (1/4 : ℂ) * h3

/-- Family three for the ordered column pair `(2, 0)`. -/
theorem fam3_2_0 (c d : SS.BitString 6 -> ℂ)
    (h0 : diagBot c ef13 w0 = diagTop d ef13 w0)
    (h1 : diagBot c ef13 w5 = diagTop d ef13 w5)
    (h2 : diagBot c ef13 w3 = diagTop d ef13 w3)
    (h3 : diagBot c ef13 w7 = diagTop d ef13 w7)
    : c y5 * star (c y7) + c y9 * star (c y11) + c y13 * star (c y15) + star (c y2) * c y0
      = star (d z10) * d z8 + star (d z6) * d z4 + star (d z2) * d z0 + d z13 * star (d z15) := by
  rw [dbot13_w0, dtop13_w0] at h0
  rw [dbot13_w5, dtop13_w5] at h1
  rw [dbot13_w3, dtop13_w3] at h2
  rw [dbot13_w7, dtop13_w7] at h3
  linear_combination (1/4 : ℂ) * h0 + (1/4 : ℂ) * h1 + (1/4 : ℂ) * h2 + (1/4 : ℂ) * h3

/-- Family three for the ordered column pair `(3, 1)`. -/
theorem fam3_3_1 (c d : SS.BitString 6 -> ℂ)
    (h0 : diagBot c ef13 w0 = diagTop d ef13 w0)
    (h1 : diagBot c ef13 w5 = diagTop d ef13 w5)
    (h2 : diagBot c ef13 w3 = diagTop d ef13 w3)
    (h3 : diagBot c ef13 w7 = diagTop d ef13 w7)
    : c y4 * star (c y6) + c y8 * star (c y10) + c y12 * star (c y14) + star (c y3) * c y1
      = star (d z11) * d z9 + star (d z7) * d z5 + star (d z3) * d z1 + d z12 * star (d z14) := by
  rw [dbot13_w0, dtop13_w0] at h0
  rw [dbot13_w5, dtop13_w5] at h1
  rw [dbot13_w3, dtop13_w3] at h2
  rw [dbot13_w7, dtop13_w7] at h3
  linear_combination (1/4 : ℂ) * h0 + (1/4 : ℂ) * h1 + (-1/4 : ℂ) * h2 + (-1/4 : ℂ) * h3

/-- Family three for the ordered column pair `(1, 3)`. -/
theorem fam3_1_3 (c d : SS.BitString 6 -> ℂ)
    (h0 : diagBot c ef13 w0 = diagTop d ef13 w0)
    (h1 : diagBot c ef13 w5 = diagTop d ef13 w5)
    (h2 : diagBot c ef13 w3 = diagTop d ef13 w3)
    (h3 : diagBot c ef13 w7 = diagTop d ef13 w7)
    : c y6 * star (c y4) + c y10 * star (c y8) + c y14 * star (c y12) + star (c y1) * c y3
      = star (d z9) * d z11 + star (d z5) * d z7 + star (d z1) * d z3 + d z14 * star (d z12) := by
  rw [dbot13_w0, dtop13_w0] at h0
  rw [dbot13_w5, dtop13_w5] at h1
  rw [dbot13_w3, dtop13_w3] at h2
  rw [dbot13_w7, dtop13_w7] at h3
  linear_combination (1/4 : ℂ) * h0 + (-1/4 : ℂ) * h1 + (1/4 : ℂ) * h2 + (-1/4 : ℂ) * h3

/-- Family three for the ordered column pair `(0, 2)`. -/
theorem fam3_0_2 (c d : SS.BitString 6 -> ℂ)
    (h0 : diagBot c ef13 w0 = diagTop d ef13 w0)
    (h1 : diagBot c ef13 w5 = diagTop d ef13 w5)
    (h2 : diagBot c ef13 w3 = diagTop d ef13 w3)
    (h3 : diagBot c ef13 w7 = diagTop d ef13 w7)
    : c y7 * star (c y5) + c y11 * star (c y9) + c y15 * star (c y13) + star (c y0) * c y2
      = star (d z8) * d z10 + star (d z4) * d z6 + star (d z0) * d z2 + d z15 * star (d z13) := by
  rw [dbot13_w0, dtop13_w0] at h0
  rw [dbot13_w5, dtop13_w5] at h1
  rw [dbot13_w3, dtop13_w3] at h2
  rw [dbot13_w7, dtop13_w7] at h3
  linear_combination (1/4 : ℂ) * h0 + (-1/4 : ℂ) * h1 + (-1/4 : ℂ) * h2 + (1/4 : ℂ) * h3

/-- Family three for the ordered column pair `(3, 0)`. -/
theorem fam3_3_0 (c d : SS.BitString 6 -> ℂ)
    (h0 : diagBot c ef14 w0 = diagTop d ef14 w0)
    (h1 : diagBot c ef14 w5 = diagTop d ef14 w5)
    (h2 : diagBot c ef14 w4 = diagTop d ef14 w4)
    (h3 : diagBot c ef14 w8 = diagTop d ef14 w8)
    : c y4 * star (c y7) + c y8 * star (c y11) + c y12 * star (c y15) + star (c y3) * c y0
      = star (d z11) * d z8 + star (d z7) * d z4 + star (d z3) * d z0 + d z12 * star (d z15) := by
  rw [dbot14_w0, dtop14_w0] at h0
  rw [dbot14_w5, dtop14_w5] at h1
  rw [dbot14_w4, dtop14_w4] at h2
  rw [dbot14_w8, dtop14_w8] at h3
  linear_combination (1/4 : ℂ) * h0 + (1/4 : ℂ) * h1 + (1/4 : ℂ) * h2 + (1/4 : ℂ) * h3

/-- Family three for the ordered column pair `(2, 1)`. -/
theorem fam3_2_1 (c d : SS.BitString 6 -> ℂ)
    (h0 : diagBot c ef14 w0 = diagTop d ef14 w0)
    (h1 : diagBot c ef14 w5 = diagTop d ef14 w5)
    (h2 : diagBot c ef14 w4 = diagTop d ef14 w4)
    (h3 : diagBot c ef14 w8 = diagTop d ef14 w8)
    : c y5 * star (c y6) + c y9 * star (c y10) + c y13 * star (c y14) + star (c y2) * c y1
      = star (d z10) * d z9 + star (d z6) * d z5 + star (d z2) * d z1 + d z13 * star (d z14) := by
  rw [dbot14_w0, dtop14_w0] at h0
  rw [dbot14_w5, dtop14_w5] at h1
  rw [dbot14_w4, dtop14_w4] at h2
  rw [dbot14_w8, dtop14_w8] at h3
  linear_combination (1/4 : ℂ) * h0 + (1/4 : ℂ) * h1 + (-1/4 : ℂ) * h2 + (-1/4 : ℂ) * h3

/-- Family three for the ordered column pair `(1, 2)`. -/
theorem fam3_1_2 (c d : SS.BitString 6 -> ℂ)
    (h0 : diagBot c ef14 w0 = diagTop d ef14 w0)
    (h1 : diagBot c ef14 w5 = diagTop d ef14 w5)
    (h2 : diagBot c ef14 w4 = diagTop d ef14 w4)
    (h3 : diagBot c ef14 w8 = diagTop d ef14 w8)
    : c y6 * star (c y5) + c y10 * star (c y9) + c y14 * star (c y13) + star (c y1) * c y2
      = star (d z9) * d z10 + star (d z5) * d z6 + star (d z1) * d z2 + d z14 * star (d z13) := by
  rw [dbot14_w0, dtop14_w0] at h0
  rw [dbot14_w5, dtop14_w5] at h1
  rw [dbot14_w4, dtop14_w4] at h2
  rw [dbot14_w8, dtop14_w8] at h3
  linear_combination (1/4 : ℂ) * h0 + (-1/4 : ℂ) * h1 + (1/4 : ℂ) * h2 + (-1/4 : ℂ) * h3

/-- Family three for the ordered column pair `(0, 3)`. -/
theorem fam3_0_3 (c d : SS.BitString 6 -> ℂ)
    (h0 : diagBot c ef14 w0 = diagTop d ef14 w0)
    (h1 : diagBot c ef14 w5 = diagTop d ef14 w5)
    (h2 : diagBot c ef14 w4 = diagTop d ef14 w4)
    (h3 : diagBot c ef14 w8 = diagTop d ef14 w8)
    : c y7 * star (c y4) + c y11 * star (c y8) + c y15 * star (c y12) + star (c y0) * c y3
      = star (d z8) * d z11 + star (d z4) * d z7 + star (d z0) * d z3 + d z15 * star (d z12) := by
  rw [dbot14_w0, dtop14_w0] at h0
  rw [dbot14_w5, dtop14_w5] at h1
  rw [dbot14_w4, dtop14_w4] at h2
  rw [dbot14_w8, dtop14_w8] at h3
  linear_combination (1/4 : ℂ) * h0 + (-1/4 : ℂ) * h1 + (-1/4 : ℂ) * h2 + (1/4 : ℂ) * h3


/-! ## The branch algebra -/

theorem lagrange3_real (x1 x2 x3 y1 y2 y3 : ℂ) :
    (Complex.normSq x1 + Complex.normSq x2 + Complex.normSq x3)
      * (Complex.normSq y1 + Complex.normSq y2 + Complex.normSq y3)
      = Complex.normSq (x1 * star y1 + x2 * star y2 + x3 * star y3)
        + (Complex.normSq (x1 * y2 - x2 * y1) + Complex.normSq (x1 * y3 - x3 * y1)
            + Complex.normSq (x2 * y3 - x3 * y2)) := by
  have hc : (((Complex.normSq x1 + Complex.normSq x2 + Complex.normSq x3)
      * (Complex.normSq y1 + Complex.normSq y2 + Complex.normSq y3) : ℝ) : ℂ)
      = ((Complex.normSq (x1 * star y1 + x2 * star y2 + x3 * star y3)
        + (Complex.normSq (x1 * y2 - x2 * y1) + Complex.normSq (x1 * y3 - x3 * y1)
            + Complex.normSq (x2 * y3 - x3 * y2)) : ℝ) : ℂ) := by
    push_cast
    simp only [← Table31.sq, star_add, star_sub, star_mul', star_star]
    ring
  exact_mod_cast hc

theorem amp_eq_zero_of_v (a v : ℂ) (hK : v * star v = a * star a) (h : v = 0) : a = 0 := by
  have hz : a * star a = 0 := by rw [← hK, h]; ring
  rcases mul_eq_zero.mp hz with h' | h'
  · exact h'
  · exact star_eq_zero.mp h'

theorem v_ne_zero (a v : ℂ) (hK : v * star v = a * star a) (ha : a ≠ 0) : v ≠ 0 := by
  intro h; exact ha (amp_eq_zero_of_v a v hK h)

/-! ### Branch: a column alone in its phase class -/

/-- A column whose phase class is a singleton has `v_f = 0`, hence `a_f = 0`. -/
theorem branch_lone (vf vg1 vg2 vg3 af Mff Mg1f Mg2f Mg3f : ℂ) (alf alg1 alg2 alg3 : ℝ)
    (hEq : vg1 * Mg1f + vg2 * Mg2f + vg3 * Mg3f + vf * Mff = 0)
    (hMff : Mff = (alf : ℂ) + 1/8)
    (t1 : vg1 * Mg1f = (alg1 : ℂ) * vf)
    (t2 : vg2 * Mg2f = (alg2 : ℂ) * vf)
    (t3 : vg3 * Mg3f = (alg3 : ℂ) * vf)
    (hS : alf + alg1 + alg2 + alg3 = 1/4)
    (hKf : vf * star vf = af * star af) : af = 0 := by
  have hSc := congrArg (fun x : ℝ => (x : ℂ)) hS
  push_cast at hSc
  rw [hMff, t1, t2, t3] at hEq
  have h38 : vf * (3/8 : ℂ) = 0 := by linear_combination hEq - vf * hSc
  rcases mul_eq_zero.mp h38 with h | h
  · exact amp_eq_zero_of_v af vf hKf h
  · norm_num at h

/-! ### Branch: a phase class of exactly two columns -/

set_option maxHeartbeats 1000000 in
/-- A class of exactly two columns: the `2 x 2` system is singular, so
Cauchy-Schwarz is tight; the vanishing permanents then confine both columns to a
single row, whose budget they exceed. -/
theorem branch_pair
    (ae af ve vf vg vh b1e b2e b3e b1f b2f b3f Mee Mff Mef Mfe Mge Mhe Mgf Mhf : ℂ)
    (alg alh : ℝ)
    (hEqE : vg * Mge + vh * Mhe + ve * Mee + vf * Mfe = 0)
    (hEqF : vg * Mgf + vh * Mhf + ve * Mef + vf * Mff = 0)
    (tge : vg * Mge = (alg : ℂ) * ve) (the : vh * Mhe = (alh : ℂ) * ve)
    (tgf : vg * Mgf = (alg : ℂ) * vf) (thf : vh * Mhf = (alh : ℂ) * vf)
    (hMee : Mee = (Complex.normSq ae : ℂ) + 1/8)
    (hMff : Mff = (Complex.normSq af : ℂ) + 1/8)
    (hMef : Mef = b1e * star b1f + b2e * star b2f + b3e * star b3f)
    (hMfe : Mfe = b1f * star b1e + b2f * star b2e + b3f * star b3e)
    (hSum : Complex.normSq ae + Complex.normSq af + alg + alh = 1/4)
    (halg : 0 ≤ alg) (halh : 0 ≤ alh)
    (hColE : Complex.normSq b1e + Complex.normSq b2e + Complex.normSq b3e
               = Complex.normSq ae + 1/8)
    (hColF : Complex.normSq b1f + Complex.normSq b2f + Complex.normSq b3f
               = Complex.normSq af + 1/8)
    (hRow1 : Complex.normSq b1e + Complex.normSq b1f ≤ 1/4)
    (hRow2 : Complex.normSq b2e + Complex.normSq b2f ≤ 1/4)
    (hRow3 : Complex.normSq b3e + Complex.normSq b3f ≤ 1/4)
    (p12 : b1e * b2f + b1f * b2e = 0)
    (p13 : b1e * b3f + b1f * b3e = 0)
    (p23 : b2e * b3f + b2f * b3e = 0)
    (hKe : ve * star ve = ae * star ae) (_hKf : vf * star vf = af * star af)
    (hae : ae ≠ 0) (haf : af ≠ 0) : False := by
  have hSc := congrArg (fun x : ℝ => (x : ℂ)) hSum
  push_cast at hSc
  have hcast : ((Complex.normSq ae + Complex.normSq af : ℝ) : ℂ)
      = (Complex.normSq ae : ℂ) + (Complex.normSq af : ℂ) := by push_cast; ring
  rw [hMee, tge, the] at hEqE
  rw [hMff, tgf, thf] at hEqF
  have h0 : ve * ((Complex.normSq ae : ℂ) + 1/8
        + ((1/4 : ℂ) - ((Complex.normSq ae + Complex.normSq af : ℝ) : ℂ))) + vf * Mfe = 0 := by
    rw [hcast]; linear_combination hEqE - ve * hSc
  have h1 : vf * ((Complex.normSq af : ℂ) + 1/8
        + ((1/4 : ℂ) - ((Complex.normSq ae + Complex.normSq af : ℝ) : ℂ))) + ve * Mef = 0 := by
    rw [hcast]; linear_combination hEqF - vf * hSc
  have hve : ve ≠ 0 := v_ne_zero ae ve hKe hae
  have hv : ¬ (ve = 0 ∧ vf = 0) := fun h => hve h.1
  have hpc := Table31.pair_class ve vf Mef Mfe (Complex.normSq ae) (Complex.normSq af)
    (Complex.normSq ae + Complex.normSq af) hv h0 h1
  have hstar : Mfe = star Mef := by
    rw [hMef, hMfe]; simp only [star_add, star_mul', star_star]; ring
  rw [hstar, Table31.sq] at hpc
  push_cast at hpc
  have hreal : (Complex.normSq ae + 1/8 + (1/4 - (Complex.normSq ae + Complex.normSq af)))
      * (Complex.normSq af + 1/8 + (1/4 - (Complex.normSq ae + Complex.normSq af)))
      = Complex.normSq Mef := by
    refine Complex.ofReal_inj.mp ?_
    push_cast
    linear_combination hpc
  have hlag := lagrange3_real b1e b2e b3e b1f b2f b3f
  rw [← hMef, hColE, hColF] at hlag
  have hgap := Table31.pair_gap (Complex.normSq ae) (Complex.normSq af)
    (Complex.normSq ae + Complex.normSq af) rfl
  have hsle : Complex.normSq ae + Complex.normSq af ≤ 1/4 := by linarith
  have n1 := Complex.normSq_nonneg (b1e * b2f - b2e * b1f)
  have n2 := Complex.normSq_nonneg (b1e * b3f - b3e * b1f)
  have n3 := Complex.normSq_nonneg (b2e * b3f - b3e * b2f)
  have hm1 : Complex.normSq (b1e * b2f - b2e * b1f) = 0 := by linarith
  have hm2 : Complex.normSq (b1e * b3f - b3e * b1f) = 0 := by linarith
  have hm3 : Complex.normSq (b2e * b3f - b3e * b2f) = 0 := by linarith
  have d12 : b1e * b2f - b1f * b2e = 0 := by
    have := Complex.normSq_eq_zero.mp hm1; linear_combination this
  have d13 : b1e * b3f - b1f * b3e = 0 := by
    have := Complex.normSq_eq_zero.mp hm2; linear_combination this
  have d23 : b2e * b3f - b2f * b3e = 0 := by
    have := Complex.normSq_eq_zero.mp hm3; linear_combination this
  obtain ⟨q12a, q12b⟩ := Table31.det_perm_zero b1e b1f b2e b2f d12 p12
  obtain ⟨q13a, q13b⟩ := Table31.det_perm_zero b1e b1f b3e b3f d13 p13
  obtain ⟨q23a, q23b⟩ := Table31.det_perm_zero b2e b2f b3e b3f d23 p23
  have z01 : Complex.normSq b1e * Complex.normSq b2f = 0 := by
    rw [← Complex.normSq_mul, q12a]; simp
  have z10 : Complex.normSq b2e * Complex.normSq b1f = 0 := by
    rw [← Complex.normSq_mul]; rw [show b2e * b1f = b1f * b2e by ring, q12b]; simp
  have z02 : Complex.normSq b1e * Complex.normSq b3f = 0 := by
    rw [← Complex.normSq_mul, q13a]; simp
  have z20 : Complex.normSq b3e * Complex.normSq b1f = 0 := by
    rw [← Complex.normSq_mul]; rw [show b3e * b1f = b1f * b3e by ring, q13b]; simp
  have z12 : Complex.normSq b2e * Complex.normSq b3f = 0 := by
    rw [← Complex.normSq_mul, q23a]; simp
  have z21 : Complex.normSq b3e * Complex.normSq b2f = 0 := by
    rw [← Complex.normSq_mul]; rw [show b3e * b2f = b2f * b3e by ring, q23b]; simp
  have hApos : (0 : ℝ) < Complex.normSq ae + 1/8 := by
    have := Complex.normSq_nonneg ae; linarith
  have hBpos : (0 : ℝ) < Complex.normSq af + 1/8 := by
    have := Complex.normSq_nonneg af; linarith
  have htp := Table31.tight_pair (Complex.normSq b1e) (Complex.normSq b2e) (Complex.normSq b3e)
    (Complex.normSq b1f) (Complex.normSq b2f) (Complex.normSq b3f)
    (Complex.normSq ae + 1/8) (Complex.normSq af + 1/8)
    (Complex.normSq_nonneg _) (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
    (Complex.normSq_nonneg _) (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
    z01 z02 z10 z12 z20 z21 hColE hColF hApos hBpos hRow1 hRow2 hRow3
  have hpos : 0 < Complex.normSq ae := Complex.normSq_pos.mpr hae
  have hpos' : 0 < Complex.normSq af := Complex.normSq_pos.mpr haf
  linarith

theorem same_phase_ne (ae af ve vf : ℂ)
    (hT : ve * star vf - ae * star af = 0)
    (hKf : vf * star vf = af * star af)
    (hae : ae ≠ 0) (haf : af ≠ 0) :
    ve * af + vf * ae ≠ 0 := by
  intro h
  have key : (2 : ℂ) * (ae * (af * star af)) = 0 := by
    linear_combination (star vf) * h - af * hT - ae * hKf
  rcases mul_eq_zero.mp key with h' | h'
  · norm_num at h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · exact hae h''
    · rcases mul_eq_zero.mp h'' with h3 | h3
      · exact haf h3
      · exact haf (star_eq_zero.mp h3)

/-- The `B`-column Gram diagonal is the column total, `alpha_e + 1/8`. -/
theorem diag_M (b1 b2 b3 : ℂ) (al : ℝ)
    (h : Complex.normSq b1 + Complex.normSq b2 + Complex.normSq b3 = al + 1/8) :
    b1 * star b1 + b2 * star b2 + b3 * star b3 = (al : ℂ) + 1/8 := by
  rw [Table31.sq, Table31.sq, Table31.sq]
  have hc := congrArg (fun x : ℝ => (x : ℂ)) h
  push_cast at hc
  linear_combination hc

/-- A column with no `A` amplitude contributes nothing to the pairing. -/
theorem term_of_zero (ae ve vf Mef : ℂ) (h0 : ae = 0) (hKe : ve * star ve = ae * star ae) :
    ve * Mef = (Complex.normSq ae : ℂ) * vf := by
  have hv : ve = 0 := by
    rcases mul_eq_zero.mp (by rw [hKe, h0]; ring : ve * star ve = 0) with h | h
    · exact h
    · exact star_eq_zero.mp h
  rw [hv, h0]; simp

/-- A column of a different phase contributes `alpha_e * v_f`. -/
theorem term_of_diff (ae ve vf Mef : ℂ) (hKe : ve * star ve = ae * star ae)
    (hM : Mef = star ve * vf) : ve * Mef = (Complex.normSq ae : ℂ) * vf := by
  rw [hM, ← Table31.sq ae]
  linear_combination vf * hKe

/-- The phase test is symmetric. -/
theorem T_symm (ae af ve vf : ℂ) (h : ve * star vf - ae * star af = 0) :
    vf * star ve - af * star ae = 0 := by
  have hs := congrArg star h
  simp only [star_sub, star_mul', star_star, star_zero] at hs
  linear_combination hs

/-- Same phase kills the permanent outright. -/
theorem perm_extract (ae af ve vf x : ℂ) (hP : (ve * af + vf * ae) * x = 0)
    (hT : ve * star vf - ae * star af = 0) (hKf : vf * star vf = af * star af)
    (hae : ae ≠ 0) (haf : af ≠ 0) : x = 0 := by
  rcases mul_eq_zero.mp hP with h | h
  · exact absurd h (same_phase_ne ae af ve vf hT hKf hae haf)
  · exact h

/-- The phase test is transitive through a column with a nonzero amplitude. -/
theorem T_trans (ae af ag ve vf vg : ℂ)
    (h1 : ve * star vf - ae * star af = 0)
    (h2 : vf * star vg - af * star ag = 0)
    (hKf : vf * star vf = af * star af)
    (haf : af ≠ 0) :
    ve * star vg - ae * star ag = 0 := by
  have key : (ve * star vg - ae * star ag) * (af * star af) = 0 := by
    linear_combination (vf * star vg) * h1 + (ae * star af) * h2 - (ve * star vg) * hKf
  rcases mul_eq_zero.mp key with h' | h'
  · exact h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd h'' haf
    · exact absurd (star_eq_zero.mp h'') haf

/-- Family two, cleared of denominators by the four column relations: the
permanent of the `2 x 2` block is killed by the phase factor. -/
theorem perm_of_raw (ae af ve vf b1e b1f b2e b2f u1e u1f u2e u2f : ℂ)
    (hFam2 : b1f * u2e + b1e * u2f + b2f * u1e + b2e * u1f = 0)
    (hC1e : u1e * ae = ve * b1e) (hC1f : u1f * af = vf * b1f)
    (hC2e : u2e * ae = ve * b2e) (hC2f : u2f * af = vf * b2f) :
    (ve * af + vf * ae) * (b1e * b2f + b1f * b2e) = 0 := by
  linear_combination (ae * af) * hFam2 - (af * b2f) * hC1e - (ae * b2e) * hC1f
    - (af * b1f) * hC2e - (ae * b1e) * hC2f

/-! ### Support propagation along vanishing permanents -/

/-- If one row is nonzero at a column where another vanishes, the vanishing
permanents wipe out the whole of the second row -- impossible, since every row
carries a quarter. -/
theorem row_wipe (be bf bg bh se sf sg sh : ℂ) (hbe : be ≠ 0) (hse : se = 0)
    (pf : be * sf + bf * se = 0) (pg : be * sg + bg * se = 0) (ph : be * sh + bh * se = 0)
    (hrow : Complex.normSq se + Complex.normSq sf + Complex.normSq sg + Complex.normSq sh = 1/4) :
    False := by
  have h1 := Table31.perm_support be bf se sf hbe hse pf
  have h2 := Table31.perm_support be bg se sg hbe hse pg
  have h3 := Table31.perm_support be bh se sh hbe hse ph
  rw [hse, h1, h2, h3] at hrow
  simp only [Complex.normSq_zero] at hrow
  linarith

/-- The three-column version: the wiped row is then confined to the fourth
column, whose total is only an eighth. -/
theorem row_wipe3 (be bf bg se sf sg sh : ℂ) (hbe : be ≠ 0) (hse : se = 0)
    (pf : be * sf + bf * se = 0) (pg : be * sg + bg * se = 0)
    (hrow : Complex.normSq se + Complex.normSq sf + Complex.normSq sg + Complex.normSq sh = 1/4)
    (hsh : Complex.normSq sh ≤ 1/8) : False := by
  have h1 := Table31.perm_support be bf se sf hbe hse pf
  have h2 := Table31.perm_support be bg se sg hbe hse pg
  rw [hse, h1, h2] at hrow
  simp only [Complex.normSq_zero] at hrow
  linarith

/-- Every entry of the bottom block is nonzero once all permanents vanish. -/
theorem entry_ne (xe xf xg xh ye yf yg yh ze zf zg zh : ℂ) (ale : ℝ) (hale : 0 ≤ ale)
    (hcol : Complex.normSq xe + Complex.normSq ye + Complex.normSq ze = ale + 1/8)
    (hrow : Complex.normSq xe + Complex.normSq xf + Complex.normSq xg + Complex.normSq xh = 1/4)
    (qyf : ye * xf + yf * xe = 0) (qyg : ye * xg + yg * xe = 0) (qyh : ye * xh + yh * xe = 0)
    (qzf : ze * xf + zf * xe = 0) (qzg : ze * xg + zg * xe = 0) (qzh : ze * xh + zh * xe = 0) :
    xe ≠ 0 := by
  intro h0
  by_cases hy : ye = 0
  · by_cases hz : ze = 0
    · rw [h0, hy, hz] at hcol
      simp only [Complex.normSq_zero] at hcol
      linarith
    · exact row_wipe ze zf zg zh xe xf xg xh hz h0 qzf qzg qzh hrow
  · exact row_wipe ye yf yg yh xe xf xg xh hy h0 qyf qyg qyh hrow

/-- The three-column version. -/
theorem entry_ne3 (xe xf xg xh ye yf yg ze zf zg : ℂ) (ale : ℝ) (hale : 0 ≤ ale)
    (hcol : Complex.normSq xe + Complex.normSq ye + Complex.normSq ze = ale + 1/8)
    (hrow : Complex.normSq xe + Complex.normSq xf + Complex.normSq xg + Complex.normSq xh = 1/4)
    (hxh : Complex.normSq xh ≤ 1/8)
    (qyf : ye * xf + yf * xe = 0) (qyg : ye * xg + yg * xe = 0)
    (qzf : ze * xf + zf * xe = 0) (qzg : ze * xg + zg * xe = 0) :
    xe ≠ 0 := by
  intro h0
  by_cases hy : ye = 0
  · by_cases hz : ze = 0
    · rw [h0, hy, hz] at hcol
      simp only [Complex.normSq_zero] at hcol
      linarith
    · exact row_wipe3 ze zf zg xe xf xg xh hz h0 qzf qzg hrow hxh
  · exact row_wipe3 ye yf yg xe xf xg xh hy h0 qyf qyg hrow hxh

/-! ### Branch: all four columns in one phase class -/

/-- With every permanent vanishing, all twelve bottom entries are nonzero, and
`perm_triple` then gives a contradiction. -/
theorem branch_quad (b10 b11 b12 b13 b20 b21 b22 b23 b30 b31 b32 b33 : ℂ)
    (al0 al1 al2 : ℝ) (hal0 : 0 ≤ al0) (hal1 : 0 ≤ al1) (hal2 : 0 ≤ al2)
    (hRow1 : Complex.normSq b10 + Complex.normSq b11 + Complex.normSq b12
               + Complex.normSq b13 = 1/4)
    (hRow2 : Complex.normSq b20 + Complex.normSq b21 + Complex.normSq b22
               + Complex.normSq b23 = 1/4)
    (hCol0 : Complex.normSq b10 + Complex.normSq b20 + Complex.normSq b30 = al0 + 1/8)
    (hCol1 : Complex.normSq b11 + Complex.normSq b21 + Complex.normSq b31 = al1 + 1/8)
    (hCol2 : Complex.normSq b12 + Complex.normSq b22 + Complex.normSq b32 = al2 + 1/8)
    (p12_01 : b10 * b21 + b11 * b20 = 0) (p12_02 : b10 * b22 + b12 * b20 = 0)
    (p12_03 : b10 * b23 + b13 * b20 = 0) (p12_12 : b11 * b22 + b12 * b21 = 0)
    (p12_13 : b11 * b23 + b13 * b21 = 0) (p12_23 : b12 * b23 + b13 * b22 = 0)
    (p13_01 : b10 * b31 + b11 * b30 = 0) (p13_02 : b10 * b32 + b12 * b30 = 0)
    (p13_12 : b11 * b32 + b12 * b31 = 0) (p13_13 : b11 * b33 + b13 * b31 = 0)
    (p13_23 : b12 * b33 + b13 * b32 = 0)
    (p23_01 : b20 * b31 + b21 * b30 = 0) (p23_02 : b20 * b32 + b22 * b30 = 0)
    (p23_03 : b20 * b33 + b23 * b30 = 0) : False := by
  have hb11 : b11 ≠ 0 :=
    entry_ne b11 b10 b12 b13 b21 b20 b22 b23 b31 b30 b32 b33 al1 hal1 hCol1 (by linarith)
      (by linear_combination p12_01) (by linear_combination p12_12)
      (by linear_combination p12_13) (by linear_combination p13_01)
      (by linear_combination p13_12) (by linear_combination p13_13)
  have hb12 : b12 ≠ 0 :=
    entry_ne b12 b10 b11 b13 b22 b20 b21 b23 b32 b30 b31 b33 al2 hal2 hCol2 (by linarith)
      (by linear_combination p12_02) (by linear_combination p12_12)
      (by linear_combination p12_23) (by linear_combination p13_02)
      (by linear_combination p13_12) (by linear_combination p13_23)
  have hb20 : b20 ≠ 0 :=
    entry_ne b20 b21 b22 b23 b10 b11 b12 b13 b30 b31 b32 b33 al0 hal0 (by linarith) hRow2
      (by linear_combination p12_01) (by linear_combination p12_02)
      (by linear_combination p12_03) (by linear_combination p23_01)
      (by linear_combination p23_02) (by linear_combination p23_03)
  have htri := Table31.perm_triple b10 b11 b12 b20 b21 b22 p12_01 p12_02 p12_12
  rcases mul_eq_zero.mp htri with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact hb11 h'
    · exact hb12 h'
  · exact hb20 h

/-! ### Branch: three columns in one class, the fourth with no `A` amplitude -/

/-- The three same-phase columns are entirely nonzero on the bottom block, and
`perm_triple` closes the branch. -/
theorem branch_triple (b1e b1f b1g b1h b2e b2f b2g b2h b3e b3f b3g : ℂ)
    (ale alf alg : ℝ) (hale : 0 ≤ ale) (half : 0 ≤ alf) (halg : 0 ≤ alg)
    (hRow1 : Complex.normSq b1e + Complex.normSq b1f + Complex.normSq b1g
               + Complex.normSq b1h = 1/4)
    (hRow2 : Complex.normSq b2e + Complex.normSq b2f + Complex.normSq b2g
               + Complex.normSq b2h = 1/4)
    (hColE : Complex.normSq b1e + Complex.normSq b2e + Complex.normSq b3e = ale + 1/8)
    (hColF : Complex.normSq b1f + Complex.normSq b2f + Complex.normSq b3f = alf + 1/8)
    (hColG : Complex.normSq b1g + Complex.normSq b2g + Complex.normSq b3g = alg + 1/8)
    (hColH : Complex.normSq b1h + Complex.normSq b2h ≤ 1/8)
    (p12_ef : b1e * b2f + b1f * b2e = 0) (p12_eg : b1e * b2g + b1g * b2e = 0)
    (p12_fg : b1f * b2g + b1g * b2f = 0)
    (p13_ef : b1e * b3f + b1f * b3e = 0) (p13_eg : b1e * b3g + b1g * b3e = 0)
    (p13_fg : b1f * b3g + b1g * b3f = 0)
    (p23_ef : b2e * b3f + b2f * b3e = 0) (p23_eg : b2e * b3g + b2g * b3e = 0) : False := by
  have n1h := Complex.normSq_nonneg b1h
  have n2h := Complex.normSq_nonneg b2h
  have hb1f : b1f ≠ 0 :=
    entry_ne3 b1f b1e b1g b1h b2f b2e b2g b3f b3e b3g alf half hColF (by linarith) (by linarith)
      (by linear_combination p12_ef) (by linear_combination p12_fg)
      (by linear_combination p13_ef) (by linear_combination p13_fg)
  have hb1g : b1g ≠ 0 :=
    entry_ne3 b1g b1e b1f b1h b2g b2e b2f b3g b3e b3f alg halg hColG (by linarith) (by linarith)
      (by linear_combination p12_eg) (by linear_combination p12_fg)
      (by linear_combination p13_eg) (by linear_combination p13_fg)
  have hb2e : b2e ≠ 0 :=
    entry_ne3 b2e b2f b2g b2h b1e b1f b1g b3e b3f b3g ale hale (by linarith) hRow2 (by linarith)
      (by linear_combination p12_ef) (by linear_combination p12_eg)
      (by linear_combination p23_ef) (by linear_combination p23_eg)
  have htri := Table31.perm_triple b1e b1f b1g b2e b2f b2g p12_ef p12_eg p12_fg
  rcases mul_eq_zero.mp htri with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact hb1f h'
    · exact hb1g h'
  · exact hb2e h

set_option maxHeartbeats 2000000 in
/-- **The branch assembly.**  The four columns of the orbit-31 table, with
family one, the moment budget, the conditional family-three pins and the
family-two permanents, admit no solution. -/
theorem master
    (a0 a1 a2 a3 v0 v1 v2 v3 : ℂ)
    (b10 b11 b12 b13 b20 b21 b22 b23 b30 b31 b32 b33 : ℂ)
    (hK0 : v0 * star v0 = a0 * star a0)
    (hK1 : v1 * star v1 = a1 * star a1)
    (hK2 : v2 * star v2 = a2 * star a2)
    (hK3 : v3 * star v3 = a3 * star a3)
    (hF1 : b10 * v0 + b11 * v1 + b12 * v2 + b13 * v3 = 0)
    (hF2 : b20 * v0 + b21 * v1 + b22 * v2 + b23 * v3 = 0)
    (hF3 : b30 * v0 + b31 * v1 + b32 * v2 + b33 * v3 = 0)
    (hSum : Complex.normSq a0 + Complex.normSq a1 + Complex.normSq a2 + Complex.normSq a3 = 1/4)
    (hRow1 : Complex.normSq b10 + Complex.normSq b11 + Complex.normSq b12 + Complex.normSq b13 = 1/4)
    (hRow2 : Complex.normSq b20 + Complex.normSq b21 + Complex.normSq b22 + Complex.normSq b23 = 1/4)
    (hRow3 : Complex.normSq b30 + Complex.normSq b31 + Complex.normSq b32 + Complex.normSq b33 = 1/4)
    (hCol0 : Complex.normSq b10 + Complex.normSq b20 + Complex.normSq b30 = Complex.normSq a0 + 1/8)
    (hCol1 : Complex.normSq b11 + Complex.normSq b21 + Complex.normSq b31 = Complex.normSq a1 + 1/8)
    (hCol2 : Complex.normSq b12 + Complex.normSq b22 + Complex.normSq b32 = Complex.normSq a2 + 1/8)
    (hCol3 : Complex.normSq b13 + Complex.normSq b23 + Complex.normSq b33 = Complex.normSq a3 + 1/8)
    (hM01 : v0 * star v1 - a0 * star a1 ≠ 0 →
        (b10 * star b11 + b20 * star b21 + b30 * star b31) = star v0 * v1)
    (hM02 : v0 * star v2 - a0 * star a2 ≠ 0 →
        (b10 * star b12 + b20 * star b22 + b30 * star b32) = star v0 * v2)
    (hM03 : v0 * star v3 - a0 * star a3 ≠ 0 →
        (b10 * star b13 + b20 * star b23 + b30 * star b33) = star v0 * v3)
    (hM10 : v1 * star v0 - a1 * star a0 ≠ 0 →
        (b11 * star b10 + b21 * star b20 + b31 * star b30) = star v1 * v0)
    (hM12 : v1 * star v2 - a1 * star a2 ≠ 0 →
        (b11 * star b12 + b21 * star b22 + b31 * star b32) = star v1 * v2)
    (hM13 : v1 * star v3 - a1 * star a3 ≠ 0 →
        (b11 * star b13 + b21 * star b23 + b31 * star b33) = star v1 * v3)
    (hM20 : v2 * star v0 - a2 * star a0 ≠ 0 →
        (b12 * star b10 + b22 * star b20 + b32 * star b30) = star v2 * v0)
    (hM21 : v2 * star v1 - a2 * star a1 ≠ 0 →
        (b12 * star b11 + b22 * star b21 + b32 * star b31) = star v2 * v1)
    (hM23 : v2 * star v3 - a2 * star a3 ≠ 0 →
        (b12 * star b13 + b22 * star b23 + b32 * star b33) = star v2 * v3)
    (hM30 : v3 * star v0 - a3 * star a0 ≠ 0 →
        (b13 * star b10 + b23 * star b20 + b33 * star b30) = star v3 * v0)
    (hM31 : v3 * star v1 - a3 * star a1 ≠ 0 →
        (b13 * star b11 + b23 * star b21 + b33 * star b31) = star v3 * v1)
    (hM32 : v3 * star v2 - a3 * star a2 ≠ 0 →
        (b13 * star b12 + b23 * star b22 + b33 * star b32) = star v3 * v2)
    (hP12_01 : (v0 * a1 + v1 * a0) * (b10 * b21 + b11 * b20) = 0)
    (hP12_02 : (v0 * a2 + v2 * a0) * (b10 * b22 + b12 * b20) = 0)
    (hP12_03 : (v0 * a3 + v3 * a0) * (b10 * b23 + b13 * b20) = 0)
    (hP12_12 : (v1 * a2 + v2 * a1) * (b11 * b22 + b12 * b21) = 0)
    (hP12_13 : (v1 * a3 + v3 * a1) * (b11 * b23 + b13 * b21) = 0)
    (hP12_23 : (v2 * a3 + v3 * a2) * (b12 * b23 + b13 * b22) = 0)
    (hP13_01 : (v0 * a1 + v1 * a0) * (b10 * b31 + b11 * b30) = 0)
    (hP13_02 : (v0 * a2 + v2 * a0) * (b10 * b32 + b12 * b30) = 0)
    (hP13_03 : (v0 * a3 + v3 * a0) * (b10 * b33 + b13 * b30) = 0)
    (hP13_12 : (v1 * a2 + v2 * a1) * (b11 * b32 + b12 * b31) = 0)
    (hP13_13 : (v1 * a3 + v3 * a1) * (b11 * b33 + b13 * b31) = 0)
    (hP13_23 : (v2 * a3 + v3 * a2) * (b12 * b33 + b13 * b32) = 0)
    (hP23_01 : (v0 * a1 + v1 * a0) * (b20 * b31 + b21 * b30) = 0)
    (hP23_02 : (v0 * a2 + v2 * a0) * (b20 * b32 + b22 * b30) = 0)
    (hP23_03 : (v0 * a3 + v3 * a0) * (b20 * b33 + b23 * b30) = 0)
    (hP23_12 : (v1 * a2 + v2 * a1) * (b21 * b32 + b22 * b31) = 0)
    (hP23_13 : (v1 * a3 + v3 * a1) * (b21 * b33 + b23 * b31) = 0)
    (hP23_23 : (v2 * a3 + v3 * a2) * (b22 * b33 + b23 * b32) = 0)
    : False := by
  have n0 := Complex.normSq_nonneg a0
  have n1 := Complex.normSq_nonneg a1
  have n2 := Complex.normSq_nonneg a2
  have n3 := Complex.normSq_nonneg a3
  have nb10 := Complex.normSq_nonneg b10
  have nb11 := Complex.normSq_nonneg b11
  have nb12 := Complex.normSq_nonneg b12
  have nb13 := Complex.normSq_nonneg b13
  have nb20 := Complex.normSq_nonneg b20
  have nb21 := Complex.normSq_nonneg b21
  have nb22 := Complex.normSq_nonneg b22
  have nb23 := Complex.normSq_nonneg b23
  have nb30 := Complex.normSq_nonneg b30
  have nb31 := Complex.normSq_nonneg b31
  have nb32 := Complex.normSq_nonneg b32
  have nb33 := Complex.normSq_nonneg b33
  have hD0 := diag_M b10 b20 b30 (Complex.normSq a0) hCol0
  have hD1 := diag_M b11 b21 b31 (Complex.normSq a1) hCol1
  have hD2 := diag_M b12 b22 b32 (Complex.normSq a2) hCol2
  have hD3 := diag_M b13 b23 b33 (Complex.normSq a3) hCol3
  have G0 := Table31.gram_eq b10 b20 b30 b11 b21 b31 b12 b22 b32 b13 b23 b33 v0 v1 v2 v3 b10 b20 b30 hF1 hF2 hF3
  have G1 := Table31.gram_eq b10 b20 b30 b11 b21 b31 b12 b22 b32 b13 b23 b33 v0 v1 v2 v3 b11 b21 b31 hF1 hF2 hF3
  have G2 := Table31.gram_eq b10 b20 b30 b11 b21 b31 b12 b22 b32 b13 b23 b33 v0 v1 v2 v3 b12 b22 b32 hF1 hF2 hF3
  have G3 := Table31.gram_eq b10 b20 b30 b11 b21 b31 b12 b22 b32 b13 b23 b33 v0 v1 v2 v3 b13 b23 b33 hF1 hF2 hF3
  by_cases ha0 : a0 = 0
  ·
    by_cases ha1 : a1 = 0
    ·
      by_cases ha2 : a2 = 0
      ·
        by_cases ha3 : a3 = 0
        ·
          have hz0 : Complex.normSq a0 = 0 := by rw [ha0]; simp
          have hz1 : Complex.normSq a1 = 0 := by rw [ha1]; simp
          have hz2 : Complex.normSq a2 = 0 := by rw [ha2]; simp
          have hz3 : Complex.normSq a3 = 0 := by rw [ha3]; simp
          linarith
        ·
          have hz0 : Complex.normSq a0 = 0 := by rw [ha0]; simp
          have hz1 : Complex.normSq a1 = 0 := by rw [ha1]; simp
          have hz2 : Complex.normSq a2 = 0 := by rw [ha2]; simp
          exact ha3 (branch_lone v3 v0 v1 v2 a3
            (b13 * star b13 + b23 * star b23 + b33 * star b33) (b10 * star b13 + b20 * star b23 + b30 * star b33) (b11 * star b13 + b21 * star b23 + b31 * star b33) (b12 * star b13 + b22 * star b23 + b32 * star b33)
            (Complex.normSq a3) (Complex.normSq a0) (Complex.normSq a1) (Complex.normSq a2)
            (by linear_combination G3) hD3
            (term_of_zero a0 v0 v3 (b10 * star b13 + b20 * star b23 + b30 * star b33) ha0 hK0)
            (term_of_zero a1 v1 v3 (b11 * star b13 + b21 * star b23 + b31 * star b33) ha1 hK1)
            (term_of_zero a2 v2 v3 (b12 * star b13 + b22 * star b23 + b32 * star b33) ha2 hK2)
            (by linarith) hK3)
      ·
        by_cases ha3 : a3 = 0
        ·
          have hz0 : Complex.normSq a0 = 0 := by rw [ha0]; simp
          have hz1 : Complex.normSq a1 = 0 := by rw [ha1]; simp
          have hz3 : Complex.normSq a3 = 0 := by rw [ha3]; simp
          exact ha2 (branch_lone v2 v0 v1 v3 a2
            (b12 * star b12 + b22 * star b22 + b32 * star b32) (b10 * star b12 + b20 * star b22 + b30 * star b32) (b11 * star b12 + b21 * star b22 + b31 * star b32) (b13 * star b12 + b23 * star b22 + b33 * star b32)
            (Complex.normSq a2) (Complex.normSq a0) (Complex.normSq a1) (Complex.normSq a3)
            (by linear_combination G2) hD2
            (term_of_zero a0 v0 v2 (b10 * star b12 + b20 * star b22 + b30 * star b32) ha0 hK0)
            (term_of_zero a1 v1 v2 (b11 * star b12 + b21 * star b22 + b31 * star b32) ha1 hK1)
            (term_of_zero a3 v3 v2 (b13 * star b12 + b23 * star b22 + b33 * star b32) ha3 hK3)
            (by linarith) hK2)
        ·
          have hz0 : Complex.normSq a0 = 0 := by rw [ha0]; simp
          have hz1 : Complex.normSq a1 = 0 := by rw [ha1]; simp
          by_cases hT23 : v2 * star v3 - a2 * star a3 = 0
          · -- the two live columns share a phase
            exact branch_pair a2 a3 v2 v3 v0 v1 b12 b22 b32 b13 b23 b33
              (b12 * star b12 + b22 * star b22 + b32 * star b32) (b13 * star b13 + b23 * star b23 + b33 * star b33) (b12 * star b13 + b22 * star b23 + b32 * star b33) (b13 * star b12 + b23 * star b22 + b33 * star b32)
              (b10 * star b12 + b20 * star b22 + b30 * star b32) (b11 * star b12 + b21 * star b22 + b31 * star b32) (b10 * star b13 + b20 * star b23 + b30 * star b33) (b11 * star b13 + b21 * star b23 + b31 * star b33)
              (Complex.normSq a0) (Complex.normSq a1)
              (by linear_combination G2) (by linear_combination G3)
              (term_of_zero a0 v0 v2 (b10 * star b12 + b20 * star b22 + b30 * star b32) ha0 hK0)
              (term_of_zero a1 v1 v2 (b11 * star b12 + b21 * star b22 + b31 * star b32) ha1 hK1)
              (term_of_zero a0 v0 v3 (b10 * star b13 + b20 * star b23 + b30 * star b33) ha0 hK0)
              (term_of_zero a1 v1 v3 (b11 * star b13 + b21 * star b23 + b31 * star b33) ha1 hK1)
              hD2 hD3 rfl rfl
              (by linarith) n0 n1 hCol2 hCol3
              (by linarith) (by linarith) (by linarith)
              (perm_extract a2 a3 v2 v3 (b12 * b23 + b13 * b22) (by linear_combination hP12_23) hT23 hK3 ha2 ha3)
              (perm_extract a2 a3 v2 v3 (b12 * b33 + b13 * b32) (by linear_combination hP13_23) hT23 hK3 ha2 ha3)
              (perm_extract a2 a3 v2 v3 (b22 * b33 + b23 * b32) (by linear_combination hP23_23) hT23 hK3 ha2 ha3)
              hK2 hK3 ha2 ha3
          · -- column 2 is alone
            exact ha2 (branch_lone v2 v0 v1 v3 a2
              (b12 * star b12 + b22 * star b22 + b32 * star b32) (b10 * star b12 + b20 * star b22 + b30 * star b32) (b11 * star b12 + b21 * star b22 + b31 * star b32) (b13 * star b12 + b23 * star b22 + b33 * star b32)
              (Complex.normSq a2) (Complex.normSq a0) (Complex.normSq a1) (Complex.normSq a3)
              (by linear_combination G2) hD2
              (term_of_zero a0 v0 v2 (b10 * star b12 + b20 * star b22 + b30 * star b32) ha0 hK0)
              (term_of_zero a1 v1 v2 (b11 * star b12 + b21 * star b22 + b31 * star b32) ha1 hK1)
              (term_of_diff a3 v3 v2 (b13 * star b12 + b23 * star b22 + b33 * star b32) hK3 (hM32 (fun hh => hT23 (T_symm a3 a2 v3 v2 hh))))
              (by linarith) hK2)
    ·
      by_cases ha2 : a2 = 0
      ·
        by_cases ha3 : a3 = 0
        ·
          have hz0 : Complex.normSq a0 = 0 := by rw [ha0]; simp
          have hz2 : Complex.normSq a2 = 0 := by rw [ha2]; simp
          have hz3 : Complex.normSq a3 = 0 := by rw [ha3]; simp
          exact ha1 (branch_lone v1 v0 v2 v3 a1
            (b11 * star b11 + b21 * star b21 + b31 * star b31) (b10 * star b11 + b20 * star b21 + b30 * star b31) (b12 * star b11 + b22 * star b21 + b32 * star b31) (b13 * star b11 + b23 * star b21 + b33 * star b31)
            (Complex.normSq a1) (Complex.normSq a0) (Complex.normSq a2) (Complex.normSq a3)
            (by linear_combination G1) hD1
            (term_of_zero a0 v0 v1 (b10 * star b11 + b20 * star b21 + b30 * star b31) ha0 hK0)
            (term_of_zero a2 v2 v1 (b12 * star b11 + b22 * star b21 + b32 * star b31) ha2 hK2)
            (term_of_zero a3 v3 v1 (b13 * star b11 + b23 * star b21 + b33 * star b31) ha3 hK3)
            (by linarith) hK1)
        ·
          have hz0 : Complex.normSq a0 = 0 := by rw [ha0]; simp
          have hz2 : Complex.normSq a2 = 0 := by rw [ha2]; simp
          by_cases hT13 : v1 * star v3 - a1 * star a3 = 0
          · -- the two live columns share a phase
            exact branch_pair a1 a3 v1 v3 v0 v2 b11 b21 b31 b13 b23 b33
              (b11 * star b11 + b21 * star b21 + b31 * star b31) (b13 * star b13 + b23 * star b23 + b33 * star b33) (b11 * star b13 + b21 * star b23 + b31 * star b33) (b13 * star b11 + b23 * star b21 + b33 * star b31)
              (b10 * star b11 + b20 * star b21 + b30 * star b31) (b12 * star b11 + b22 * star b21 + b32 * star b31) (b10 * star b13 + b20 * star b23 + b30 * star b33) (b12 * star b13 + b22 * star b23 + b32 * star b33)
              (Complex.normSq a0) (Complex.normSq a2)
              (by linear_combination G1) (by linear_combination G3)
              (term_of_zero a0 v0 v1 (b10 * star b11 + b20 * star b21 + b30 * star b31) ha0 hK0)
              (term_of_zero a2 v2 v1 (b12 * star b11 + b22 * star b21 + b32 * star b31) ha2 hK2)
              (term_of_zero a0 v0 v3 (b10 * star b13 + b20 * star b23 + b30 * star b33) ha0 hK0)
              (term_of_zero a2 v2 v3 (b12 * star b13 + b22 * star b23 + b32 * star b33) ha2 hK2)
              hD1 hD3 rfl rfl
              (by linarith) n0 n2 hCol1 hCol3
              (by linarith) (by linarith) (by linarith)
              (perm_extract a1 a3 v1 v3 (b11 * b23 + b13 * b21) (by linear_combination hP12_13) hT13 hK3 ha1 ha3)
              (perm_extract a1 a3 v1 v3 (b11 * b33 + b13 * b31) (by linear_combination hP13_13) hT13 hK3 ha1 ha3)
              (perm_extract a1 a3 v1 v3 (b21 * b33 + b23 * b31) (by linear_combination hP23_13) hT13 hK3 ha1 ha3)
              hK1 hK3 ha1 ha3
          · -- column 1 is alone
            exact ha1 (branch_lone v1 v0 v2 v3 a1
              (b11 * star b11 + b21 * star b21 + b31 * star b31) (b10 * star b11 + b20 * star b21 + b30 * star b31) (b12 * star b11 + b22 * star b21 + b32 * star b31) (b13 * star b11 + b23 * star b21 + b33 * star b31)
              (Complex.normSq a1) (Complex.normSq a0) (Complex.normSq a2) (Complex.normSq a3)
              (by linear_combination G1) hD1
              (term_of_zero a0 v0 v1 (b10 * star b11 + b20 * star b21 + b30 * star b31) ha0 hK0)
              (term_of_zero a2 v2 v1 (b12 * star b11 + b22 * star b21 + b32 * star b31) ha2 hK2)
              (term_of_diff a3 v3 v1 (b13 * star b11 + b23 * star b21 + b33 * star b31) hK3 (hM31 (fun hh => hT13 (T_symm a3 a1 v3 v1 hh))))
              (by linarith) hK1)
      ·
        by_cases ha3 : a3 = 0
        ·
          have hz0 : Complex.normSq a0 = 0 := by rw [ha0]; simp
          have hz3 : Complex.normSq a3 = 0 := by rw [ha3]; simp
          by_cases hT12 : v1 * star v2 - a1 * star a2 = 0
          · -- the two live columns share a phase
            exact branch_pair a1 a2 v1 v2 v0 v3 b11 b21 b31 b12 b22 b32
              (b11 * star b11 + b21 * star b21 + b31 * star b31) (b12 * star b12 + b22 * star b22 + b32 * star b32) (b11 * star b12 + b21 * star b22 + b31 * star b32) (b12 * star b11 + b22 * star b21 + b32 * star b31)
              (b10 * star b11 + b20 * star b21 + b30 * star b31) (b13 * star b11 + b23 * star b21 + b33 * star b31) (b10 * star b12 + b20 * star b22 + b30 * star b32) (b13 * star b12 + b23 * star b22 + b33 * star b32)
              (Complex.normSq a0) (Complex.normSq a3)
              (by linear_combination G1) (by linear_combination G2)
              (term_of_zero a0 v0 v1 (b10 * star b11 + b20 * star b21 + b30 * star b31) ha0 hK0)
              (term_of_zero a3 v3 v1 (b13 * star b11 + b23 * star b21 + b33 * star b31) ha3 hK3)
              (term_of_zero a0 v0 v2 (b10 * star b12 + b20 * star b22 + b30 * star b32) ha0 hK0)
              (term_of_zero a3 v3 v2 (b13 * star b12 + b23 * star b22 + b33 * star b32) ha3 hK3)
              hD1 hD2 rfl rfl
              (by linarith) n0 n3 hCol1 hCol2
              (by linarith) (by linarith) (by linarith)
              (perm_extract a1 a2 v1 v2 (b11 * b22 + b12 * b21) (by linear_combination hP12_12) hT12 hK2 ha1 ha2)
              (perm_extract a1 a2 v1 v2 (b11 * b32 + b12 * b31) (by linear_combination hP13_12) hT12 hK2 ha1 ha2)
              (perm_extract a1 a2 v1 v2 (b21 * b32 + b22 * b31) (by linear_combination hP23_12) hT12 hK2 ha1 ha2)
              hK1 hK2 ha1 ha2
          · -- column 1 is alone
            exact ha1 (branch_lone v1 v0 v2 v3 a1
              (b11 * star b11 + b21 * star b21 + b31 * star b31) (b10 * star b11 + b20 * star b21 + b30 * star b31) (b12 * star b11 + b22 * star b21 + b32 * star b31) (b13 * star b11 + b23 * star b21 + b33 * star b31)
              (Complex.normSq a1) (Complex.normSq a0) (Complex.normSq a2) (Complex.normSq a3)
              (by linear_combination G1) hD1
              (term_of_zero a0 v0 v1 (b10 * star b11 + b20 * star b21 + b30 * star b31) ha0 hK0)
              (term_of_diff a2 v2 v1 (b12 * star b11 + b22 * star b21 + b32 * star b31) hK2 (hM21 (fun hh => hT12 (T_symm a2 a1 v2 v1 hh))))
              (term_of_zero a3 v3 v1 (b13 * star b11 + b23 * star b21 + b33 * star b31) ha3 hK3)
              (by linarith) hK1)
        ·
          have hz0 : Complex.normSq a0 = 0 := by rw [ha0]; simp
          by_cases hT12 : v1 * star v2 - a1 * star a2 = 0
          · by_cases hT13 : v1 * star v3 - a1 * star a3 = 0
            · have hT23 : v2 * star v3 - a2 * star a3 = 0 :=
                (T_trans a2 a1 a3 v2 v1 v3 (T_symm a1 a2 v1 v2 hT12) hT13 hK1 ha1)
              exact branch_triple b11 b12 b13 b10 b21 b22 b23 b20 b31 b32 b33
                (Complex.normSq a1) (Complex.normSq a2) (Complex.normSq a3) n1 n2 n3
                (by linarith) (by linarith)
                hCol1 hCol2 hCol3 (by linarith)
                (perm_extract a1 a2 v1 v2 (b11 * b22 + b12 * b21) (by linear_combination hP12_12) hT12 hK2 ha1 ha2)
                (perm_extract a1 a3 v1 v3 (b11 * b23 + b13 * b21) (by linear_combination hP12_13) hT13 hK3 ha1 ha3)
                (perm_extract a2 a3 v2 v3 (b12 * b23 + b13 * b22) (by linear_combination hP12_23) hT23 hK3 ha2 ha3)
                (perm_extract a1 a2 v1 v2 (b11 * b32 + b12 * b31) (by linear_combination hP13_12) hT12 hK2 ha1 ha2)
                (perm_extract a1 a3 v1 v3 (b11 * b33 + b13 * b31) (by linear_combination hP13_13) hT13 hK3 ha1 ha3)
                (perm_extract a2 a3 v2 v3 (b12 * b33 + b13 * b32) (by linear_combination hP13_23) hT23 hK3 ha2 ha3)
                (perm_extract a1 a2 v1 v2 (b21 * b32 + b22 * b31) (by linear_combination hP23_12) hT12 hK2 ha1 ha2)
                (perm_extract a1 a3 v1 v3 (b21 * b33 + b23 * b31) (by linear_combination hP23_13) hT13 hK3 ha1 ha3)
            · have hT23 : ¬ (v2 * star v3 - a2 * star a3 = 0) := fun hh =>
                hT13 (T_trans a1 a2 a3 v1 v2 v3 hT12 hh hK2 ha2)
              exact ha3 (branch_lone v3 v0 v1 v2 a3
                (b13 * star b13 + b23 * star b23 + b33 * star b33) (b10 * star b13 + b20 * star b23 + b30 * star b33) (b11 * star b13 + b21 * star b23 + b31 * star b33) (b12 * star b13 + b22 * star b23 + b32 * star b33)
                (Complex.normSq a3) (Complex.normSq a0) (Complex.normSq a1) (Complex.normSq a2)
                (by linear_combination G3) hD3
                (term_of_zero a0 v0 v3 (b10 * star b13 + b20 * star b23 + b30 * star b33) ha0 hK0)
                (term_of_diff a1 v1 v3 (b11 * star b13 + b21 * star b23 + b31 * star b33) hK1 (hM13 hT13))
                (term_of_diff a2 v2 v3 (b12 * star b13 + b22 * star b23 + b32 * star b33) hK2 (hM23 hT23))
                (by linarith) hK3)
          · by_cases hT13 : v1 * star v3 - a1 * star a3 = 0
            · have hT23 : ¬ (v2 * star v3 - a2 * star a3 = 0) := fun hh =>
                hT12 (T_trans a1 a3 a2 v1 v3 v2 hT13 (T_symm a2 a3 v2 v3 hh) hK3 ha3)
              exact ha2 (branch_lone v2 v0 v1 v3 a2
                (b12 * star b12 + b22 * star b22 + b32 * star b32) (b10 * star b12 + b20 * star b22 + b30 * star b32) (b11 * star b12 + b21 * star b22 + b31 * star b32) (b13 * star b12 + b23 * star b22 + b33 * star b32)
                (Complex.normSq a2) (Complex.normSq a0) (Complex.normSq a1) (Complex.normSq a3)
                (by linear_combination G2) hD2
                (term_of_zero a0 v0 v2 (b10 * star b12 + b20 * star b22 + b30 * star b32) ha0 hK0)
                (term_of_diff a1 v1 v2 (b11 * star b12 + b21 * star b22 + b31 * star b32) hK1 (hM12 hT12))
                (term_of_diff a3 v3 v2 (b13 * star b12 + b23 * star b22 + b33 * star b32) hK3 (hM32 (fun hh => hT23 (T_symm a3 a2 v3 v2 hh))))
                (by linarith) hK2)
            · -- column 1 is alone
              exact ha1 (branch_lone v1 v0 v2 v3 a1
                (b11 * star b11 + b21 * star b21 + b31 * star b31) (b10 * star b11 + b20 * star b21 + b30 * star b31) (b12 * star b11 + b22 * star b21 + b32 * star b31) (b13 * star b11 + b23 * star b21 + b33 * star b31)
                (Complex.normSq a1) (Complex.normSq a0) (Complex.normSq a2) (Complex.normSq a3)
                (by linear_combination G1) hD1
                (term_of_zero a0 v0 v1 (b10 * star b11 + b20 * star b21 + b30 * star b31) ha0 hK0)
                (term_of_diff a2 v2 v1 (b12 * star b11 + b22 * star b21 + b32 * star b31) hK2 (hM21 (fun hh => hT12 (T_symm a2 a1 v2 v1 hh))))
                (term_of_diff a3 v3 v1 (b13 * star b11 + b23 * star b21 + b33 * star b31) hK3 (hM31 (fun hh => hT13 (T_symm a3 a1 v3 v1 hh))))
                (by linarith) hK1)
  ·
    by_cases ha1 : a1 = 0
    ·
      by_cases ha2 : a2 = 0
      ·
        by_cases ha3 : a3 = 0
        ·
          have hz1 : Complex.normSq a1 = 0 := by rw [ha1]; simp
          have hz2 : Complex.normSq a2 = 0 := by rw [ha2]; simp
          have hz3 : Complex.normSq a3 = 0 := by rw [ha3]; simp
          exact ha0 (branch_lone v0 v1 v2 v3 a0
            (b10 * star b10 + b20 * star b20 + b30 * star b30) (b11 * star b10 + b21 * star b20 + b31 * star b30) (b12 * star b10 + b22 * star b20 + b32 * star b30) (b13 * star b10 + b23 * star b20 + b33 * star b30)
            (Complex.normSq a0) (Complex.normSq a1) (Complex.normSq a2) (Complex.normSq a3)
            (by linear_combination G0) hD0
            (term_of_zero a1 v1 v0 (b11 * star b10 + b21 * star b20 + b31 * star b30) ha1 hK1)
            (term_of_zero a2 v2 v0 (b12 * star b10 + b22 * star b20 + b32 * star b30) ha2 hK2)
            (term_of_zero a3 v3 v0 (b13 * star b10 + b23 * star b20 + b33 * star b30) ha3 hK3)
            (by linarith) hK0)
        ·
          have hz1 : Complex.normSq a1 = 0 := by rw [ha1]; simp
          have hz2 : Complex.normSq a2 = 0 := by rw [ha2]; simp
          by_cases hT03 : v0 * star v3 - a0 * star a3 = 0
          · -- the two live columns share a phase
            exact branch_pair a0 a3 v0 v3 v1 v2 b10 b20 b30 b13 b23 b33
              (b10 * star b10 + b20 * star b20 + b30 * star b30) (b13 * star b13 + b23 * star b23 + b33 * star b33) (b10 * star b13 + b20 * star b23 + b30 * star b33) (b13 * star b10 + b23 * star b20 + b33 * star b30)
              (b11 * star b10 + b21 * star b20 + b31 * star b30) (b12 * star b10 + b22 * star b20 + b32 * star b30) (b11 * star b13 + b21 * star b23 + b31 * star b33) (b12 * star b13 + b22 * star b23 + b32 * star b33)
              (Complex.normSq a1) (Complex.normSq a2)
              (by linear_combination G0) (by linear_combination G3)
              (term_of_zero a1 v1 v0 (b11 * star b10 + b21 * star b20 + b31 * star b30) ha1 hK1)
              (term_of_zero a2 v2 v0 (b12 * star b10 + b22 * star b20 + b32 * star b30) ha2 hK2)
              (term_of_zero a1 v1 v3 (b11 * star b13 + b21 * star b23 + b31 * star b33) ha1 hK1)
              (term_of_zero a2 v2 v3 (b12 * star b13 + b22 * star b23 + b32 * star b33) ha2 hK2)
              hD0 hD3 rfl rfl
              (by linarith) n1 n2 hCol0 hCol3
              (by linarith) (by linarith) (by linarith)
              (perm_extract a0 a3 v0 v3 (b10 * b23 + b13 * b20) (by linear_combination hP12_03) hT03 hK3 ha0 ha3)
              (perm_extract a0 a3 v0 v3 (b10 * b33 + b13 * b30) (by linear_combination hP13_03) hT03 hK3 ha0 ha3)
              (perm_extract a0 a3 v0 v3 (b20 * b33 + b23 * b30) (by linear_combination hP23_03) hT03 hK3 ha0 ha3)
              hK0 hK3 ha0 ha3
          · -- column 0 is alone
            exact ha0 (branch_lone v0 v1 v2 v3 a0
              (b10 * star b10 + b20 * star b20 + b30 * star b30) (b11 * star b10 + b21 * star b20 + b31 * star b30) (b12 * star b10 + b22 * star b20 + b32 * star b30) (b13 * star b10 + b23 * star b20 + b33 * star b30)
              (Complex.normSq a0) (Complex.normSq a1) (Complex.normSq a2) (Complex.normSq a3)
              (by linear_combination G0) hD0
              (term_of_zero a1 v1 v0 (b11 * star b10 + b21 * star b20 + b31 * star b30) ha1 hK1)
              (term_of_zero a2 v2 v0 (b12 * star b10 + b22 * star b20 + b32 * star b30) ha2 hK2)
              (term_of_diff a3 v3 v0 (b13 * star b10 + b23 * star b20 + b33 * star b30) hK3 (hM30 (fun hh => hT03 (T_symm a3 a0 v3 v0 hh))))
              (by linarith) hK0)
      ·
        by_cases ha3 : a3 = 0
        ·
          have hz1 : Complex.normSq a1 = 0 := by rw [ha1]; simp
          have hz3 : Complex.normSq a3 = 0 := by rw [ha3]; simp
          by_cases hT02 : v0 * star v2 - a0 * star a2 = 0
          · -- the two live columns share a phase
            exact branch_pair a0 a2 v0 v2 v1 v3 b10 b20 b30 b12 b22 b32
              (b10 * star b10 + b20 * star b20 + b30 * star b30) (b12 * star b12 + b22 * star b22 + b32 * star b32) (b10 * star b12 + b20 * star b22 + b30 * star b32) (b12 * star b10 + b22 * star b20 + b32 * star b30)
              (b11 * star b10 + b21 * star b20 + b31 * star b30) (b13 * star b10 + b23 * star b20 + b33 * star b30) (b11 * star b12 + b21 * star b22 + b31 * star b32) (b13 * star b12 + b23 * star b22 + b33 * star b32)
              (Complex.normSq a1) (Complex.normSq a3)
              (by linear_combination G0) (by linear_combination G2)
              (term_of_zero a1 v1 v0 (b11 * star b10 + b21 * star b20 + b31 * star b30) ha1 hK1)
              (term_of_zero a3 v3 v0 (b13 * star b10 + b23 * star b20 + b33 * star b30) ha3 hK3)
              (term_of_zero a1 v1 v2 (b11 * star b12 + b21 * star b22 + b31 * star b32) ha1 hK1)
              (term_of_zero a3 v3 v2 (b13 * star b12 + b23 * star b22 + b33 * star b32) ha3 hK3)
              hD0 hD2 rfl rfl
              (by linarith) n1 n3 hCol0 hCol2
              (by linarith) (by linarith) (by linarith)
              (perm_extract a0 a2 v0 v2 (b10 * b22 + b12 * b20) (by linear_combination hP12_02) hT02 hK2 ha0 ha2)
              (perm_extract a0 a2 v0 v2 (b10 * b32 + b12 * b30) (by linear_combination hP13_02) hT02 hK2 ha0 ha2)
              (perm_extract a0 a2 v0 v2 (b20 * b32 + b22 * b30) (by linear_combination hP23_02) hT02 hK2 ha0 ha2)
              hK0 hK2 ha0 ha2
          · -- column 0 is alone
            exact ha0 (branch_lone v0 v1 v2 v3 a0
              (b10 * star b10 + b20 * star b20 + b30 * star b30) (b11 * star b10 + b21 * star b20 + b31 * star b30) (b12 * star b10 + b22 * star b20 + b32 * star b30) (b13 * star b10 + b23 * star b20 + b33 * star b30)
              (Complex.normSq a0) (Complex.normSq a1) (Complex.normSq a2) (Complex.normSq a3)
              (by linear_combination G0) hD0
              (term_of_zero a1 v1 v0 (b11 * star b10 + b21 * star b20 + b31 * star b30) ha1 hK1)
              (term_of_diff a2 v2 v0 (b12 * star b10 + b22 * star b20 + b32 * star b30) hK2 (hM20 (fun hh => hT02 (T_symm a2 a0 v2 v0 hh))))
              (term_of_zero a3 v3 v0 (b13 * star b10 + b23 * star b20 + b33 * star b30) ha3 hK3)
              (by linarith) hK0)
        ·
          have hz1 : Complex.normSq a1 = 0 := by rw [ha1]; simp
          by_cases hT02 : v0 * star v2 - a0 * star a2 = 0
          · by_cases hT03 : v0 * star v3 - a0 * star a3 = 0
            · have hT23 : v2 * star v3 - a2 * star a3 = 0 :=
                (T_trans a2 a0 a3 v2 v0 v3 (T_symm a0 a2 v0 v2 hT02) hT03 hK0 ha0)
              exact branch_triple b10 b12 b13 b11 b20 b22 b23 b21 b30 b32 b33
                (Complex.normSq a0) (Complex.normSq a2) (Complex.normSq a3) n0 n2 n3
                (by linarith) (by linarith)
                hCol0 hCol2 hCol3 (by linarith)
                (perm_extract a0 a2 v0 v2 (b10 * b22 + b12 * b20) (by linear_combination hP12_02) hT02 hK2 ha0 ha2)
                (perm_extract a0 a3 v0 v3 (b10 * b23 + b13 * b20) (by linear_combination hP12_03) hT03 hK3 ha0 ha3)
                (perm_extract a2 a3 v2 v3 (b12 * b23 + b13 * b22) (by linear_combination hP12_23) hT23 hK3 ha2 ha3)
                (perm_extract a0 a2 v0 v2 (b10 * b32 + b12 * b30) (by linear_combination hP13_02) hT02 hK2 ha0 ha2)
                (perm_extract a0 a3 v0 v3 (b10 * b33 + b13 * b30) (by linear_combination hP13_03) hT03 hK3 ha0 ha3)
                (perm_extract a2 a3 v2 v3 (b12 * b33 + b13 * b32) (by linear_combination hP13_23) hT23 hK3 ha2 ha3)
                (perm_extract a0 a2 v0 v2 (b20 * b32 + b22 * b30) (by linear_combination hP23_02) hT02 hK2 ha0 ha2)
                (perm_extract a0 a3 v0 v3 (b20 * b33 + b23 * b30) (by linear_combination hP23_03) hT03 hK3 ha0 ha3)
            · have hT23 : ¬ (v2 * star v3 - a2 * star a3 = 0) := fun hh =>
                hT03 (T_trans a0 a2 a3 v0 v2 v3 hT02 hh hK2 ha2)
              exact ha3 (branch_lone v3 v0 v1 v2 a3
                (b13 * star b13 + b23 * star b23 + b33 * star b33) (b10 * star b13 + b20 * star b23 + b30 * star b33) (b11 * star b13 + b21 * star b23 + b31 * star b33) (b12 * star b13 + b22 * star b23 + b32 * star b33)
                (Complex.normSq a3) (Complex.normSq a0) (Complex.normSq a1) (Complex.normSq a2)
                (by linear_combination G3) hD3
                (term_of_diff a0 v0 v3 (b10 * star b13 + b20 * star b23 + b30 * star b33) hK0 (hM03 hT03))
                (term_of_zero a1 v1 v3 (b11 * star b13 + b21 * star b23 + b31 * star b33) ha1 hK1)
                (term_of_diff a2 v2 v3 (b12 * star b13 + b22 * star b23 + b32 * star b33) hK2 (hM23 hT23))
                (by linarith) hK3)
          · by_cases hT03 : v0 * star v3 - a0 * star a3 = 0
            · have hT23 : ¬ (v2 * star v3 - a2 * star a3 = 0) := fun hh =>
                hT02 (T_trans a0 a3 a2 v0 v3 v2 hT03 (T_symm a2 a3 v2 v3 hh) hK3 ha3)
              exact ha2 (branch_lone v2 v0 v1 v3 a2
                (b12 * star b12 + b22 * star b22 + b32 * star b32) (b10 * star b12 + b20 * star b22 + b30 * star b32) (b11 * star b12 + b21 * star b22 + b31 * star b32) (b13 * star b12 + b23 * star b22 + b33 * star b32)
                (Complex.normSq a2) (Complex.normSq a0) (Complex.normSq a1) (Complex.normSq a3)
                (by linear_combination G2) hD2
                (term_of_diff a0 v0 v2 (b10 * star b12 + b20 * star b22 + b30 * star b32) hK0 (hM02 hT02))
                (term_of_zero a1 v1 v2 (b11 * star b12 + b21 * star b22 + b31 * star b32) ha1 hK1)
                (term_of_diff a3 v3 v2 (b13 * star b12 + b23 * star b22 + b33 * star b32) hK3 (hM32 (fun hh => hT23 (T_symm a3 a2 v3 v2 hh))))
                (by linarith) hK2)
            · -- column 0 is alone
              exact ha0 (branch_lone v0 v1 v2 v3 a0
                (b10 * star b10 + b20 * star b20 + b30 * star b30) (b11 * star b10 + b21 * star b20 + b31 * star b30) (b12 * star b10 + b22 * star b20 + b32 * star b30) (b13 * star b10 + b23 * star b20 + b33 * star b30)
                (Complex.normSq a0) (Complex.normSq a1) (Complex.normSq a2) (Complex.normSq a3)
                (by linear_combination G0) hD0
                (term_of_zero a1 v1 v0 (b11 * star b10 + b21 * star b20 + b31 * star b30) ha1 hK1)
                (term_of_diff a2 v2 v0 (b12 * star b10 + b22 * star b20 + b32 * star b30) hK2 (hM20 (fun hh => hT02 (T_symm a2 a0 v2 v0 hh))))
                (term_of_diff a3 v3 v0 (b13 * star b10 + b23 * star b20 + b33 * star b30) hK3 (hM30 (fun hh => hT03 (T_symm a3 a0 v3 v0 hh))))
                (by linarith) hK0)
    ·
      by_cases ha2 : a2 = 0
      ·
        by_cases ha3 : a3 = 0
        ·
          have hz2 : Complex.normSq a2 = 0 := by rw [ha2]; simp
          have hz3 : Complex.normSq a3 = 0 := by rw [ha3]; simp
          by_cases hT01 : v0 * star v1 - a0 * star a1 = 0
          · -- the two live columns share a phase
            exact branch_pair a0 a1 v0 v1 v2 v3 b10 b20 b30 b11 b21 b31
              (b10 * star b10 + b20 * star b20 + b30 * star b30) (b11 * star b11 + b21 * star b21 + b31 * star b31) (b10 * star b11 + b20 * star b21 + b30 * star b31) (b11 * star b10 + b21 * star b20 + b31 * star b30)
              (b12 * star b10 + b22 * star b20 + b32 * star b30) (b13 * star b10 + b23 * star b20 + b33 * star b30) (b12 * star b11 + b22 * star b21 + b32 * star b31) (b13 * star b11 + b23 * star b21 + b33 * star b31)
              (Complex.normSq a2) (Complex.normSq a3)
              (by linear_combination G0) (by linear_combination G1)
              (term_of_zero a2 v2 v0 (b12 * star b10 + b22 * star b20 + b32 * star b30) ha2 hK2)
              (term_of_zero a3 v3 v0 (b13 * star b10 + b23 * star b20 + b33 * star b30) ha3 hK3)
              (term_of_zero a2 v2 v1 (b12 * star b11 + b22 * star b21 + b32 * star b31) ha2 hK2)
              (term_of_zero a3 v3 v1 (b13 * star b11 + b23 * star b21 + b33 * star b31) ha3 hK3)
              hD0 hD1 rfl rfl
              (by linarith) n2 n3 hCol0 hCol1
              (by linarith) (by linarith) (by linarith)
              (perm_extract a0 a1 v0 v1 (b10 * b21 + b11 * b20) (by linear_combination hP12_01) hT01 hK1 ha0 ha1)
              (perm_extract a0 a1 v0 v1 (b10 * b31 + b11 * b30) (by linear_combination hP13_01) hT01 hK1 ha0 ha1)
              (perm_extract a0 a1 v0 v1 (b20 * b31 + b21 * b30) (by linear_combination hP23_01) hT01 hK1 ha0 ha1)
              hK0 hK1 ha0 ha1
          · -- column 0 is alone
            exact ha0 (branch_lone v0 v1 v2 v3 a0
              (b10 * star b10 + b20 * star b20 + b30 * star b30) (b11 * star b10 + b21 * star b20 + b31 * star b30) (b12 * star b10 + b22 * star b20 + b32 * star b30) (b13 * star b10 + b23 * star b20 + b33 * star b30)
              (Complex.normSq a0) (Complex.normSq a1) (Complex.normSq a2) (Complex.normSq a3)
              (by linear_combination G0) hD0
              (term_of_diff a1 v1 v0 (b11 * star b10 + b21 * star b20 + b31 * star b30) hK1 (hM10 (fun hh => hT01 (T_symm a1 a0 v1 v0 hh))))
              (term_of_zero a2 v2 v0 (b12 * star b10 + b22 * star b20 + b32 * star b30) ha2 hK2)
              (term_of_zero a3 v3 v0 (b13 * star b10 + b23 * star b20 + b33 * star b30) ha3 hK3)
              (by linarith) hK0)
        ·
          have hz2 : Complex.normSq a2 = 0 := by rw [ha2]; simp
          by_cases hT01 : v0 * star v1 - a0 * star a1 = 0
          · by_cases hT03 : v0 * star v3 - a0 * star a3 = 0
            · have hT13 : v1 * star v3 - a1 * star a3 = 0 :=
                (T_trans a1 a0 a3 v1 v0 v3 (T_symm a0 a1 v0 v1 hT01) hT03 hK0 ha0)
              exact branch_triple b10 b11 b13 b12 b20 b21 b23 b22 b30 b31 b33
                (Complex.normSq a0) (Complex.normSq a1) (Complex.normSq a3) n0 n1 n3
                (by linarith) (by linarith)
                hCol0 hCol1 hCol3 (by linarith)
                (perm_extract a0 a1 v0 v1 (b10 * b21 + b11 * b20) (by linear_combination hP12_01) hT01 hK1 ha0 ha1)
                (perm_extract a0 a3 v0 v3 (b10 * b23 + b13 * b20) (by linear_combination hP12_03) hT03 hK3 ha0 ha3)
                (perm_extract a1 a3 v1 v3 (b11 * b23 + b13 * b21) (by linear_combination hP12_13) hT13 hK3 ha1 ha3)
                (perm_extract a0 a1 v0 v1 (b10 * b31 + b11 * b30) (by linear_combination hP13_01) hT01 hK1 ha0 ha1)
                (perm_extract a0 a3 v0 v3 (b10 * b33 + b13 * b30) (by linear_combination hP13_03) hT03 hK3 ha0 ha3)
                (perm_extract a1 a3 v1 v3 (b11 * b33 + b13 * b31) (by linear_combination hP13_13) hT13 hK3 ha1 ha3)
                (perm_extract a0 a1 v0 v1 (b20 * b31 + b21 * b30) (by linear_combination hP23_01) hT01 hK1 ha0 ha1)
                (perm_extract a0 a3 v0 v3 (b20 * b33 + b23 * b30) (by linear_combination hP23_03) hT03 hK3 ha0 ha3)
            · have hT13 : ¬ (v1 * star v3 - a1 * star a3 = 0) := fun hh =>
                hT03 (T_trans a0 a1 a3 v0 v1 v3 hT01 hh hK1 ha1)
              exact ha3 (branch_lone v3 v0 v1 v2 a3
                (b13 * star b13 + b23 * star b23 + b33 * star b33) (b10 * star b13 + b20 * star b23 + b30 * star b33) (b11 * star b13 + b21 * star b23 + b31 * star b33) (b12 * star b13 + b22 * star b23 + b32 * star b33)
                (Complex.normSq a3) (Complex.normSq a0) (Complex.normSq a1) (Complex.normSq a2)
                (by linear_combination G3) hD3
                (term_of_diff a0 v0 v3 (b10 * star b13 + b20 * star b23 + b30 * star b33) hK0 (hM03 hT03))
                (term_of_diff a1 v1 v3 (b11 * star b13 + b21 * star b23 + b31 * star b33) hK1 (hM13 hT13))
                (term_of_zero a2 v2 v3 (b12 * star b13 + b22 * star b23 + b32 * star b33) ha2 hK2)
                (by linarith) hK3)
          · by_cases hT03 : v0 * star v3 - a0 * star a3 = 0
            · have hT13 : ¬ (v1 * star v3 - a1 * star a3 = 0) := fun hh =>
                hT01 (T_trans a0 a3 a1 v0 v3 v1 hT03 (T_symm a1 a3 v1 v3 hh) hK3 ha3)
              exact ha1 (branch_lone v1 v0 v2 v3 a1
                (b11 * star b11 + b21 * star b21 + b31 * star b31) (b10 * star b11 + b20 * star b21 + b30 * star b31) (b12 * star b11 + b22 * star b21 + b32 * star b31) (b13 * star b11 + b23 * star b21 + b33 * star b31)
                (Complex.normSq a1) (Complex.normSq a0) (Complex.normSq a2) (Complex.normSq a3)
                (by linear_combination G1) hD1
                (term_of_diff a0 v0 v1 (b10 * star b11 + b20 * star b21 + b30 * star b31) hK0 (hM01 hT01))
                (term_of_zero a2 v2 v1 (b12 * star b11 + b22 * star b21 + b32 * star b31) ha2 hK2)
                (term_of_diff a3 v3 v1 (b13 * star b11 + b23 * star b21 + b33 * star b31) hK3 (hM31 (fun hh => hT13 (T_symm a3 a1 v3 v1 hh))))
                (by linarith) hK1)
            · -- column 0 is alone
              exact ha0 (branch_lone v0 v1 v2 v3 a0
                (b10 * star b10 + b20 * star b20 + b30 * star b30) (b11 * star b10 + b21 * star b20 + b31 * star b30) (b12 * star b10 + b22 * star b20 + b32 * star b30) (b13 * star b10 + b23 * star b20 + b33 * star b30)
                (Complex.normSq a0) (Complex.normSq a1) (Complex.normSq a2) (Complex.normSq a3)
                (by linear_combination G0) hD0
                (term_of_diff a1 v1 v0 (b11 * star b10 + b21 * star b20 + b31 * star b30) hK1 (hM10 (fun hh => hT01 (T_symm a1 a0 v1 v0 hh))))
                (term_of_zero a2 v2 v0 (b12 * star b10 + b22 * star b20 + b32 * star b30) ha2 hK2)
                (term_of_diff a3 v3 v0 (b13 * star b10 + b23 * star b20 + b33 * star b30) hK3 (hM30 (fun hh => hT03 (T_symm a3 a0 v3 v0 hh))))
                (by linarith) hK0)
      ·
        by_cases ha3 : a3 = 0
        ·
          have hz3 : Complex.normSq a3 = 0 := by rw [ha3]; simp
          by_cases hT01 : v0 * star v1 - a0 * star a1 = 0
          · by_cases hT02 : v0 * star v2 - a0 * star a2 = 0
            · have hT12 : v1 * star v2 - a1 * star a2 = 0 :=
                (T_trans a1 a0 a2 v1 v0 v2 (T_symm a0 a1 v0 v1 hT01) hT02 hK0 ha0)
              exact branch_triple b10 b11 b12 b13 b20 b21 b22 b23 b30 b31 b32
                (Complex.normSq a0) (Complex.normSq a1) (Complex.normSq a2) n0 n1 n2
                (by linarith) (by linarith)
                hCol0 hCol1 hCol2 (by linarith)
                (perm_extract a0 a1 v0 v1 (b10 * b21 + b11 * b20) (by linear_combination hP12_01) hT01 hK1 ha0 ha1)
                (perm_extract a0 a2 v0 v2 (b10 * b22 + b12 * b20) (by linear_combination hP12_02) hT02 hK2 ha0 ha2)
                (perm_extract a1 a2 v1 v2 (b11 * b22 + b12 * b21) (by linear_combination hP12_12) hT12 hK2 ha1 ha2)
                (perm_extract a0 a1 v0 v1 (b10 * b31 + b11 * b30) (by linear_combination hP13_01) hT01 hK1 ha0 ha1)
                (perm_extract a0 a2 v0 v2 (b10 * b32 + b12 * b30) (by linear_combination hP13_02) hT02 hK2 ha0 ha2)
                (perm_extract a1 a2 v1 v2 (b11 * b32 + b12 * b31) (by linear_combination hP13_12) hT12 hK2 ha1 ha2)
                (perm_extract a0 a1 v0 v1 (b20 * b31 + b21 * b30) (by linear_combination hP23_01) hT01 hK1 ha0 ha1)
                (perm_extract a0 a2 v0 v2 (b20 * b32 + b22 * b30) (by linear_combination hP23_02) hT02 hK2 ha0 ha2)
            · have hT12 : ¬ (v1 * star v2 - a1 * star a2 = 0) := fun hh =>
                hT02 (T_trans a0 a1 a2 v0 v1 v2 hT01 hh hK1 ha1)
              exact ha2 (branch_lone v2 v0 v1 v3 a2
                (b12 * star b12 + b22 * star b22 + b32 * star b32) (b10 * star b12 + b20 * star b22 + b30 * star b32) (b11 * star b12 + b21 * star b22 + b31 * star b32) (b13 * star b12 + b23 * star b22 + b33 * star b32)
                (Complex.normSq a2) (Complex.normSq a0) (Complex.normSq a1) (Complex.normSq a3)
                (by linear_combination G2) hD2
                (term_of_diff a0 v0 v2 (b10 * star b12 + b20 * star b22 + b30 * star b32) hK0 (hM02 hT02))
                (term_of_diff a1 v1 v2 (b11 * star b12 + b21 * star b22 + b31 * star b32) hK1 (hM12 hT12))
                (term_of_zero a3 v3 v2 (b13 * star b12 + b23 * star b22 + b33 * star b32) ha3 hK3)
                (by linarith) hK2)
          · by_cases hT02 : v0 * star v2 - a0 * star a2 = 0
            · have hT12 : ¬ (v1 * star v2 - a1 * star a2 = 0) := fun hh =>
                hT01 (T_trans a0 a2 a1 v0 v2 v1 hT02 (T_symm a1 a2 v1 v2 hh) hK2 ha2)
              exact ha1 (branch_lone v1 v0 v2 v3 a1
                (b11 * star b11 + b21 * star b21 + b31 * star b31) (b10 * star b11 + b20 * star b21 + b30 * star b31) (b12 * star b11 + b22 * star b21 + b32 * star b31) (b13 * star b11 + b23 * star b21 + b33 * star b31)
                (Complex.normSq a1) (Complex.normSq a0) (Complex.normSq a2) (Complex.normSq a3)
                (by linear_combination G1) hD1
                (term_of_diff a0 v0 v1 (b10 * star b11 + b20 * star b21 + b30 * star b31) hK0 (hM01 hT01))
                (term_of_diff a2 v2 v1 (b12 * star b11 + b22 * star b21 + b32 * star b31) hK2 (hM21 (fun hh => hT12 (T_symm a2 a1 v2 v1 hh))))
                (term_of_zero a3 v3 v1 (b13 * star b11 + b23 * star b21 + b33 * star b31) ha3 hK3)
                (by linarith) hK1)
            · -- column 0 is alone
              exact ha0 (branch_lone v0 v1 v2 v3 a0
                (b10 * star b10 + b20 * star b20 + b30 * star b30) (b11 * star b10 + b21 * star b20 + b31 * star b30) (b12 * star b10 + b22 * star b20 + b32 * star b30) (b13 * star b10 + b23 * star b20 + b33 * star b30)
                (Complex.normSq a0) (Complex.normSq a1) (Complex.normSq a2) (Complex.normSq a3)
                (by linear_combination G0) hD0
                (term_of_diff a1 v1 v0 (b11 * star b10 + b21 * star b20 + b31 * star b30) hK1 (hM10 (fun hh => hT01 (T_symm a1 a0 v1 v0 hh))))
                (term_of_diff a2 v2 v0 (b12 * star b10 + b22 * star b20 + b32 * star b30) hK2 (hM20 (fun hh => hT02 (T_symm a2 a0 v2 v0 hh))))
                (term_of_zero a3 v3 v0 (b13 * star b10 + b23 * star b20 + b33 * star b30) ha3 hK3)
                (by linarith) hK0)
        ·
          by_cases hT01 : v0 * star v1 - a0 * star a1 = 0
          · by_cases hT02 : v0 * star v2 - a0 * star a2 = 0
            · by_cases hT03 : v0 * star v3 - a0 * star a3 = 0
              · have hT12 : v1 * star v2 - a1 * star a2 = 0 :=
                  (T_trans a1 a0 a2 v1 v0 v2 (T_symm a0 a1 v0 v1 hT01) hT02 hK0 ha0)
                have hT13 : v1 * star v3 - a1 * star a3 = 0 :=
                  (T_trans a1 a0 a3 v1 v0 v3 (T_symm a0 a1 v0 v1 hT01) hT03 hK0 ha0)
                have hT23 : v2 * star v3 - a2 * star a3 = 0 :=
                  (T_trans a2 a0 a3 v2 v0 v3 (T_symm a0 a2 v0 v2 hT02) hT03 hK0 ha0)
                exact branch_quad b10 b11 b12 b13 b20 b21 b22 b23 b30 b31 b32 b33
                  (Complex.normSq a0) (Complex.normSq a1) (Complex.normSq a2) n0 n1 n2
                  hRow1 hRow2 hCol0 hCol1 hCol2
                  (perm_extract a0 a1 v0 v1 (b10 * b21 + b11 * b20) (by linear_combination hP12_01) hT01 hK1 ha0 ha1)
                  (perm_extract a0 a2 v0 v2 (b10 * b22 + b12 * b20) (by linear_combination hP12_02) hT02 hK2 ha0 ha2)
                  (perm_extract a0 a3 v0 v3 (b10 * b23 + b13 * b20) (by linear_combination hP12_03) hT03 hK3 ha0 ha3)
                  (perm_extract a1 a2 v1 v2 (b11 * b22 + b12 * b21) (by linear_combination hP12_12) hT12 hK2 ha1 ha2)
                  (perm_extract a1 a3 v1 v3 (b11 * b23 + b13 * b21) (by linear_combination hP12_13) hT13 hK3 ha1 ha3)
                  (perm_extract a2 a3 v2 v3 (b12 * b23 + b13 * b22) (by linear_combination hP12_23) hT23 hK3 ha2 ha3)
                  (perm_extract a0 a1 v0 v1 (b10 * b31 + b11 * b30) (by linear_combination hP13_01) hT01 hK1 ha0 ha1)
                  (perm_extract a0 a2 v0 v2 (b10 * b32 + b12 * b30) (by linear_combination hP13_02) hT02 hK2 ha0 ha2)
                  (perm_extract a1 a2 v1 v2 (b11 * b32 + b12 * b31) (by linear_combination hP13_12) hT12 hK2 ha1 ha2)
                  (perm_extract a1 a3 v1 v3 (b11 * b33 + b13 * b31) (by linear_combination hP13_13) hT13 hK3 ha1 ha3)
                  (perm_extract a2 a3 v2 v3 (b12 * b33 + b13 * b32) (by linear_combination hP13_23) hT23 hK3 ha2 ha3)
                  (perm_extract a0 a1 v0 v1 (b20 * b31 + b21 * b30) (by linear_combination hP23_01) hT01 hK1 ha0 ha1)
                  (perm_extract a0 a2 v0 v2 (b20 * b32 + b22 * b30) (by linear_combination hP23_02) hT02 hK2 ha0 ha2)
                  (perm_extract a0 a3 v0 v3 (b20 * b33 + b23 * b30) (by linear_combination hP23_03) hT03 hK3 ha0 ha3)
              · have hT13 : ¬ (v1 * star v3 - a1 * star a3 = 0) := fun hh =>
                  hT03 (T_trans a0 a1 a3 v0 v1 v3 hT01 hh hK1 ha1)
                have hT23 : ¬ (v2 * star v3 - a2 * star a3 = 0) := fun hh =>
                  hT03 (T_trans a0 a2 a3 v0 v2 v3 hT02 hh hK2 ha2)
                exact ha3 (branch_lone v3 v0 v1 v2 a3
                  (b13 * star b13 + b23 * star b23 + b33 * star b33) (b10 * star b13 + b20 * star b23 + b30 * star b33) (b11 * star b13 + b21 * star b23 + b31 * star b33) (b12 * star b13 + b22 * star b23 + b32 * star b33)
                  (Complex.normSq a3) (Complex.normSq a0) (Complex.normSq a1) (Complex.normSq a2)
                  (by linear_combination G3) hD3
                  (term_of_diff a0 v0 v3 (b10 * star b13 + b20 * star b23 + b30 * star b33) hK0 (hM03 hT03))
                  (term_of_diff a1 v1 v3 (b11 * star b13 + b21 * star b23 + b31 * star b33) hK1 (hM13 hT13))
                  (term_of_diff a2 v2 v3 (b12 * star b13 + b22 * star b23 + b32 * star b33) hK2 (hM23 hT23))
                  (by linarith) hK3)
            · by_cases hT03 : v0 * star v3 - a0 * star a3 = 0
              · have hT12 : ¬ (v1 * star v2 - a1 * star a2 = 0) := fun hh =>
                  hT02 (T_trans a0 a1 a2 v0 v1 v2 hT01 hh hK1 ha1)
                have hT23 : ¬ (v2 * star v3 - a2 * star a3 = 0) := fun hh =>
                  hT02 (T_trans a0 a3 a2 v0 v3 v2 hT03 (T_symm a2 a3 v2 v3 hh) hK3 ha3)
                exact ha2 (branch_lone v2 v0 v1 v3 a2
                  (b12 * star b12 + b22 * star b22 + b32 * star b32) (b10 * star b12 + b20 * star b22 + b30 * star b32) (b11 * star b12 + b21 * star b22 + b31 * star b32) (b13 * star b12 + b23 * star b22 + b33 * star b32)
                  (Complex.normSq a2) (Complex.normSq a0) (Complex.normSq a1) (Complex.normSq a3)
                  (by linear_combination G2) hD2
                  (term_of_diff a0 v0 v2 (b10 * star b12 + b20 * star b22 + b30 * star b32) hK0 (hM02 hT02))
                  (term_of_diff a1 v1 v2 (b11 * star b12 + b21 * star b22 + b31 * star b32) hK1 (hM12 hT12))
                  (term_of_diff a3 v3 v2 (b13 * star b12 + b23 * star b22 + b33 * star b32) hK3 (hM32 (fun hh => hT23 (T_symm a3 a2 v3 v2 hh))))
                  (by linarith) hK2)
              · have hT12 : ¬ (v1 * star v2 - a1 * star a2 = 0) := fun hh =>
                  hT02 (T_trans a0 a1 a2 v0 v1 v2 hT01 hh hK1 ha1)
                have hT13 : ¬ (v1 * star v3 - a1 * star a3 = 0) := fun hh =>
                  hT03 (T_trans a0 a1 a3 v0 v1 v3 hT01 hh hK1 ha1)
                exact branch_pair a0 a1 v0 v1 v2 v3 b10 b20 b30 b11 b21 b31
                  (b10 * star b10 + b20 * star b20 + b30 * star b30) (b11 * star b11 + b21 * star b21 + b31 * star b31) (b10 * star b11 + b20 * star b21 + b30 * star b31) (b11 * star b10 + b21 * star b20 + b31 * star b30)
                  (b12 * star b10 + b22 * star b20 + b32 * star b30) (b13 * star b10 + b23 * star b20 + b33 * star b30) (b12 * star b11 + b22 * star b21 + b32 * star b31) (b13 * star b11 + b23 * star b21 + b33 * star b31)
                  (Complex.normSq a2) (Complex.normSq a3)
                  (by linear_combination G0) (by linear_combination G1)
                  (term_of_diff a2 v2 v0 (b12 * star b10 + b22 * star b20 + b32 * star b30) hK2 (hM20 (fun hh => hT02 (T_symm a2 a0 v2 v0 hh))))
                  (term_of_diff a3 v3 v0 (b13 * star b10 + b23 * star b20 + b33 * star b30) hK3 (hM30 (fun hh => hT03 (T_symm a3 a0 v3 v0 hh))))
                  (term_of_diff a2 v2 v1 (b12 * star b11 + b22 * star b21 + b32 * star b31) hK2 (hM21 (fun hh => hT12 (T_symm a2 a1 v2 v1 hh))))
                  (term_of_diff a3 v3 v1 (b13 * star b11 + b23 * star b21 + b33 * star b31) hK3 (hM31 (fun hh => hT13 (T_symm a3 a1 v3 v1 hh))))
                  hD0 hD1 rfl rfl
                  (by linarith) n2 n3 hCol0 hCol1
                  (by linarith) (by linarith) (by linarith)
                  (perm_extract a0 a1 v0 v1 (b10 * b21 + b11 * b20) (by linear_combination hP12_01) hT01 hK1 ha0 ha1)
                  (perm_extract a0 a1 v0 v1 (b10 * b31 + b11 * b30) (by linear_combination hP13_01) hT01 hK1 ha0 ha1)
                  (perm_extract a0 a1 v0 v1 (b20 * b31 + b21 * b30) (by linear_combination hP23_01) hT01 hK1 ha0 ha1)
                  hK0 hK1 ha0 ha1
          · by_cases hT02 : v0 * star v2 - a0 * star a2 = 0
            · by_cases hT03 : v0 * star v3 - a0 * star a3 = 0
              · have hT12 : ¬ (v1 * star v2 - a1 * star a2 = 0) := fun hh =>
                  hT01 (T_trans a0 a2 a1 v0 v2 v1 hT02 (T_symm a1 a2 v1 v2 hh) hK2 ha2)
                have hT13 : ¬ (v1 * star v3 - a1 * star a3 = 0) := fun hh =>
                  hT01 (T_trans a0 a3 a1 v0 v3 v1 hT03 (T_symm a1 a3 v1 v3 hh) hK3 ha3)
                exact ha1 (branch_lone v1 v0 v2 v3 a1
                  (b11 * star b11 + b21 * star b21 + b31 * star b31) (b10 * star b11 + b20 * star b21 + b30 * star b31) (b12 * star b11 + b22 * star b21 + b32 * star b31) (b13 * star b11 + b23 * star b21 + b33 * star b31)
                  (Complex.normSq a1) (Complex.normSq a0) (Complex.normSq a2) (Complex.normSq a3)
                  (by linear_combination G1) hD1
                  (term_of_diff a0 v0 v1 (b10 * star b11 + b20 * star b21 + b30 * star b31) hK0 (hM01 hT01))
                  (term_of_diff a2 v2 v1 (b12 * star b11 + b22 * star b21 + b32 * star b31) hK2 (hM21 (fun hh => hT12 (T_symm a2 a1 v2 v1 hh))))
                  (term_of_diff a3 v3 v1 (b13 * star b11 + b23 * star b21 + b33 * star b31) hK3 (hM31 (fun hh => hT13 (T_symm a3 a1 v3 v1 hh))))
                  (by linarith) hK1)
              · have hT12 : ¬ (v1 * star v2 - a1 * star a2 = 0) := fun hh =>
                  hT01 (T_symm a1 a0 v1 v0 (T_trans a1 a2 a0 v1 v2 v0 hh (T_symm a0 a2 v0 v2 hT02) hK2 ha2))
                have hT23 : ¬ (v2 * star v3 - a2 * star a3 = 0) := fun hh =>
                  hT03 (T_trans a0 a2 a3 v0 v2 v3 hT02 hh hK2 ha2)
                exact branch_pair a0 a2 v0 v2 v1 v3 b10 b20 b30 b12 b22 b32
                  (b10 * star b10 + b20 * star b20 + b30 * star b30) (b12 * star b12 + b22 * star b22 + b32 * star b32) (b10 * star b12 + b20 * star b22 + b30 * star b32) (b12 * star b10 + b22 * star b20 + b32 * star b30)
                  (b11 * star b10 + b21 * star b20 + b31 * star b30) (b13 * star b10 + b23 * star b20 + b33 * star b30) (b11 * star b12 + b21 * star b22 + b31 * star b32) (b13 * star b12 + b23 * star b22 + b33 * star b32)
                  (Complex.normSq a1) (Complex.normSq a3)
                  (by linear_combination G0) (by linear_combination G2)
                  (term_of_diff a1 v1 v0 (b11 * star b10 + b21 * star b20 + b31 * star b30) hK1 (hM10 (fun hh => hT01 (T_symm a1 a0 v1 v0 hh))))
                  (term_of_diff a3 v3 v0 (b13 * star b10 + b23 * star b20 + b33 * star b30) hK3 (hM30 (fun hh => hT03 (T_symm a3 a0 v3 v0 hh))))
                  (term_of_diff a1 v1 v2 (b11 * star b12 + b21 * star b22 + b31 * star b32) hK1 (hM12 hT12))
                  (term_of_diff a3 v3 v2 (b13 * star b12 + b23 * star b22 + b33 * star b32) hK3 (hM32 (fun hh => hT23 (T_symm a3 a2 v3 v2 hh))))
                  hD0 hD2 rfl rfl
                  (by linarith) n1 n3 hCol0 hCol2
                  (by linarith) (by linarith) (by linarith)
                  (perm_extract a0 a2 v0 v2 (b10 * b22 + b12 * b20) (by linear_combination hP12_02) hT02 hK2 ha0 ha2)
                  (perm_extract a0 a2 v0 v2 (b10 * b32 + b12 * b30) (by linear_combination hP13_02) hT02 hK2 ha0 ha2)
                  (perm_extract a0 a2 v0 v2 (b20 * b32 + b22 * b30) (by linear_combination hP23_02) hT02 hK2 ha0 ha2)
                  hK0 hK2 ha0 ha2
            · by_cases hT03 : v0 * star v3 - a0 * star a3 = 0
              · have hT13 : ¬ (v1 * star v3 - a1 * star a3 = 0) := fun hh =>
                  hT01 (T_symm a1 a0 v1 v0 (T_trans a1 a3 a0 v1 v3 v0 hh (T_symm a0 a3 v0 v3 hT03) hK3 ha3))
                have hT23 : ¬ (v2 * star v3 - a2 * star a3 = 0) := fun hh =>
                  hT02 (T_symm a2 a0 v2 v0 (T_trans a2 a3 a0 v2 v3 v0 hh (T_symm a0 a3 v0 v3 hT03) hK3 ha3))
                exact branch_pair a0 a3 v0 v3 v1 v2 b10 b20 b30 b13 b23 b33
                  (b10 * star b10 + b20 * star b20 + b30 * star b30) (b13 * star b13 + b23 * star b23 + b33 * star b33) (b10 * star b13 + b20 * star b23 + b30 * star b33) (b13 * star b10 + b23 * star b20 + b33 * star b30)
                  (b11 * star b10 + b21 * star b20 + b31 * star b30) (b12 * star b10 + b22 * star b20 + b32 * star b30) (b11 * star b13 + b21 * star b23 + b31 * star b33) (b12 * star b13 + b22 * star b23 + b32 * star b33)
                  (Complex.normSq a1) (Complex.normSq a2)
                  (by linear_combination G0) (by linear_combination G3)
                  (term_of_diff a1 v1 v0 (b11 * star b10 + b21 * star b20 + b31 * star b30) hK1 (hM10 (fun hh => hT01 (T_symm a1 a0 v1 v0 hh))))
                  (term_of_diff a2 v2 v0 (b12 * star b10 + b22 * star b20 + b32 * star b30) hK2 (hM20 (fun hh => hT02 (T_symm a2 a0 v2 v0 hh))))
                  (term_of_diff a1 v1 v3 (b11 * star b13 + b21 * star b23 + b31 * star b33) hK1 (hM13 hT13))
                  (term_of_diff a2 v2 v3 (b12 * star b13 + b22 * star b23 + b32 * star b33) hK2 (hM23 hT23))
                  hD0 hD3 rfl rfl
                  (by linarith) n1 n2 hCol0 hCol3
                  (by linarith) (by linarith) (by linarith)
                  (perm_extract a0 a3 v0 v3 (b10 * b23 + b13 * b20) (by linear_combination hP12_03) hT03 hK3 ha0 ha3)
                  (perm_extract a0 a3 v0 v3 (b10 * b33 + b13 * b30) (by linear_combination hP13_03) hT03 hK3 ha0 ha3)
                  (perm_extract a0 a3 v0 v3 (b20 * b33 + b23 * b30) (by linear_combination hP23_03) hT03 hK3 ha0 ha3)
                  hK0 hK3 ha0 ha3
              · -- column 0 is alone
                exact ha0 (branch_lone v0 v1 v2 v3 a0
                  (b10 * star b10 + b20 * star b20 + b30 * star b30) (b11 * star b10 + b21 * star b20 + b31 * star b30) (b12 * star b10 + b22 * star b20 + b32 * star b30) (b13 * star b10 + b23 * star b20 + b33 * star b30)
                  (Complex.normSq a0) (Complex.normSq a1) (Complex.normSq a2) (Complex.normSq a3)
                  (by linear_combination G0) hD0
                  (term_of_diff a1 v1 v0 (b11 * star b10 + b21 * star b20 + b31 * star b30) hK1 (hM10 (fun hh => hT01 (T_symm a1 a0 v1 v0 hh))))
                  (term_of_diff a2 v2 v0 (b12 * star b10 + b22 * star b20 + b32 * star b30) hK2 (hM20 (fun hh => hT02 (T_symm a2 a0 v2 v0 hh))))
                  (term_of_diff a3 v3 v0 (b13 * star b10 + b23 * star b20 + b33 * star b30) hK3 (hM30 (fun hh => hT03 (T_symm a3 a0 v3 v0 hh))))
                  (by linarith) hK0)


/-! ## The no-go -/

set_option maxHeartbeats 4000000 in
/-- **Orbit 31 admits no six-qubit `((6,2,3))` code.**  The moment system,
the thirty-three off-diagonal Knill-Laflamme conditions listed here and the
twelve Klein-mask diagonal conditions are jointly inconsistent. -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11)) (Complex.normSq (c y12)) (Complex.normSq (c y13)) (Complex.normSq (c y14)) (Complex.normSq (c y15))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)) (Complex.normSq (d z12)) (Complex.normSq (d z13)) (Complex.normSq (d z14)) (Complex.normSq (d z15)))
    (E0_w0 : offSum c d ef0 w0 = 0)
    (E0_w1 : offSum c d ef0 w1 = 0)
    (E0_w3 : offSum c d ef0 w3 = 0)
    (E0_w4 : offSum c d ef0 w4 = 0)
    (E0_w5 : offSum c d ef0 w5 = 0)
    (E1_w0 : offSum c d ef1 w0 = 0)
    (E1_w2 : offSum c d ef1 w2 = 0)
    (E1_w3 : offSum c d ef1 w3 = 0)
    (E1_w4 : offSum c d ef1 w4 = 0)
    (E1_w5 : offSum c d ef1 w5 = 0)
    (E2_w0 : offSum c d ef2 w0 = 0)
    (E2_w2 : offSum c d ef2 w2 = 0)
    (E2_w3 : offSum c d ef2 w3 = 0)
    (E2_w4 : offSum c d ef2 w4 = 0)
    (E2_w5 : offSum c d ef2 w5 = 0)
    (E3_w0 : offSum c d ef3 w0 = 0)
    (E3_w5 : offSum c d ef3 w5 = 0)
    (E4_w0 : offSum c d ef4 w0 = 0)
    (E4_w5 : offSum c d ef4 w5 = 0)
    (E5_w0 : offSum c d ef5 w0 = 0)
    (E5_w5 : offSum c d ef5 w5 = 0)
    (E6_w0 : offSum c d ef6 w0 = 0)
    (E6_w4 : offSum c d ef6 w4 = 0)
    (E7_w0 : offSum c d ef7 w0 = 0)
    (E7_w4 : offSum c d ef7 w4 = 0)
    (E8_w0 : offSum c d ef8 w0 = 0)
    (E8_w4 : offSum c d ef8 w4 = 0)
    (E9_w0 : offSum c d ef9 w0 = 0)
    (E9_w3 : offSum c d ef9 w3 = 0)
    (E10_w0 : offSum c d ef10 w0 = 0)
    (E10_w3 : offSum c d ef10 w3 = 0)
    (E11_w0 : offSum c d ef11 w0 = 0)
    (E11_w3 : offSum c d ef11 w3 = 0)
    (D12_w0 : diagBot c ef12 w0 = diagTop d ef12 w0)
    (D12_w4 : diagBot c ef12 w4 = diagTop d ef12 w4)
    (D12_w3 : diagBot c ef12 w3 = diagTop d ef12 w3)
    (D12_w6 : diagBot c ef12 w6 = diagTop d ef12 w6)
    (D13_w0 : diagBot c ef13 w0 = diagTop d ef13 w0)
    (D13_w5 : diagBot c ef13 w5 = diagTop d ef13 w5)
    (D13_w3 : diagBot c ef13 w3 = diagTop d ef13 w3)
    (D13_w7 : diagBot c ef13 w7 = diagTop d ef13 w7)
    (D14_w0 : diagBot c ef14 w0 = diagTop d ef14 w0)
    (D14_w5 : diagBot c ef14 w5 = diagTop d ef14 w5)
    (D14_w4 : diagBot c ef14 w4 = diagTop d ef14 w4)
    (D14_w8 : diagBot c ef14 w8 = diagTop d ef14 w8)
    : False := by
  have hK0 : star (d z15) * star (star (d z15)) = c y0 * star (c y0) :=
    Table31.kernel_norm (c y0) (star (d z15)) (Complex.normSq (c y0))
      (by simpa using (by linarith [eq0 hm] :
        Complex.normSq (d z15) = Complex.normSq (c y0))) rfl
  have hK1 : star (d z14) * star (star (d z14)) = c y1 * star (c y1) :=
    Table31.kernel_norm (c y1) (star (d z14)) (Complex.normSq (c y1))
      (by simpa using (by linarith [eq1 hm] :
        Complex.normSq (d z14) = Complex.normSq (c y1))) rfl
  have hK2 : star (d z13) * star (star (d z13)) = c y2 * star (c y2) :=
    Table31.kernel_norm (c y2) (star (d z13)) (Complex.normSq (c y2))
      (by simpa using (by linarith [eq2 hm] :
        Complex.normSq (d z13) = Complex.normSq (c y2))) rfl
  have hK3 : star (d z12) * star (star (d z12)) = c y3 * star (c y3) :=
    Table31.kernel_norm (c y3) (star (d z12)) (Complex.normSq (c y3))
      (by simpa using (by linarith [eq3 hm] :
        Complex.normSq (d z12) = Complex.normSq (c y3))) rfl
  have C10 := hcol_1_0 c d E0_w1 E0_w5 E0_w4 E0_w3
  have C11 := hcol_1_1 c d E0_w1 E0_w5 E0_w4 E0_w3
  have C12 := hcol_1_2 c d E0_w1 E0_w5 E0_w4 E0_w3
  have C13 := hcol_1_3 c d E0_w1 E0_w5 E0_w4 E0_w3
  have C20 := hcol_2_0 c d E1_w2 E1_w5 E1_w4 E1_w3
  have C21 := hcol_2_1 c d E1_w2 E1_w5 E1_w4 E1_w3
  have C22 := hcol_2_2 c d E1_w2 E1_w5 E1_w4 E1_w3
  have C23 := hcol_2_3 c d E1_w2 E1_w5 E1_w4 E1_w3
  have C30 := hcol_3_0 c d E2_w2 E2_w5 E2_w4 E2_w3
  have C31 := hcol_3_1 c d E2_w2 E2_w5 E2_w4 E2_w3
  have C32 := hcol_3_2 c d E2_w2 E2_w5 E2_w4 E2_w3
  have C33 := hcol_3_3 c d E2_w2 E2_w5 E2_w4 E2_w3
  have F1 : c y7 * star (d z15) + c y6 * star (d z14) + c y5 * star (d z13) + c y4 * star (d z12) = 0 := by
    have h := Table31.conj4 (c y4) (c y5) (c y6) (c y7) (d z12) (d z13) (d z14) (d z15)
        (fam1_1 c d E0_w0 E0_w1)
    linear_combination h
  have F2 : c y11 * star (d z15) + c y10 * star (d z14) + c y9 * star (d z13) + c y8 * star (d z12) = 0 := by
    have h := Table31.conj4 (c y8) (c y9) (c y10) (c y11) (d z12) (d z13) (d z14) (d z15)
        (fam1_2 c d E1_w0 E1_w2)
    linear_combination h
  have F3 : c y15 * star (d z15) + c y14 * star (d z14) + c y13 * star (d z13) + c y12 * star (d z12) = 0 := by
    have h := Table31.conj4 (c y12) (c y13) (c y14) (c y15) (d z12) (d z13) (d z14) (d z15)
        (fam1_3 c d E2_w0 E2_w2)
    linear_combination h
  have R01 := fam3_0_1 c d D12_w0 D12_w4 D12_w3 D12_w6
  have R02 := fam3_0_2 c d D13_w0 D13_w5 D13_w3 D13_w7
  have R03 := fam3_0_3 c d D14_w0 D14_w5 D14_w4 D14_w8
  have R10 := fam3_1_0 c d D12_w0 D12_w4 D12_w3 D12_w6
  have R12 := fam3_1_2 c d D14_w0 D14_w5 D14_w4 D14_w8
  have R13 := fam3_1_3 c d D13_w0 D13_w5 D13_w3 D13_w7
  have R20 := fam3_2_0 c d D13_w0 D13_w5 D13_w3 D13_w7
  have R21 := fam3_2_1 c d D14_w0 D14_w5 D14_w4 D14_w8
  have R23 := fam3_2_3 c d D12_w0 D12_w4 D12_w3 D12_w6
  have R30 := fam3_3_0 c d D14_w0 D14_w5 D14_w4 D14_w8
  have R31 := fam3_3_1 c d D13_w0 D13_w5 D13_w3 D13_w7
  have R32 := fam3_3_2 c d D12_w0 D12_w4 D12_w3 D12_w6
  have Q4 := congrArg star (fam2_4 c d E5_w0 E5_w5)
  simp only [star_add, star_mul', star_star, star_zero] at Q4
  have Q10 := congrArg star (fam2_10 c d E8_w0 E8_w4)
  simp only [star_add, star_mul', star_star, star_zero] at Q10
  have Q16 := congrArg star (fam2_16 c d E11_w0 E11_w3)
  simp only [star_add, star_mul', star_star, star_zero] at Q16
  have Q17 := congrArg star (fam2_17 c d E11_w0 E11_w3)
  simp only [star_add, star_mul', star_star, star_zero] at Q17
  have Q11 := congrArg star (fam2_11 c d E8_w0 E8_w4)
  simp only [star_add, star_mul', star_star, star_zero] at Q11
  have Q5 := congrArg star (fam2_5 c d E5_w0 E5_w5)
  simp only [star_add, star_mul', star_star, star_zero] at Q5
  have Q2 := congrArg star (fam2_2 c d E4_w0 E4_w5)
  simp only [star_add, star_mul', star_star, star_zero] at Q2
  have Q8 := congrArg star (fam2_8 c d E7_w0 E7_w4)
  simp only [star_add, star_mul', star_star, star_zero] at Q8
  have Q14 := congrArg star (fam2_14 c d E10_w0 E10_w3)
  simp only [star_add, star_mul', star_star, star_zero] at Q14
  have Q15 := congrArg star (fam2_15 c d E10_w0 E10_w3)
  simp only [star_add, star_mul', star_star, star_zero] at Q15
  have Q9 := congrArg star (fam2_9 c d E7_w0 E7_w4)
  simp only [star_add, star_mul', star_star, star_zero] at Q9
  have Q3 := congrArg star (fam2_3 c d E4_w0 E4_w5)
  simp only [star_add, star_mul', star_star, star_zero] at Q3
  have Q0 := congrArg star (fam2_0 c d E3_w0 E3_w5)
  simp only [star_add, star_mul', star_star, star_zero] at Q0
  have Q6 := congrArg star (fam2_6 c d E6_w0 E6_w4)
  simp only [star_add, star_mul', star_star, star_zero] at Q6
  have Q12 := congrArg star (fam2_12 c d E9_w0 E9_w3)
  simp only [star_add, star_mul', star_star, star_zero] at Q12
  have Q13 := congrArg star (fam2_13 c d E9_w0 E9_w3)
  simp only [star_add, star_mul', star_star, star_zero] at Q13
  have Q7 := congrArg star (fam2_7 c d E6_w0 E6_w4)
  simp only [star_add, star_mul', star_star, star_zero] at Q7
  have Q1 := congrArg star (fam2_1 c d E3_w0 E3_w5)
  simp only [star_add, star_mul', star_star, star_zero] at Q1
  exact master
    (c y0) (c y1) (c y2) (c y3) (star (d z15)) (star (d z14)) (star (d z13)) (star (d z12))
    (c y7) (c y6) (c y5) (c y4) (c y11) (c y10) (c y9) (c y8) (c y15) (c y14) (c y13) (c y12)
    hK0 hK1 hK2 hK3 F1 F2 F3
    (by linarith [hm.n0, row1 hm, row2 hm, row3 hm])
    (by linarith [row1 hm]) (by linarith [row2 hm]) (by linarith [row3 hm])
    (by linarith [col0 hm]) (by linarith [col1 hm]) (by linarith [col2 hm]) (by linarith [col3 hm])
    (fun hT => Table31.M_eq_of_raw (c y0) (c y1) (star (d z15)) (star (d z14))
        (c y7) (c y11) (c y15) (c y6) (c y10) (c y14)
        (star (d z8)) (star (d z4)) (star (d z0)) (star (d z9)) (star (d z5)) (star (d z1))
        (by simp only [star_star]; linear_combination R01)
        C10 C20 C30 C11 C21 C31 hK0 hK1 hT)
    (fun hT => Table31.M_eq_of_raw (c y0) (c y2) (star (d z15)) (star (d z13))
        (c y7) (c y11) (c y15) (c y5) (c y9) (c y13)
        (star (d z8)) (star (d z4)) (star (d z0)) (star (d z10)) (star (d z6)) (star (d z2))
        (by simp only [star_star]; linear_combination R02)
        C10 C20 C30 C12 C22 C32 hK0 hK2 hT)
    (fun hT => Table31.M_eq_of_raw (c y0) (c y3) (star (d z15)) (star (d z12))
        (c y7) (c y11) (c y15) (c y4) (c y8) (c y12)
        (star (d z8)) (star (d z4)) (star (d z0)) (star (d z11)) (star (d z7)) (star (d z3))
        (by simp only [star_star]; linear_combination R03)
        C10 C20 C30 C13 C23 C33 hK0 hK3 hT)
    (fun hT => Table31.M_eq_of_raw (c y1) (c y0) (star (d z14)) (star (d z15))
        (c y6) (c y10) (c y14) (c y7) (c y11) (c y15)
        (star (d z9)) (star (d z5)) (star (d z1)) (star (d z8)) (star (d z4)) (star (d z0))
        (by simp only [star_star]; linear_combination R10)
        C11 C21 C31 C10 C20 C30 hK1 hK0 hT)
    (fun hT => Table31.M_eq_of_raw (c y1) (c y2) (star (d z14)) (star (d z13))
        (c y6) (c y10) (c y14) (c y5) (c y9) (c y13)
        (star (d z9)) (star (d z5)) (star (d z1)) (star (d z10)) (star (d z6)) (star (d z2))
        (by simp only [star_star]; linear_combination R12)
        C11 C21 C31 C12 C22 C32 hK1 hK2 hT)
    (fun hT => Table31.M_eq_of_raw (c y1) (c y3) (star (d z14)) (star (d z12))
        (c y6) (c y10) (c y14) (c y4) (c y8) (c y12)
        (star (d z9)) (star (d z5)) (star (d z1)) (star (d z11)) (star (d z7)) (star (d z3))
        (by simp only [star_star]; linear_combination R13)
        C11 C21 C31 C13 C23 C33 hK1 hK3 hT)
    (fun hT => Table31.M_eq_of_raw (c y2) (c y0) (star (d z13)) (star (d z15))
        (c y5) (c y9) (c y13) (c y7) (c y11) (c y15)
        (star (d z10)) (star (d z6)) (star (d z2)) (star (d z8)) (star (d z4)) (star (d z0))
        (by simp only [star_star]; linear_combination R20)
        C12 C22 C32 C10 C20 C30 hK2 hK0 hT)
    (fun hT => Table31.M_eq_of_raw (c y2) (c y1) (star (d z13)) (star (d z14))
        (c y5) (c y9) (c y13) (c y6) (c y10) (c y14)
        (star (d z10)) (star (d z6)) (star (d z2)) (star (d z9)) (star (d z5)) (star (d z1))
        (by simp only [star_star]; linear_combination R21)
        C12 C22 C32 C11 C21 C31 hK2 hK1 hT)
    (fun hT => Table31.M_eq_of_raw (c y2) (c y3) (star (d z13)) (star (d z12))
        (c y5) (c y9) (c y13) (c y4) (c y8) (c y12)
        (star (d z10)) (star (d z6)) (star (d z2)) (star (d z11)) (star (d z7)) (star (d z3))
        (by simp only [star_star]; linear_combination R23)
        C12 C22 C32 C13 C23 C33 hK2 hK3 hT)
    (fun hT => Table31.M_eq_of_raw (c y3) (c y0) (star (d z12)) (star (d z15))
        (c y4) (c y8) (c y12) (c y7) (c y11) (c y15)
        (star (d z11)) (star (d z7)) (star (d z3)) (star (d z8)) (star (d z4)) (star (d z0))
        (by simp only [star_star]; linear_combination R30)
        C13 C23 C33 C10 C20 C30 hK3 hK0 hT)
    (fun hT => Table31.M_eq_of_raw (c y3) (c y1) (star (d z12)) (star (d z14))
        (c y4) (c y8) (c y12) (c y6) (c y10) (c y14)
        (star (d z11)) (star (d z7)) (star (d z3)) (star (d z9)) (star (d z5)) (star (d z1))
        (by simp only [star_star]; linear_combination R31)
        C13 C23 C33 C11 C21 C31 hK3 hK1 hT)
    (fun hT => Table31.M_eq_of_raw (c y3) (c y2) (star (d z12)) (star (d z13))
        (c y4) (c y8) (c y12) (c y5) (c y9) (c y13)
        (star (d z11)) (star (d z7)) (star (d z3)) (star (d z10)) (star (d z6)) (star (d z2))
        (by simp only [star_star]; linear_combination R32)
        C13 C23 C33 C12 C22 C32 hK3 hK2 hT)
    (perm_of_raw (c y0) (c y1) (star (d z15)) (star (d z14))
        (c y7) (c y6) (c y11) (c y10)
        (star (d z8)) (star (d z9)) (star (d z4)) (star (d z5))
        (by linear_combination Q4) C10 C11 C20 C21)
    (perm_of_raw (c y0) (c y2) (star (d z15)) (star (d z13))
        (c y7) (c y5) (c y11) (c y9)
        (star (d z8)) (star (d z10)) (star (d z4)) (star (d z6))
        (by linear_combination Q10) C10 C12 C20 C22)
    (perm_of_raw (c y0) (c y3) (star (d z15)) (star (d z12))
        (c y7) (c y4) (c y11) (c y8)
        (star (d z8)) (star (d z11)) (star (d z4)) (star (d z7))
        (by linear_combination Q16) C10 C13 C20 C23)
    (perm_of_raw (c y1) (c y2) (star (d z14)) (star (d z13))
        (c y6) (c y5) (c y10) (c y9)
        (star (d z9)) (star (d z10)) (star (d z5)) (star (d z6))
        (by linear_combination Q17) C11 C12 C21 C22)
    (perm_of_raw (c y1) (c y3) (star (d z14)) (star (d z12))
        (c y6) (c y4) (c y10) (c y8)
        (star (d z9)) (star (d z11)) (star (d z5)) (star (d z7))
        (by linear_combination Q11) C11 C13 C21 C23)
    (perm_of_raw (c y2) (c y3) (star (d z13)) (star (d z12))
        (c y5) (c y4) (c y9) (c y8)
        (star (d z10)) (star (d z11)) (star (d z6)) (star (d z7))
        (by linear_combination Q5) C12 C13 C22 C23)
    (perm_of_raw (c y0) (c y1) (star (d z15)) (star (d z14))
        (c y7) (c y6) (c y15) (c y14)
        (star (d z8)) (star (d z9)) (star (d z0)) (star (d z1))
        (by linear_combination Q2) C10 C11 C30 C31)
    (perm_of_raw (c y0) (c y2) (star (d z15)) (star (d z13))
        (c y7) (c y5) (c y15) (c y13)
        (star (d z8)) (star (d z10)) (star (d z0)) (star (d z2))
        (by linear_combination Q8) C10 C12 C30 C32)
    (perm_of_raw (c y0) (c y3) (star (d z15)) (star (d z12))
        (c y7) (c y4) (c y15) (c y12)
        (star (d z8)) (star (d z11)) (star (d z0)) (star (d z3))
        (by linear_combination Q14) C10 C13 C30 C33)
    (perm_of_raw (c y1) (c y2) (star (d z14)) (star (d z13))
        (c y6) (c y5) (c y14) (c y13)
        (star (d z9)) (star (d z10)) (star (d z1)) (star (d z2))
        (by linear_combination Q15) C11 C12 C31 C32)
    (perm_of_raw (c y1) (c y3) (star (d z14)) (star (d z12))
        (c y6) (c y4) (c y14) (c y12)
        (star (d z9)) (star (d z11)) (star (d z1)) (star (d z3))
        (by linear_combination Q9) C11 C13 C31 C33)
    (perm_of_raw (c y2) (c y3) (star (d z13)) (star (d z12))
        (c y5) (c y4) (c y13) (c y12)
        (star (d z10)) (star (d z11)) (star (d z2)) (star (d z3))
        (by linear_combination Q3) C12 C13 C32 C33)
    (perm_of_raw (c y0) (c y1) (star (d z15)) (star (d z14))
        (c y11) (c y10) (c y15) (c y14)
        (star (d z4)) (star (d z5)) (star (d z0)) (star (d z1))
        (by linear_combination Q0) C20 C21 C30 C31)
    (perm_of_raw (c y0) (c y2) (star (d z15)) (star (d z13))
        (c y11) (c y9) (c y15) (c y13)
        (star (d z4)) (star (d z6)) (star (d z0)) (star (d z2))
        (by linear_combination Q6) C20 C22 C30 C32)
    (perm_of_raw (c y0) (c y3) (star (d z15)) (star (d z12))
        (c y11) (c y8) (c y15) (c y12)
        (star (d z4)) (star (d z7)) (star (d z0)) (star (d z3))
        (by linear_combination Q12) C20 C23 C30 C33)
    (perm_of_raw (c y1) (c y2) (star (d z14)) (star (d z13))
        (c y10) (c y9) (c y14) (c y13)
        (star (d z5)) (star (d z6)) (star (d z1)) (star (d z2))
        (by linear_combination Q13) C21 C22 C31 C32)
    (perm_of_raw (c y1) (c y3) (star (d z14)) (star (d z12))
        (c y10) (c y8) (c y14) (c y12)
        (star (d z5)) (star (d z7)) (star (d z1)) (star (d z3))
        (by linear_combination Q7) C21 C23 C31 C33)
    (perm_of_raw (c y2) (c y3) (star (d z13)) (star (d z12))
        (c y9) (c y8) (c y13) (c y12)
        (star (d z6)) (star (d z7)) (star (d z2)) (star (d z3))
        (by linear_combination Q1) C22 C23 C32 C33)
end

end SixQubit.Orbit31
