import Mathlib

import SS.FullKL
import SixQubit.Common
import SixQubit.Block26

/-!
# Six-qubit no-go for moment orbit 26: the transcription layer

Orbit 26 of `six_qubit_sslp.tex`: q = 4, angle vector a = (0, 1, 1, 2, 2, 3),
residues 0 and 1, fibers of size sixteen each.  The first angle is zero, so
both fibers are closed under `X_1`, and each splits into eight blocks of two
amplitudes.  Writing `C_i` for the bottom block and `D_i` for the top block
carried by the complementary tail, the Knill-Laflamme system supplies

* twelve **outer identities**, four matrix entries for each of the three
  pairs of non-anchor groups;
* twelve **anchor scalars** `ip C_i D_j + ip C_j D_i = 0`, one for each
  non-anchor block `i` and each anchor `j`;
* the **matrix moment identity** `C_g C_g^† + D_g D_g^† = ρ/2`, per group and
  per entry, from the diagonal conditions;

together with the linear **moment facts** `P_i = Q_i`, `P_6 = P_7 = 1/8`, the
group totals `P_{2g} + P_{2g+1} = 1/4` and the load-bearing pair
`P_0 + P_2 + P_4 = P_1 + P_3 + P_5 = 3/8`.

The algebra that consumes these lives in `SixQubit.Block26`.

Everything computational is decided by the Lean kernel; `native_decide` is
not used.
-/

namespace SixQubit.Orbit26

open scoped BigOperators

noncomputable section

def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]

/-! ## The two fibers -/

def y0  : SS.BitString 6 := bs false false false false false false -- 000000
def y1  : SS.BitString 6 := bs false false false true  true  false -- 000110
def y2  : SS.BitString 6 := bs false false true  false false true  -- 001001
def y3  : SS.BitString 6 := bs false false true  true  true  true  -- 001111
def y4  : SS.BitString 6 := bs false true  false false false true  -- 010001
def y5  : SS.BitString 6 := bs false true  false true  true  true  -- 010111
def y6  : SS.BitString 6 := bs false true  true  false true  false -- 011010
def y7  : SS.BitString 6 := bs false true  true  true  false false -- 011100
def y8  : SS.BitString 6 := bs true  false false false false false -- 100000
def y9  : SS.BitString 6 := bs true  false false true  true  false -- 100110
def y10 : SS.BitString 6 := bs true  false true  false false true  -- 101001
def y11 : SS.BitString 6 := bs true  false true  true  true  true  -- 101111
def y12 : SS.BitString 6 := bs true  true  false false false true  -- 110001
def y13 : SS.BitString 6 := bs true  true  false true  true  true  -- 110111
def y14 : SS.BitString 6 := bs true  true  true  false true  false -- 111010
def y15 : SS.BitString 6 := bs true  true  true  true  false false -- 111100

def z0  : SS.BitString 6 := bs false false false false true  true  -- 000011
def z1  : SS.BitString 6 := bs false false false true  false true  -- 000101
def z2  : SS.BitString 6 := bs false false true  false false false -- 001000
def z3  : SS.BitString 6 := bs false false true  true  true  false -- 001110
def z4  : SS.BitString 6 := bs false true  false false false false -- 010000
def z5  : SS.BitString 6 := bs false true  false true  true  false -- 010110
def z6  : SS.BitString 6 := bs false true  true  false false true  -- 011001
def z7  : SS.BitString 6 := bs false true  true  true  true  true  -- 011111
def z8  : SS.BitString 6 := bs true  false false false true  true  -- 100011
def z9  : SS.BitString 6 := bs true  false false true  false true  -- 100101
def z10 : SS.BitString 6 := bs true  false true  false false false -- 101000
def z11 : SS.BitString 6 := bs true  false true  true  true  false -- 101110
def z12 : SS.BitString 6 := bs true  true  false false false false -- 110000
def z13 : SS.BitString 6 := bs true  true  false true  true  false -- 110110
def z14 : SS.BitString 6 := bs true  true  true  false false true  -- 111001
def z15 : SS.BitString 6 := bs true  true  true  true  true  true  -- 111111

def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15}
def S1 : Finset (SS.BitString 6) := {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15}

def av : Fin 6 -> ZMod 4 := ![0, 1, 1, 2, 2, 3]

/-- Each support is exactly its residue fiber, decided over all 64 strings. -/
theorem S0_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 0) = S0 := by
  decide

theorem S1_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 1) = S1 := by
  decide

/-! ## The moment system -/

/-- The two normalizations and the moment equalities, with every probability
nonnegative. -/
structure MomentSystem (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real) : Prop where
  n0 : q0 + q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 + q9 + q10 + q11 + q12 + q13 + q14 + q15 = 1
  n1 : r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15 = 1
  m1 : q8 + q9 + q10 + q11 + q12 + q13 + q14 + q15 = r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15
  m2 : q4 + q5 + q6 + q7 + q12 + q13 + q14 + q15 = r4 + r5 + r6 + r7 + r12 + r13 + r14 + r15
  m3 : q2 + q3 + q6 + q7 + q10 + q11 + q14 + q15 = r2 + r3 + r6 + r7 + r10 + r11 + r14 + r15
  m4 : q1 + q3 + q5 + q7 + q9 + q11 + q13 + q15 = r1 + r3 + r5 + r7 + r9 + r11 + r13 + r15
  m5 : q1 + q3 + q5 + q6 + q9 + q11 + q13 + q14 = r0 + r3 + r5 + r7 + r8 + r11 + r13 + r15
  m6 : q2 + q3 + q4 + q5 + q10 + q11 + q12 + q13 = r0 + r1 + r6 + r7 + r8 + r9 + r14 + r15
  c12 : q12 + q13 + q14 + q15 = r12 + r13 + r14 + r15
  c13 : q10 + q11 + q14 + q15 = r10 + r11 + r14 + r15
  c14 : q9 + q11 + q13 + q15 = r9 + r11 + r13 + r15
  c15 : q9 + q11 + q13 + q14 = r8 + r11 + r13 + r15
  c16 : q10 + q11 + q12 + q13 = r8 + r9 + r14 + r15
  c23 : q6 + q7 + q14 + q15 = r6 + r7 + r14 + r15
  c24 : q5 + q7 + q13 + q15 = r5 + r7 + r13 + r15
  c25 : q5 + q6 + q13 + q14 = r5 + r7 + r13 + r15
  c26 : q4 + q5 + q12 + q13 = r6 + r7 + r14 + r15
  c34 : q3 + q7 + q11 + q15 = r3 + r7 + r11 + r15
  c35 : q3 + q6 + q11 + q14 = r3 + r7 + r11 + r15
  c36 : q2 + q3 + q10 + q11 = r6 + r7 + r14 + r15
  c45 : q1 + q3 + q5 + q9 + q11 + q13 = r3 + r5 + r7 + r11 + r13 + r15
  c46 : q3 + q5 + q11 + q13 = r1 + r7 + r9 + r15
  c56 : q3 + q5 + q11 + q13 = r0 + r7 + r8 + r15

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

/-- block 0 carries the same weight below and above. -/
theorem mPQ0 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    q0 + q8 - r7 - r15 = 0 := by
  obtain ⟨n0, n1, _m1, m2, m3, _m4, _m5, m6, _c12, _c13, _c14, _c15, _c16, _c23, _c24, c25, c26, c34, _c35, c36, c45, _c46, _c56, _nq0, _nq1, _nq2, _nq3, _nq4, _nq5, _nq6, _nq7, _nq8, _nq9, _nq10, _nq11, _nq12, _nq13, _nq14, _nq15, _nr0, _nr1, _nr2, _nr3, _nr4, _nr5, _nr6, _nr7, _nr8, _nr9, _nr10, _nr11, _nr12, _nr13, _nr14, _nr15⟩ := h
  linear_combination (1) * n0 + (-1) * n1 + (-1) * m2 + (-1) * m3 + (-1) * m6 + (1) * c25 + (1) * c26 + (1) * c34 + (1) * c36 + (-1) * c45

/-- block 1 carries the same weight below and above. -/
theorem mPQ1 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    q1 + q9 - r6 - r14 = 0 := by
  obtain ⟨_n0, _n1, _m1, _m2, _m3, _m4, _m5, _m6, _c12, _c13, _c14, _c15, _c16, c23, _c24, c25, _c26, c34, _c35, _c36, c45, _c46, _c56, _nq0, _nq1, _nq2, _nq3, _nq4, _nq5, _nq6, _nq7, _nq8, _nq9, _nq10, _nq11, _nq12, _nq13, _nq14, _nq15, _nr0, _nr1, _nr2, _nr3, _nr4, _nr5, _nr6, _nr7, _nr8, _nr9, _nr10, _nr11, _nr12, _nr13, _nr14, _nr15⟩ := h
  linear_combination (1) * c23 + (-1) * c25 + (-1) * c34 + (1) * c45

/-- block 2 carries the same weight below and above. -/
theorem mPQ2 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    q2 + q10 - r5 - r13 = 0 := by
  obtain ⟨_n0, _n1, _m1, _m2, _m3, _m4, _m5, m6, _c12, _c13, _c14, _c15, _c16, c23, _c24, c25, c26, c34, c35, c36, _c45, c46, c56, _nq0, _nq1, _nq2, _nq3, _nq4, _nq5, _nq6, _nq7, _nq8, _nq9, _nq10, _nq11, _nq12, _nq13, _nq14, _nq15, _nr0, _nr1, _nr2, _nr3, _nr4, _nr5, _nr6, _nr7, _nr8, _nr9, _nr10, _nr11, _nr12, _nr13, _nr14, _nr15⟩ := h
  linear_combination (1/2) * m6 + (-1/2) * c23 + (1) * c25 + (-1/2) * c26 + (1/2) * c34 + (-1/2) * c35 + (1/2) * c36 + (-1/2) * c46 + (-1/2) * c56

/-- block 3 carries the same weight below and above. -/
theorem mPQ3 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    q3 + q11 - r4 - r12 = 0 := by
  obtain ⟨_n0, _n1, _m1, m2, _m3, _m4, _m5, m6, _c12, _c13, _c14, _c15, _c16, c23, _c24, c25, c26, c34, c35, c36, _c45, c46, c56, _nq0, _nq1, _nq2, _nq3, _nq4, _nq5, _nq6, _nq7, _nq8, _nq9, _nq10, _nq11, _nq12, _nq13, _nq14, _nq15, _nr0, _nr1, _nr2, _nr3, _nr4, _nr5, _nr6, _nr7, _nr8, _nr9, _nr10, _nr11, _nr12, _nr13, _nr14, _nr15⟩ := h
  linear_combination (1) * m2 + (-1/2) * m6 + (-1/2) * c23 + (-1) * c25 + (-1/2) * c26 + (-1/2) * c34 + (1/2) * c35 + (1/2) * c36 + (1/2) * c46 + (1/2) * c56

/-- block 4 carries the same weight below and above. -/
theorem mPQ4 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    q4 + q12 - r3 - r11 = 0 := by
  obtain ⟨_n0, _n1, _m1, _m2, _m3, _m4, _m5, m6, _c12, _c13, _c14, _c15, _c16, c23, _c24, _c25, c26, c34, c35, c36, _c45, c46, c56, _nq0, _nq1, _nq2, _nq3, _nq4, _nq5, _nq6, _nq7, _nq8, _nq9, _nq10, _nq11, _nq12, _nq13, _nq14, _nq15, _nr0, _nr1, _nr2, _nr3, _nr4, _nr5, _nr6, _nr7, _nr8, _nr9, _nr10, _nr11, _nr12, _nr13, _nr14, _nr15⟩ := h
  linear_combination (1/2) * m6 + (-1/2) * c23 + (1/2) * c26 + (1/2) * c34 + (1/2) * c35 + (-1/2) * c36 + (-1/2) * c46 + (-1/2) * c56

/-- block 5 carries the same weight below and above. -/
theorem mPQ5 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    q5 + q13 - r2 - r10 = 0 := by
  obtain ⟨_n0, _n1, _m1, _m2, m3, _m4, _m5, m6, _c12, _c13, _c14, _c15, _c16, c23, _c24, _c25, c26, c34, c35, c36, _c45, c46, c56, _nq0, _nq1, _nq2, _nq3, _nq4, _nq5, _nq6, _nq7, _nq8, _nq9, _nq10, _nq11, _nq12, _nq13, _nq14, _nq15, _nr0, _nr1, _nr2, _nr3, _nr4, _nr5, _nr6, _nr7, _nr8, _nr9, _nr10, _nr11, _nr12, _nr13, _nr14, _nr15⟩ := h
  linear_combination (1) * m3 + (-1/2) * m6 + (-1/2) * c23 + (1/2) * c26 + (-1/2) * c34 + (-1/2) * c35 + (-1/2) * c36 + (1/2) * c46 + (1/2) * c56

/-- block 6 carries the same weight below and above. -/
theorem mPQ6 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    q6 + q14 - r1 - r9 = 0 := by
  obtain ⟨_n0, _n1, _m1, _m2, _m3, _m4, _m5, m6, _c12, _c13, _c14, _c15, _c16, c23, _c24, _c25, c26, c34, c35, c36, _c45, c46, c56, _nq0, _nq1, _nq2, _nq3, _nq4, _nq5, _nq6, _nq7, _nq8, _nq9, _nq10, _nq11, _nq12, _nq13, _nq14, _nq15, _nr0, _nr1, _nr2, _nr3, _nr4, _nr5, _nr6, _nr7, _nr8, _nr9, _nr10, _nr11, _nr12, _nr13, _nr14, _nr15⟩ := h
  linear_combination (1/2) * m6 + (1/2) * c23 + (-1/2) * c26 + (-1/2) * c34 + (1/2) * c35 + (-1/2) * c36 + (1/2) * c46 + (-1/2) * c56

/-- block 7 carries the same weight below and above. -/
theorem mPQ7 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    q7 + q15 - r0 - r8 = 0 := by
  obtain ⟨_n0, _n1, _m1, _m2, _m3, _m4, _m5, m6, _c12, _c13, _c14, _c15, _c16, c23, _c24, _c25, c26, c34, c35, c36, _c45, c46, c56, _nq0, _nq1, _nq2, _nq3, _nq4, _nq5, _nq6, _nq7, _nq8, _nq9, _nq10, _nq11, _nq12, _nq13, _nq14, _nq15, _nr0, _nr1, _nr2, _nr3, _nr4, _nr5, _nr6, _nr7, _nr8, _nr9, _nr10, _nr11, _nr12, _nr13, _nr14, _nr15⟩ := h
  linear_combination (1/2) * m6 + (1/2) * c23 + (-1/2) * c26 + (1/2) * c34 + (-1/2) * c35 + (-1/2) * c36 + (-1/2) * c46 + (1/2) * c56

/-- the first anchor block holds an eighth. -/
theorem mP6 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    q6 + q14 - 1/8 = 0 := by
  obtain ⟨_n0, n1, _m1, m2, m3, _m4, _m5, m6, _c12, _c13, _c14, _c15, _c16, c23, _c24, _c25, c26, c34, c35, c36, _c45, _c46, _c56, _nq0, _nq1, _nq2, _nq3, _nq4, _nq5, _nq6, _nq7, _nq8, _nq9, _nq10, _nq11, _nq12, _nq13, _nq14, _nq15, _nr0, _nr1, _nr2, _nr3, _nr4, _nr5, _nr6, _nr7, _nr8, _nr9, _nr10, _nr11, _nr12, _nr13, _nr14, _nr15⟩ := h
  linear_combination (1/8) * n1 + (1/8) * m2 + (1/8) * m3 + (1/8) * m6 + (1/4) * c23 + (-1/4) * c26 + (-1/2) * c34 + (1/2) * c35 + (-1/4) * c36

/-- the second anchor block holds an eighth. -/
theorem mP7 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    q7 + q15 - 1/8 = 0 := by
  obtain ⟨_n0, n1, _m1, m2, m3, _m4, _m5, m6, _c12, _c13, _c14, _c15, _c16, c23, _c24, _c25, c26, c34, c35, c36, _c45, _c46, _c56, _nq0, _nq1, _nq2, _nq3, _nq4, _nq5, _nq6, _nq7, _nq8, _nq9, _nq10, _nq11, _nq12, _nq13, _nq14, _nq15, _nr0, _nr1, _nr2, _nr3, _nr4, _nr5, _nr6, _nr7, _nr8, _nr9, _nr10, _nr11, _nr12, _nr13, _nr14, _nr15⟩ := h
  linear_combination (1/8) * n1 + (1/8) * m2 + (1/8) * m3 + (1/8) * m6 + (1/4) * c23 + (-1/4) * c26 + (1/2) * c34 + (-1/2) * c35 + (-1/4) * c36

/-- the six non-anchor blocks hold three quarters. -/
theorem mSUM6 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    q0 + q1 + q2 + q3 + q4 + q5 + q8 + q9 + q10 + q11 + q12 + q13 - 3/4 = 0 := by
  obtain ⟨n0, n1, _m1, m2, m3, _m4, _m5, m6, _c12, _c13, _c14, _c15, _c16, c23, _c24, _c25, c26, _c34, _c35, c36, _c45, _c46, _c56, _nq0, _nq1, _nq2, _nq3, _nq4, _nq5, _nq6, _nq7, _nq8, _nq9, _nq10, _nq11, _nq12, _nq13, _nq14, _nq15, _nr0, _nr1, _nr2, _nr3, _nr4, _nr5, _nr6, _nr7, _nr8, _nr9, _nr10, _nr11, _nr12, _nr13, _nr14, _nr15⟩ := h
  linear_combination (1) * n0 + (-1/4) * n1 + (-1/4) * m2 + (-1/4) * m3 + (-1/4) * m6 + (-1/2) * c23 + (1/2) * c26 + (1/2) * c36

/-- group 0 holds a quarter. -/
theorem mT0 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    q0 + q1 + q8 + q9 - 1/4 = 0 := by
  obtain ⟨n0, n1, _m1, m2, m3, _m4, _m5, m6, _c12, _c13, _c14, _c15, _c16, c23, _c24, _c25, c26, _c34, _c35, c36, _c45, _c46, _c56, _nq0, _nq1, _nq2, _nq3, _nq4, _nq5, _nq6, _nq7, _nq8, _nq9, _nq10, _nq11, _nq12, _nq13, _nq14, _nq15, _nr0, _nr1, _nr2, _nr3, _nr4, _nr5, _nr6, _nr7, _nr8, _nr9, _nr10, _nr11, _nr12, _nr13, _nr14, _nr15⟩ := h
  linear_combination (1) * n0 + (-3/4) * n1 + (-3/4) * m2 + (-3/4) * m3 + (-3/4) * m6 + (1/2) * c23 + (1/2) * c26 + (1/2) * c36

/-- group 1 holds a quarter. -/
theorem mT1 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    q2 + q3 + q10 + q11 - 1/4 = 0 := by
  obtain ⟨_n0, n1, _m1, m2, m3, _m4, _m5, m6, _c12, _c13, _c14, _c15, _c16, c23, _c24, _c25, c26, _c34, _c35, c36, _c45, _c46, _c56, _nq0, _nq1, _nq2, _nq3, _nq4, _nq5, _nq6, _nq7, _nq8, _nq9, _nq10, _nq11, _nq12, _nq13, _nq14, _nq15, _nr0, _nr1, _nr2, _nr3, _nr4, _nr5, _nr6, _nr7, _nr8, _nr9, _nr10, _nr11, _nr12, _nr13, _nr14, _nr15⟩ := h
  linear_combination (1/4) * n1 + (1/4) * m2 + (1/4) * m3 + (1/4) * m6 + (-1/2) * c23 + (-1/2) * c26 + (1/2) * c36

/-- group 2 holds a quarter. -/
theorem mT2 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    q4 + q5 + q12 + q13 - 1/4 = 0 := by
  obtain ⟨_n0, n1, _m1, m2, m3, _m4, _m5, m6, _c12, _c13, _c14, _c15, _c16, c23, _c24, _c25, c26, _c34, _c35, c36, _c45, _c46, _c56, _nq0, _nq1, _nq2, _nq3, _nq4, _nq5, _nq6, _nq7, _nq8, _nq9, _nq10, _nq11, _nq12, _nq13, _nq14, _nq15, _nr0, _nr1, _nr2, _nr3, _nr4, _nr5, _nr6, _nr7, _nr8, _nr9, _nr10, _nr11, _nr12, _nr13, _nr14, _nr15⟩ := h
  linear_combination (1/4) * n1 + (1/4) * m2 + (1/4) * m3 + (1/4) * m6 + (-1/2) * c23 + (1/2) * c26 + (-1/2) * c36

/-- group 3 holds a quarter. -/
theorem mT3 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    q6 + q7 + q14 + q15 - 1/4 = 0 := by
  obtain ⟨_n0, n1, _m1, m2, m3, _m4, _m5, m6, _c12, _c13, _c14, _c15, _c16, c23, _c24, _c25, c26, _c34, _c35, c36, _c45, _c46, _c56, _nq0, _nq1, _nq2, _nq3, _nq4, _nq5, _nq6, _nq7, _nq8, _nq9, _nq10, _nq11, _nq12, _nq13, _nq14, _nq15, _nr0, _nr1, _nr2, _nr3, _nr4, _nr5, _nr6, _nr7, _nr8, _nr9, _nr10, _nr11, _nr12, _nr13, _nr14, _nr15⟩ := h
  linear_combination (1/4) * n1 + (1/4) * m2 + (1/4) * m3 + (1/4) * m6 + (1/2) * c23 + (-1/2) * c26 + (-1/2) * c36

/-- the first block of each group holds three eighths in all. -/
theorem mT2a {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    q0 + q2 + q4 + q8 + q10 + q12 - 3/8 = 0 := by
  obtain ⟨n0, n1, _m1, m2, m3, _m4, _m5, m6, _c12, _c13, _c14, _c15, _c16, c23, _c24, c25, c26, c34, _c35, c36, c45, c46, c56, _nq0, _nq1, _nq2, _nq3, _nq4, _nq5, _nq6, _nq7, _nq8, _nq9, _nq10, _nq11, _nq12, _nq13, _nq14, _nq15, _nr0, _nr1, _nr2, _nr3, _nr4, _nr5, _nr6, _nr7, _nr8, _nr9, _nr10, _nr11, _nr12, _nr13, _nr14, _nr15⟩ := h
  linear_combination (1) * n0 + (-5/8) * n1 + (-5/8) * m2 + (-5/8) * m3 + (-1/8) * m6 + (-3/4) * c23 + (1) * c25 + (3/4) * c26 + (1) * c34 + (3/4) * c36 + (-1) * c45 + (-1/2) * c46 + (-1/2) * c56

/-- the second block of each group holds three eighths in all. -/
theorem mT2b {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    q1 + q3 + q5 + q9 + q11 + q13 - 3/8 = 0 := by
  obtain ⟨_n0, n1, _m1, m2, m3, _m4, _m5, m6, _c12, _c13, _c14, _c15, _c16, c23, _c24, c25, c26, c34, _c35, c36, c45, c46, c56, _nq0, _nq1, _nq2, _nq3, _nq4, _nq5, _nq6, _nq7, _nq8, _nq9, _nq10, _nq11, _nq12, _nq13, _nq14, _nq15, _nr0, _nr1, _nr2, _nr3, _nr4, _nr5, _nr6, _nr7, _nr8, _nr9, _nr10, _nr11, _nr12, _nr13, _nr14, _nr15⟩ := h
  linear_combination (3/8) * n1 + (3/8) * m2 + (3/8) * m3 + (-1/8) * m6 + (1/4) * c23 + (-1) * c25 + (-1/4) * c26 + (-1) * c34 + (-1/4) * c36 + (1) * c45 + (1/2) * c46 + (1/2) * c56

/-! ## The Walsh sums -/

def ef0  : SS.BitString 6 := bs false false false false false false -- flip 000000
def ef1  : SS.BitString 6 := bs false false false false false true  -- flip 000001
def ef2  : SS.BitString 6 := bs false false false false true  true  -- flip 000011
def ef3  : SS.BitString 6 := bs false false false true  false true  -- flip 000101
def ef4  : SS.BitString 6 := bs false false true  false false false -- flip 001000
def ef5  : SS.BitString 6 := bs false false true  false true  false -- flip 001010
def ef6  : SS.BitString 6 := bs false false true  true  false false -- flip 001100
def ef7  : SS.BitString 6 := bs false true  false false false false -- flip 010000
def ef8  : SS.BitString 6 := bs false true  false false true  false -- flip 010010
def ef9  : SS.BitString 6 := bs false true  false true  false false -- flip 010100
def ef10 : SS.BitString 6 := bs true  false false false false false -- flip 100000
def ef11 : SS.BitString 6 := bs true  false false false false true  -- flip 100001
def ef12 : SS.BitString 6 := bs true  false true  false false false -- flip 101000
def ef13 : SS.BitString 6 := bs true  true  false false false false -- flip 110000

def w0  : SS.BitString 6 := bs false false false false false false -- dressing 000000
def w1  : SS.BitString 6 := bs false false false false false true  -- dressing 000001
def w2  : SS.BitString 6 := bs false false false false true  false -- dressing 000010
def w3  : SS.BitString 6 := bs false false false true  false false -- dressing 000100
def w4  : SS.BitString 6 := bs false false true  false false false -- dressing 001000
def w5  : SS.BitString 6 := bs false true  false false false false -- dressing 010000
def w6  : SS.BitString 6 := bs true  false false false false false -- dressing 100000
def w7  : SS.BitString 6 := bs true  false false false false true  -- dressing 100001
def w8  : SS.BitString 6 := bs true  false true  false false false -- dressing 101000
def w9  : SS.BitString 6 := bs true  true  false false false false -- dressing 110000

/-- `<0_L| X^e Z^z |1_L>` with the global prefactor omitted. -/
def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),
      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

/-- `<0_L| X^e Z^z |0_L>`. -/
def diagBot (c : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ x ∈ S0.filter (fun x => SS.bxor x e ∈ S0),
      SixQubit.signMul (SS.bdot z x) (star (c (SS.bxor x e)) * c x)

/-- `<1_L| X^e Z^z |1_L>`. -/
def diagTop (d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S1),
      SixQubit.signMul (SS.bdot z y) (star (d (SS.bxor y e)) * d y)

/-- `star z * z` is the squared modulus. -/
theorem sq (z : ℂ) : star z * z = (Complex.normSq z : ℂ) := by
  rw [Complex.normSq_eq_conj_mul_self]; rfl

/-- The bridge to `SixQubit.Block26`: its `ip` is this file's `star`-pairing. -/
theorem ip_eq (a1 a2 b1 b2 : ℂ) :
    SixQubit.Block26.ip a1 a2 b1 b2 = star a1 * b1 + star a2 * b2 := rfl

/-! ### Incidences, flips and signs -/

theorem incO_1 :
    S1.filter (fun y => SS.bxor y ef1 ∈ S0) = {z2, z3, z4, z5, z10, z11, z12, z13} := by decide
theorem fo_1_2 : SS.bxor z2 ef1 = y2 := by decide
theorem fo_1_3 : SS.bxor z3 ef1 = y3 := by decide
theorem fo_1_4 : SS.bxor z4 ef1 = y4 := by decide
theorem fo_1_5 : SS.bxor z5 ef1 = y5 := by decide
theorem fo_1_10 : SS.bxor z10 ef1 = y10 := by decide
theorem fo_1_11 : SS.bxor z11 ef1 = y11 := by decide
theorem fo_1_12 : SS.bxor z12 ef1 = y12 := by decide
theorem fo_1_13 : SS.bxor z13 ef1 = y13 := by decide
theorem incO_2 :
    S1.filter (fun y => SS.bxor y ef2 ∈ S0) = {z0, z1, z6, z7, z8, z9, z14, z15} := by decide
theorem fo_2_0 : SS.bxor z0 ef2 = y0 := by decide
theorem fo_2_1 : SS.bxor z1 ef2 = y1 := by decide
theorem fo_2_6 : SS.bxor z6 ef2 = y6 := by decide
theorem fo_2_7 : SS.bxor z7 ef2 = y7 := by decide
theorem fo_2_8 : SS.bxor z8 ef2 = y8 := by decide
theorem fo_2_9 : SS.bxor z9 ef2 = y9 := by decide
theorem fo_2_14 : SS.bxor z14 ef2 = y14 := by decide
theorem fo_2_15 : SS.bxor z15 ef2 = y15 := by decide
theorem incO_3 :
    S1.filter (fun y => SS.bxor y ef3 ∈ S0) = {z0, z1, z6, z7, z8, z9, z14, z15} := by decide
theorem fo_3_0 : SS.bxor z0 ef3 = y1 := by decide
theorem fo_3_1 : SS.bxor z1 ef3 = y0 := by decide
theorem fo_3_6 : SS.bxor z6 ef3 = y7 := by decide
theorem fo_3_7 : SS.bxor z7 ef3 = y6 := by decide
theorem fo_3_8 : SS.bxor z8 ef3 = y9 := by decide
theorem fo_3_9 : SS.bxor z9 ef3 = y8 := by decide
theorem fo_3_14 : SS.bxor z14 ef3 = y15 := by decide
theorem fo_3_15 : SS.bxor z15 ef3 = y14 := by decide
theorem incO_4 :
    S1.filter (fun y => SS.bxor y ef4 ∈ S0) = {z2, z3, z6, z7, z10, z11, z14, z15} := by decide
theorem fo_4_2 : SS.bxor z2 ef4 = y0 := by decide
theorem fo_4_3 : SS.bxor z3 ef4 = y1 := by decide
theorem fo_4_6 : SS.bxor z6 ef4 = y4 := by decide
theorem fo_4_7 : SS.bxor z7 ef4 = y5 := by decide
theorem fo_4_10 : SS.bxor z10 ef4 = y8 := by decide
theorem fo_4_11 : SS.bxor z11 ef4 = y9 := by decide
theorem fo_4_14 : SS.bxor z14 ef4 = y12 := by decide
theorem fo_4_15 : SS.bxor z15 ef4 = y13 := by decide
theorem incO_5 :
    S1.filter (fun y => SS.bxor y ef5 ∈ S0) = {z0, z1, z4, z5, z8, z9, z12, z13} := by decide
theorem fo_5_0 : SS.bxor z0 ef5 = y2 := by decide
theorem fo_5_1 : SS.bxor z1 ef5 = y3 := by decide
theorem fo_5_4 : SS.bxor z4 ef5 = y6 := by decide
theorem fo_5_5 : SS.bxor z5 ef5 = y7 := by decide
theorem fo_5_8 : SS.bxor z8 ef5 = y10 := by decide
theorem fo_5_9 : SS.bxor z9 ef5 = y11 := by decide
theorem fo_5_12 : SS.bxor z12 ef5 = y14 := by decide
theorem fo_5_13 : SS.bxor z13 ef5 = y15 := by decide
theorem incO_6 :
    S1.filter (fun y => SS.bxor y ef6 ∈ S0) = {z0, z1, z4, z5, z8, z9, z12, z13} := by decide
theorem fo_6_0 : SS.bxor z0 ef6 = y3 := by decide
theorem fo_6_1 : SS.bxor z1 ef6 = y2 := by decide
theorem fo_6_4 : SS.bxor z4 ef6 = y7 := by decide
theorem fo_6_5 : SS.bxor z5 ef6 = y6 := by decide
theorem fo_6_8 : SS.bxor z8 ef6 = y11 := by decide
theorem fo_6_9 : SS.bxor z9 ef6 = y10 := by decide
theorem fo_6_12 : SS.bxor z12 ef6 = y15 := by decide
theorem fo_6_13 : SS.bxor z13 ef6 = y14 := by decide
theorem incO_7 :
    S1.filter (fun y => SS.bxor y ef7 ∈ S0) = {z4, z5, z6, z7, z12, z13, z14, z15} := by decide
theorem fo_7_4 : SS.bxor z4 ef7 = y0 := by decide
theorem fo_7_5 : SS.bxor z5 ef7 = y1 := by decide
theorem fo_7_6 : SS.bxor z6 ef7 = y2 := by decide
theorem fo_7_7 : SS.bxor z7 ef7 = y3 := by decide
theorem fo_7_12 : SS.bxor z12 ef7 = y8 := by decide
theorem fo_7_13 : SS.bxor z13 ef7 = y9 := by decide
theorem fo_7_14 : SS.bxor z14 ef7 = y10 := by decide
theorem fo_7_15 : SS.bxor z15 ef7 = y11 := by decide
theorem incO_8 :
    S1.filter (fun y => SS.bxor y ef8 ∈ S0) = {z0, z1, z2, z3, z8, z9, z10, z11} := by decide
theorem fo_8_0 : SS.bxor z0 ef8 = y4 := by decide
theorem fo_8_1 : SS.bxor z1 ef8 = y5 := by decide
theorem fo_8_2 : SS.bxor z2 ef8 = y6 := by decide
theorem fo_8_3 : SS.bxor z3 ef8 = y7 := by decide
theorem fo_8_8 : SS.bxor z8 ef8 = y12 := by decide
theorem fo_8_9 : SS.bxor z9 ef8 = y13 := by decide
theorem fo_8_10 : SS.bxor z10 ef8 = y14 := by decide
theorem fo_8_11 : SS.bxor z11 ef8 = y15 := by decide
theorem incO_9 :
    S1.filter (fun y => SS.bxor y ef9 ∈ S0) = {z0, z1, z2, z3, z8, z9, z10, z11} := by decide
theorem fo_9_0 : SS.bxor z0 ef9 = y5 := by decide
theorem fo_9_1 : SS.bxor z1 ef9 = y4 := by decide
theorem fo_9_2 : SS.bxor z2 ef9 = y7 := by decide
theorem fo_9_3 : SS.bxor z3 ef9 = y6 := by decide
theorem fo_9_8 : SS.bxor z8 ef9 = y13 := by decide
theorem fo_9_9 : SS.bxor z9 ef9 = y12 := by decide
theorem fo_9_10 : SS.bxor z10 ef9 = y15 := by decide
theorem fo_9_11 : SS.bxor z11 ef9 = y14 := by decide
theorem incO_11 :
    S1.filter (fun y => SS.bxor y ef11 ∈ S0) = {z2, z3, z4, z5, z10, z11, z12, z13} := by decide
theorem fo_11_2 : SS.bxor z2 ef11 = y10 := by decide
theorem fo_11_3 : SS.bxor z3 ef11 = y11 := by decide
theorem fo_11_4 : SS.bxor z4 ef11 = y12 := by decide
theorem fo_11_5 : SS.bxor z5 ef11 = y13 := by decide
theorem fo_11_10 : SS.bxor z10 ef11 = y2 := by decide
theorem fo_11_11 : SS.bxor z11 ef11 = y3 := by decide
theorem fo_11_12 : SS.bxor z12 ef11 = y4 := by decide
theorem fo_11_13 : SS.bxor z13 ef11 = y5 := by decide
theorem incO_12 :
    S1.filter (fun y => SS.bxor y ef12 ∈ S0) = {z2, z3, z6, z7, z10, z11, z14, z15} := by decide
theorem fo_12_2 : SS.bxor z2 ef12 = y8 := by decide
theorem fo_12_3 : SS.bxor z3 ef12 = y9 := by decide
theorem fo_12_6 : SS.bxor z6 ef12 = y12 := by decide
theorem fo_12_7 : SS.bxor z7 ef12 = y13 := by decide
theorem fo_12_10 : SS.bxor z10 ef12 = y0 := by decide
theorem fo_12_11 : SS.bxor z11 ef12 = y1 := by decide
theorem fo_12_14 : SS.bxor z14 ef12 = y4 := by decide
theorem fo_12_15 : SS.bxor z15 ef12 = y5 := by decide
theorem incO_13 :
    S1.filter (fun y => SS.bxor y ef13 ∈ S0) = {z4, z5, z6, z7, z12, z13, z14, z15} := by decide
theorem fo_13_4 : SS.bxor z4 ef13 = y8 := by decide
theorem fo_13_5 : SS.bxor z5 ef13 = y9 := by decide
theorem fo_13_6 : SS.bxor z6 ef13 = y10 := by decide
theorem fo_13_7 : SS.bxor z7 ef13 = y11 := by decide
theorem fo_13_12 : SS.bxor z12 ef13 = y0 := by decide
theorem fo_13_13 : SS.bxor z13 ef13 = y1 := by decide
theorem fo_13_14 : SS.bxor z14 ef13 = y2 := by decide
theorem fo_13_15 : SS.bxor z15 ef13 = y3 := by decide

theorem incB_0 :
    S0.filter (fun x => SS.bxor x ef0 ∈ S0) = {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15} := by decide
theorem incT_0 :
    S1.filter (fun y => SS.bxor y ef0 ∈ S1) = {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15} := by decide
theorem fb_0_0 : SS.bxor y0 ef0 = y0 := by decide
theorem fb_0_1 : SS.bxor y1 ef0 = y1 := by decide
theorem fb_0_2 : SS.bxor y2 ef0 = y2 := by decide
theorem fb_0_3 : SS.bxor y3 ef0 = y3 := by decide
theorem fb_0_4 : SS.bxor y4 ef0 = y4 := by decide
theorem fb_0_5 : SS.bxor y5 ef0 = y5 := by decide
theorem fb_0_6 : SS.bxor y6 ef0 = y6 := by decide
theorem fb_0_7 : SS.bxor y7 ef0 = y7 := by decide
theorem fb_0_8 : SS.bxor y8 ef0 = y8 := by decide
theorem fb_0_9 : SS.bxor y9 ef0 = y9 := by decide
theorem fb_0_10 : SS.bxor y10 ef0 = y10 := by decide
theorem fb_0_11 : SS.bxor y11 ef0 = y11 := by decide
theorem fb_0_12 : SS.bxor y12 ef0 = y12 := by decide
theorem fb_0_13 : SS.bxor y13 ef0 = y13 := by decide
theorem fb_0_14 : SS.bxor y14 ef0 = y14 := by decide
theorem fb_0_15 : SS.bxor y15 ef0 = y15 := by decide
theorem ft_0_0 : SS.bxor z0 ef0 = z0 := by decide
theorem ft_0_1 : SS.bxor z1 ef0 = z1 := by decide
theorem ft_0_2 : SS.bxor z2 ef0 = z2 := by decide
theorem ft_0_3 : SS.bxor z3 ef0 = z3 := by decide
theorem ft_0_4 : SS.bxor z4 ef0 = z4 := by decide
theorem ft_0_5 : SS.bxor z5 ef0 = z5 := by decide
theorem ft_0_6 : SS.bxor z6 ef0 = z6 := by decide
theorem ft_0_7 : SS.bxor z7 ef0 = z7 := by decide
theorem ft_0_8 : SS.bxor z8 ef0 = z8 := by decide
theorem ft_0_9 : SS.bxor z9 ef0 = z9 := by decide
theorem ft_0_10 : SS.bxor z10 ef0 = z10 := by decide
theorem ft_0_11 : SS.bxor z11 ef0 = z11 := by decide
theorem ft_0_12 : SS.bxor z12 ef0 = z12 := by decide
theorem ft_0_13 : SS.bxor z13 ef0 = z13 := by decide
theorem ft_0_14 : SS.bxor z14 ef0 = z14 := by decide
theorem ft_0_15 : SS.bxor z15 ef0 = z15 := by decide
theorem incB_10 :
    S0.filter (fun x => SS.bxor x ef10 ∈ S0) = {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15} := by decide
theorem incT_10 :
    S1.filter (fun y => SS.bxor y ef10 ∈ S1) = {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15} := by decide
theorem fb_10_0 : SS.bxor y0 ef10 = y8 := by decide
theorem fb_10_1 : SS.bxor y1 ef10 = y9 := by decide
theorem fb_10_2 : SS.bxor y2 ef10 = y10 := by decide
theorem fb_10_3 : SS.bxor y3 ef10 = y11 := by decide
theorem fb_10_4 : SS.bxor y4 ef10 = y12 := by decide
theorem fb_10_5 : SS.bxor y5 ef10 = y13 := by decide
theorem fb_10_6 : SS.bxor y6 ef10 = y14 := by decide
theorem fb_10_7 : SS.bxor y7 ef10 = y15 := by decide
theorem fb_10_8 : SS.bxor y8 ef10 = y0 := by decide
theorem fb_10_9 : SS.bxor y9 ef10 = y1 := by decide
theorem fb_10_10 : SS.bxor y10 ef10 = y2 := by decide
theorem fb_10_11 : SS.bxor y11 ef10 = y3 := by decide
theorem fb_10_12 : SS.bxor y12 ef10 = y4 := by decide
theorem fb_10_13 : SS.bxor y13 ef10 = y5 := by decide
theorem fb_10_14 : SS.bxor y14 ef10 = y6 := by decide
theorem fb_10_15 : SS.bxor y15 ef10 = y7 := by decide
theorem ft_10_0 : SS.bxor z0 ef10 = z8 := by decide
theorem ft_10_1 : SS.bxor z1 ef10 = z9 := by decide
theorem ft_10_2 : SS.bxor z2 ef10 = z10 := by decide
theorem ft_10_3 : SS.bxor z3 ef10 = z11 := by decide
theorem ft_10_4 : SS.bxor z4 ef10 = z12 := by decide
theorem ft_10_5 : SS.bxor z5 ef10 = z13 := by decide
theorem ft_10_6 : SS.bxor z6 ef10 = z14 := by decide
theorem ft_10_7 : SS.bxor z7 ef10 = z15 := by decide
theorem ft_10_8 : SS.bxor z8 ef10 = z0 := by decide
theorem ft_10_9 : SS.bxor z9 ef10 = z1 := by decide
theorem ft_10_10 : SS.bxor z10 ef10 = z2 := by decide
theorem ft_10_11 : SS.bxor z11 ef10 = z3 := by decide
theorem ft_10_12 : SS.bxor z12 ef10 = z4 := by decide
theorem ft_10_13 : SS.bxor z13 ef10 = z5 := by decide
theorem ft_10_14 : SS.bxor z14 ef10 = z6 := by decide
theorem ft_10_15 : SS.bxor z15 ef10 = z7 := by decide

theorem sy_0_0 : SS.bdot w0 y0 = false := by decide
theorem sy_0_1 : SS.bdot w0 y1 = false := by decide
theorem sy_0_2 : SS.bdot w0 y2 = false := by decide
theorem sy_0_3 : SS.bdot w0 y3 = false := by decide
theorem sy_0_4 : SS.bdot w0 y4 = false := by decide
theorem sy_0_5 : SS.bdot w0 y5 = false := by decide
theorem sy_0_6 : SS.bdot w0 y6 = false := by decide
theorem sy_0_7 : SS.bdot w0 y7 = false := by decide
theorem sy_0_8 : SS.bdot w0 y8 = false := by decide
theorem sy_0_9 : SS.bdot w0 y9 = false := by decide
theorem sy_0_10 : SS.bdot w0 y10 = false := by decide
theorem sy_0_11 : SS.bdot w0 y11 = false := by decide
theorem sy_0_12 : SS.bdot w0 y12 = false := by decide
theorem sy_0_13 : SS.bdot w0 y13 = false := by decide
theorem sy_0_14 : SS.bdot w0 y14 = false := by decide
theorem sy_0_15 : SS.bdot w0 y15 = false := by decide
theorem sy_1_0 : SS.bdot w1 y0 = false := by decide
theorem sy_1_1 : SS.bdot w1 y1 = false := by decide
theorem sy_1_2 : SS.bdot w1 y2 = true := by decide
theorem sy_1_3 : SS.bdot w1 y3 = true := by decide
theorem sy_1_4 : SS.bdot w1 y4 = true := by decide
theorem sy_1_5 : SS.bdot w1 y5 = true := by decide
theorem sy_1_6 : SS.bdot w1 y6 = false := by decide
theorem sy_1_7 : SS.bdot w1 y7 = false := by decide
theorem sy_1_8 : SS.bdot w1 y8 = false := by decide
theorem sy_1_9 : SS.bdot w1 y9 = false := by decide
theorem sy_1_10 : SS.bdot w1 y10 = true := by decide
theorem sy_1_11 : SS.bdot w1 y11 = true := by decide
theorem sy_1_12 : SS.bdot w1 y12 = true := by decide
theorem sy_1_13 : SS.bdot w1 y13 = true := by decide
theorem sy_1_14 : SS.bdot w1 y14 = false := by decide
theorem sy_1_15 : SS.bdot w1 y15 = false := by decide
theorem sy_4_0 : SS.bdot w4 y0 = false := by decide
theorem sy_4_1 : SS.bdot w4 y1 = false := by decide
theorem sy_4_2 : SS.bdot w4 y2 = true := by decide
theorem sy_4_3 : SS.bdot w4 y3 = true := by decide
theorem sy_4_4 : SS.bdot w4 y4 = false := by decide
theorem sy_4_5 : SS.bdot w4 y5 = false := by decide
theorem sy_4_6 : SS.bdot w4 y6 = true := by decide
theorem sy_4_7 : SS.bdot w4 y7 = true := by decide
theorem sy_4_8 : SS.bdot w4 y8 = false := by decide
theorem sy_4_9 : SS.bdot w4 y9 = false := by decide
theorem sy_4_10 : SS.bdot w4 y10 = true := by decide
theorem sy_4_11 : SS.bdot w4 y11 = true := by decide
theorem sy_4_12 : SS.bdot w4 y12 = false := by decide
theorem sy_4_13 : SS.bdot w4 y13 = false := by decide
theorem sy_4_14 : SS.bdot w4 y14 = true := by decide
theorem sy_4_15 : SS.bdot w4 y15 = true := by decide
theorem sy_5_0 : SS.bdot w5 y0 = false := by decide
theorem sy_5_1 : SS.bdot w5 y1 = false := by decide
theorem sy_5_2 : SS.bdot w5 y2 = false := by decide
theorem sy_5_3 : SS.bdot w5 y3 = false := by decide
theorem sy_5_4 : SS.bdot w5 y4 = true := by decide
theorem sy_5_5 : SS.bdot w5 y5 = true := by decide
theorem sy_5_6 : SS.bdot w5 y6 = true := by decide
theorem sy_5_7 : SS.bdot w5 y7 = true := by decide
theorem sy_5_8 : SS.bdot w5 y8 = false := by decide
theorem sy_5_9 : SS.bdot w5 y9 = false := by decide
theorem sy_5_10 : SS.bdot w5 y10 = false := by decide
theorem sy_5_11 : SS.bdot w5 y11 = false := by decide
theorem sy_5_12 : SS.bdot w5 y12 = true := by decide
theorem sy_5_13 : SS.bdot w5 y13 = true := by decide
theorem sy_5_14 : SS.bdot w5 y14 = true := by decide
theorem sy_5_15 : SS.bdot w5 y15 = true := by decide
theorem sy_6_0 : SS.bdot w6 y0 = false := by decide
theorem sy_6_1 : SS.bdot w6 y1 = false := by decide
theorem sy_6_2 : SS.bdot w6 y2 = false := by decide
theorem sy_6_3 : SS.bdot w6 y3 = false := by decide
theorem sy_6_4 : SS.bdot w6 y4 = false := by decide
theorem sy_6_5 : SS.bdot w6 y5 = false := by decide
theorem sy_6_6 : SS.bdot w6 y6 = false := by decide
theorem sy_6_7 : SS.bdot w6 y7 = false := by decide
theorem sy_6_8 : SS.bdot w6 y8 = true := by decide
theorem sy_6_9 : SS.bdot w6 y9 = true := by decide
theorem sy_6_10 : SS.bdot w6 y10 = true := by decide
theorem sy_6_11 : SS.bdot w6 y11 = true := by decide
theorem sy_6_12 : SS.bdot w6 y12 = true := by decide
theorem sy_6_13 : SS.bdot w6 y13 = true := by decide
theorem sy_6_14 : SS.bdot w6 y14 = true := by decide
theorem sy_6_15 : SS.bdot w6 y15 = true := by decide
theorem sy_7_0 : SS.bdot w7 y0 = false := by decide
theorem sy_7_1 : SS.bdot w7 y1 = false := by decide
theorem sy_7_2 : SS.bdot w7 y2 = true := by decide
theorem sy_7_3 : SS.bdot w7 y3 = true := by decide
theorem sy_7_4 : SS.bdot w7 y4 = true := by decide
theorem sy_7_5 : SS.bdot w7 y5 = true := by decide
theorem sy_7_6 : SS.bdot w7 y6 = false := by decide
theorem sy_7_7 : SS.bdot w7 y7 = false := by decide
theorem sy_7_8 : SS.bdot w7 y8 = true := by decide
theorem sy_7_9 : SS.bdot w7 y9 = true := by decide
theorem sy_7_10 : SS.bdot w7 y10 = false := by decide
theorem sy_7_11 : SS.bdot w7 y11 = false := by decide
theorem sy_7_12 : SS.bdot w7 y12 = false := by decide
theorem sy_7_13 : SS.bdot w7 y13 = false := by decide
theorem sy_7_14 : SS.bdot w7 y14 = true := by decide
theorem sy_7_15 : SS.bdot w7 y15 = true := by decide
theorem sy_8_0 : SS.bdot w8 y0 = false := by decide
theorem sy_8_1 : SS.bdot w8 y1 = false := by decide
theorem sy_8_2 : SS.bdot w8 y2 = true := by decide
theorem sy_8_3 : SS.bdot w8 y3 = true := by decide
theorem sy_8_4 : SS.bdot w8 y4 = false := by decide
theorem sy_8_5 : SS.bdot w8 y5 = false := by decide
theorem sy_8_6 : SS.bdot w8 y6 = true := by decide
theorem sy_8_7 : SS.bdot w8 y7 = true := by decide
theorem sy_8_8 : SS.bdot w8 y8 = true := by decide
theorem sy_8_9 : SS.bdot w8 y9 = true := by decide
theorem sy_8_10 : SS.bdot w8 y10 = false := by decide
theorem sy_8_11 : SS.bdot w8 y11 = false := by decide
theorem sy_8_12 : SS.bdot w8 y12 = true := by decide
theorem sy_8_13 : SS.bdot w8 y13 = true := by decide
theorem sy_8_14 : SS.bdot w8 y14 = false := by decide
theorem sy_8_15 : SS.bdot w8 y15 = false := by decide
theorem sy_9_0 : SS.bdot w9 y0 = false := by decide
theorem sy_9_1 : SS.bdot w9 y1 = false := by decide
theorem sy_9_2 : SS.bdot w9 y2 = false := by decide
theorem sy_9_3 : SS.bdot w9 y3 = false := by decide
theorem sy_9_4 : SS.bdot w9 y4 = true := by decide
theorem sy_9_5 : SS.bdot w9 y5 = true := by decide
theorem sy_9_6 : SS.bdot w9 y6 = true := by decide
theorem sy_9_7 : SS.bdot w9 y7 = true := by decide
theorem sy_9_8 : SS.bdot w9 y8 = true := by decide
theorem sy_9_9 : SS.bdot w9 y9 = true := by decide
theorem sy_9_10 : SS.bdot w9 y10 = true := by decide
theorem sy_9_11 : SS.bdot w9 y11 = true := by decide
theorem sy_9_12 : SS.bdot w9 y12 = false := by decide
theorem sy_9_13 : SS.bdot w9 y13 = false := by decide
theorem sy_9_14 : SS.bdot w9 y14 = false := by decide
theorem sy_9_15 : SS.bdot w9 y15 = false := by decide
theorem sz_0_0 : SS.bdot w0 z0 = false := by decide
theorem sz_0_1 : SS.bdot w0 z1 = false := by decide
theorem sz_0_2 : SS.bdot w0 z2 = false := by decide
theorem sz_0_3 : SS.bdot w0 z3 = false := by decide
theorem sz_0_4 : SS.bdot w0 z4 = false := by decide
theorem sz_0_5 : SS.bdot w0 z5 = false := by decide
theorem sz_0_6 : SS.bdot w0 z6 = false := by decide
theorem sz_0_7 : SS.bdot w0 z7 = false := by decide
theorem sz_0_8 : SS.bdot w0 z8 = false := by decide
theorem sz_0_9 : SS.bdot w0 z9 = false := by decide
theorem sz_0_10 : SS.bdot w0 z10 = false := by decide
theorem sz_0_11 : SS.bdot w0 z11 = false := by decide
theorem sz_0_12 : SS.bdot w0 z12 = false := by decide
theorem sz_0_13 : SS.bdot w0 z13 = false := by decide
theorem sz_0_14 : SS.bdot w0 z14 = false := by decide
theorem sz_0_15 : SS.bdot w0 z15 = false := by decide
theorem sz_1_0 : SS.bdot w1 z0 = true := by decide
theorem sz_1_1 : SS.bdot w1 z1 = true := by decide
theorem sz_1_2 : SS.bdot w1 z2 = false := by decide
theorem sz_1_3 : SS.bdot w1 z3 = false := by decide
theorem sz_1_4 : SS.bdot w1 z4 = false := by decide
theorem sz_1_5 : SS.bdot w1 z5 = false := by decide
theorem sz_1_6 : SS.bdot w1 z6 = true := by decide
theorem sz_1_7 : SS.bdot w1 z7 = true := by decide
theorem sz_1_8 : SS.bdot w1 z8 = true := by decide
theorem sz_1_9 : SS.bdot w1 z9 = true := by decide
theorem sz_1_10 : SS.bdot w1 z10 = false := by decide
theorem sz_1_11 : SS.bdot w1 z11 = false := by decide
theorem sz_1_12 : SS.bdot w1 z12 = false := by decide
theorem sz_1_13 : SS.bdot w1 z13 = false := by decide
theorem sz_1_14 : SS.bdot w1 z14 = true := by decide
theorem sz_1_15 : SS.bdot w1 z15 = true := by decide
theorem sz_2_0 : SS.bdot w2 z0 = true := by decide
theorem sz_2_1 : SS.bdot w2 z1 = false := by decide
theorem sz_2_2 : SS.bdot w2 z2 = false := by decide
theorem sz_2_3 : SS.bdot w2 z3 = true := by decide
theorem sz_2_4 : SS.bdot w2 z4 = false := by decide
theorem sz_2_5 : SS.bdot w2 z5 = true := by decide
theorem sz_2_6 : SS.bdot w2 z6 = false := by decide
theorem sz_2_7 : SS.bdot w2 z7 = true := by decide
theorem sz_2_8 : SS.bdot w2 z8 = true := by decide
theorem sz_2_9 : SS.bdot w2 z9 = false := by decide
theorem sz_2_10 : SS.bdot w2 z10 = false := by decide
theorem sz_2_11 : SS.bdot w2 z11 = true := by decide
theorem sz_2_12 : SS.bdot w2 z12 = false := by decide
theorem sz_2_13 : SS.bdot w2 z13 = true := by decide
theorem sz_2_14 : SS.bdot w2 z14 = false := by decide
theorem sz_2_15 : SS.bdot w2 z15 = true := by decide
theorem sz_3_0 : SS.bdot w3 z0 = false := by decide
theorem sz_3_1 : SS.bdot w3 z1 = true := by decide
theorem sz_3_2 : SS.bdot w3 z2 = false := by decide
theorem sz_3_3 : SS.bdot w3 z3 = true := by decide
theorem sz_3_4 : SS.bdot w3 z4 = false := by decide
theorem sz_3_5 : SS.bdot w3 z5 = true := by decide
theorem sz_3_6 : SS.bdot w3 z6 = false := by decide
theorem sz_3_7 : SS.bdot w3 z7 = true := by decide
theorem sz_3_8 : SS.bdot w3 z8 = false := by decide
theorem sz_3_9 : SS.bdot w3 z9 = true := by decide
theorem sz_3_10 : SS.bdot w3 z10 = false := by decide
theorem sz_3_11 : SS.bdot w3 z11 = true := by decide
theorem sz_3_12 : SS.bdot w3 z12 = false := by decide
theorem sz_3_13 : SS.bdot w3 z13 = true := by decide
theorem sz_3_14 : SS.bdot w3 z14 = false := by decide
theorem sz_3_15 : SS.bdot w3 z15 = true := by decide
theorem sz_4_0 : SS.bdot w4 z0 = false := by decide
theorem sz_4_1 : SS.bdot w4 z1 = false := by decide
theorem sz_4_2 : SS.bdot w4 z2 = true := by decide
theorem sz_4_3 : SS.bdot w4 z3 = true := by decide
theorem sz_4_4 : SS.bdot w4 z4 = false := by decide
theorem sz_4_5 : SS.bdot w4 z5 = false := by decide
theorem sz_4_6 : SS.bdot w4 z6 = true := by decide
theorem sz_4_7 : SS.bdot w4 z7 = true := by decide
theorem sz_4_8 : SS.bdot w4 z8 = false := by decide
theorem sz_4_9 : SS.bdot w4 z9 = false := by decide
theorem sz_4_10 : SS.bdot w4 z10 = true := by decide
theorem sz_4_11 : SS.bdot w4 z11 = true := by decide
theorem sz_4_12 : SS.bdot w4 z12 = false := by decide
theorem sz_4_13 : SS.bdot w4 z13 = false := by decide
theorem sz_4_14 : SS.bdot w4 z14 = true := by decide
theorem sz_4_15 : SS.bdot w4 z15 = true := by decide
theorem sz_5_0 : SS.bdot w5 z0 = false := by decide
theorem sz_5_1 : SS.bdot w5 z1 = false := by decide
theorem sz_5_2 : SS.bdot w5 z2 = false := by decide
theorem sz_5_3 : SS.bdot w5 z3 = false := by decide
theorem sz_5_4 : SS.bdot w5 z4 = true := by decide
theorem sz_5_5 : SS.bdot w5 z5 = true := by decide
theorem sz_5_6 : SS.bdot w5 z6 = true := by decide
theorem sz_5_7 : SS.bdot w5 z7 = true := by decide
theorem sz_5_8 : SS.bdot w5 z8 = false := by decide
theorem sz_5_9 : SS.bdot w5 z9 = false := by decide
theorem sz_5_10 : SS.bdot w5 z10 = false := by decide
theorem sz_5_11 : SS.bdot w5 z11 = false := by decide
theorem sz_5_12 : SS.bdot w5 z12 = true := by decide
theorem sz_5_13 : SS.bdot w5 z13 = true := by decide
theorem sz_5_14 : SS.bdot w5 z14 = true := by decide
theorem sz_5_15 : SS.bdot w5 z15 = true := by decide
theorem sz_6_0 : SS.bdot w6 z0 = false := by decide
theorem sz_6_1 : SS.bdot w6 z1 = false := by decide
theorem sz_6_2 : SS.bdot w6 z2 = false := by decide
theorem sz_6_3 : SS.bdot w6 z3 = false := by decide
theorem sz_6_4 : SS.bdot w6 z4 = false := by decide
theorem sz_6_5 : SS.bdot w6 z5 = false := by decide
theorem sz_6_6 : SS.bdot w6 z6 = false := by decide
theorem sz_6_7 : SS.bdot w6 z7 = false := by decide
theorem sz_6_8 : SS.bdot w6 z8 = true := by decide
theorem sz_6_9 : SS.bdot w6 z9 = true := by decide
theorem sz_6_10 : SS.bdot w6 z10 = true := by decide
theorem sz_6_11 : SS.bdot w6 z11 = true := by decide
theorem sz_6_12 : SS.bdot w6 z12 = true := by decide
theorem sz_6_13 : SS.bdot w6 z13 = true := by decide
theorem sz_6_14 : SS.bdot w6 z14 = true := by decide
theorem sz_6_15 : SS.bdot w6 z15 = true := by decide
theorem sz_7_0 : SS.bdot w7 z0 = true := by decide
theorem sz_7_1 : SS.bdot w7 z1 = true := by decide
theorem sz_7_2 : SS.bdot w7 z2 = false := by decide
theorem sz_7_3 : SS.bdot w7 z3 = false := by decide
theorem sz_7_4 : SS.bdot w7 z4 = false := by decide
theorem sz_7_5 : SS.bdot w7 z5 = false := by decide
theorem sz_7_6 : SS.bdot w7 z6 = true := by decide
theorem sz_7_7 : SS.bdot w7 z7 = true := by decide
theorem sz_7_8 : SS.bdot w7 z8 = false := by decide
theorem sz_7_9 : SS.bdot w7 z9 = false := by decide
theorem sz_7_10 : SS.bdot w7 z10 = true := by decide
theorem sz_7_11 : SS.bdot w7 z11 = true := by decide
theorem sz_7_12 : SS.bdot w7 z12 = true := by decide
theorem sz_7_13 : SS.bdot w7 z13 = true := by decide
theorem sz_7_14 : SS.bdot w7 z14 = false := by decide
theorem sz_7_15 : SS.bdot w7 z15 = false := by decide
theorem sz_8_0 : SS.bdot w8 z0 = false := by decide
theorem sz_8_1 : SS.bdot w8 z1 = false := by decide
theorem sz_8_2 : SS.bdot w8 z2 = true := by decide
theorem sz_8_3 : SS.bdot w8 z3 = true := by decide
theorem sz_8_4 : SS.bdot w8 z4 = false := by decide
theorem sz_8_5 : SS.bdot w8 z5 = false := by decide
theorem sz_8_6 : SS.bdot w8 z6 = true := by decide
theorem sz_8_7 : SS.bdot w8 z7 = true := by decide
theorem sz_8_8 : SS.bdot w8 z8 = true := by decide
theorem sz_8_9 : SS.bdot w8 z9 = true := by decide
theorem sz_8_10 : SS.bdot w8 z10 = false := by decide
theorem sz_8_11 : SS.bdot w8 z11 = false := by decide
theorem sz_8_12 : SS.bdot w8 z12 = true := by decide
theorem sz_8_13 : SS.bdot w8 z13 = true := by decide
theorem sz_8_14 : SS.bdot w8 z14 = false := by decide
theorem sz_8_15 : SS.bdot w8 z15 = false := by decide
theorem sz_9_0 : SS.bdot w9 z0 = false := by decide
theorem sz_9_1 : SS.bdot w9 z1 = false := by decide
theorem sz_9_2 : SS.bdot w9 z2 = false := by decide
theorem sz_9_3 : SS.bdot w9 z3 = false := by decide
theorem sz_9_4 : SS.bdot w9 z4 = true := by decide
theorem sz_9_5 : SS.bdot w9 z5 = true := by decide
theorem sz_9_6 : SS.bdot w9 z6 = true := by decide
theorem sz_9_7 : SS.bdot w9 z7 = true := by decide
theorem sz_9_8 : SS.bdot w9 z8 = true := by decide
theorem sz_9_9 : SS.bdot w9 z9 = true := by decide
theorem sz_9_10 : SS.bdot w9 z10 = true := by decide
theorem sz_9_11 : SS.bdot w9 z11 = true := by decide
theorem sz_9_12 : SS.bdot w9 z12 = false := by decide
theorem sz_9_13 : SS.bdot w9 z13 = false := by decide
theorem sz_9_14 : SS.bdot w9 z14 = false := by decide
theorem sz_9_15 : SS.bdot w9 z15 = false := by decide

/-! ## The Walsh expansions -/

theorem exO_1_0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w0 =
      star (c y2) * d z2 + star (c y3) * d z3 + star (c y4) * d z4 + star (c y5) * d z5 + star (c y10) * d z10 + star (c y11) * d z11 + star (c y12) * d z12 + star (c y13) * d z13 := by
  unfold offSum
  rw [incO_1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fo_1_2, fo_1_3, fo_1_4, fo_1_5, fo_1_10, fo_1_11, fo_1_12, fo_1_13]
  simp only [sz_0_2, sz_0_3, sz_0_4, sz_0_5, sz_0_10, sz_0_11, sz_0_12, sz_0_13, SixQubit.signMul_false]
  try ring

theorem exO_1_6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w6 =
      star (c y2) * d z2 + star (c y3) * d z3 + star (c y4) * d z4 + star (c y5) * d z5 - star (c y10) * d z10 - star (c y11) * d z11 - star (c y12) * d z12 - star (c y13) * d z13 := by
  unfold offSum
  rw [incO_1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fo_1_2, fo_1_3, fo_1_4, fo_1_5, fo_1_10, fo_1_11, fo_1_12, fo_1_13]
  simp only [sz_6_2, sz_6_3, sz_6_4, sz_6_5, sz_6_10, sz_6_11, sz_6_12, sz_6_13, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exO_2_0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w0 =
      star (c y0) * d z0 + star (c y1) * d z1 + star (c y6) * d z6 + star (c y7) * d z7 + star (c y8) * d z8 + star (c y9) * d z9 + star (c y14) * d z14 + star (c y15) * d z15 := by
  unfold offSum
  rw [incO_2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fo_2_0, fo_2_1, fo_2_6, fo_2_7, fo_2_8, fo_2_9, fo_2_14, fo_2_15]
  simp only [sz_0_0, sz_0_1, sz_0_6, sz_0_7, sz_0_8, sz_0_9, sz_0_14, sz_0_15, SixQubit.signMul_false]
  try ring

theorem exO_2_2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w2 =
      - star (c y0) * d z0 + star (c y1) * d z1 + star (c y6) * d z6 - star (c y7) * d z7 - star (c y8) * d z8 + star (c y9) * d z9 + star (c y14) * d z14 - star (c y15) * d z15 := by
  unfold offSum
  rw [incO_2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fo_2_0, fo_2_1, fo_2_6, fo_2_7, fo_2_8, fo_2_9, fo_2_14, fo_2_15]
  simp only [sz_2_0, sz_2_1, sz_2_6, sz_2_7, sz_2_8, sz_2_9, sz_2_14, sz_2_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exO_3_0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w0 =
      star (c y1) * d z0 + star (c y0) * d z1 + star (c y7) * d z6 + star (c y6) * d z7 + star (c y9) * d z8 + star (c y8) * d z9 + star (c y15) * d z14 + star (c y14) * d z15 := by
  unfold offSum
  rw [incO_3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fo_3_0, fo_3_1, fo_3_6, fo_3_7, fo_3_8, fo_3_9, fo_3_14, fo_3_15]
  simp only [sz_0_0, sz_0_1, sz_0_6, sz_0_7, sz_0_8, sz_0_9, sz_0_14, sz_0_15, SixQubit.signMul_false]
  try ring

theorem exO_3_3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w3 =
      star (c y1) * d z0 - star (c y0) * d z1 + star (c y7) * d z6 - star (c y6) * d z7 + star (c y9) * d z8 - star (c y8) * d z9 + star (c y15) * d z14 - star (c y14) * d z15 := by
  unfold offSum
  rw [incO_3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fo_3_0, fo_3_1, fo_3_6, fo_3_7, fo_3_8, fo_3_9, fo_3_14, fo_3_15]
  simp only [sz_3_0, sz_3_1, sz_3_6, sz_3_7, sz_3_8, sz_3_9, sz_3_14, sz_3_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exO_4_0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w0 =
      star (c y0) * d z2 + star (c y1) * d z3 + star (c y4) * d z6 + star (c y5) * d z7 + star (c y8) * d z10 + star (c y9) * d z11 + star (c y12) * d z14 + star (c y13) * d z15 := by
  unfold offSum
  rw [incO_4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fo_4_2, fo_4_3, fo_4_6, fo_4_7, fo_4_10, fo_4_11, fo_4_14, fo_4_15]
  simp only [sz_0_2, sz_0_3, sz_0_6, sz_0_7, sz_0_10, sz_0_11, sz_0_14, sz_0_15, SixQubit.signMul_false]
  try ring

theorem exO_4_6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w6 =
      star (c y0) * d z2 + star (c y1) * d z3 + star (c y4) * d z6 + star (c y5) * d z7 - star (c y8) * d z10 - star (c y9) * d z11 - star (c y12) * d z14 - star (c y13) * d z15 := by
  unfold offSum
  rw [incO_4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fo_4_2, fo_4_3, fo_4_6, fo_4_7, fo_4_10, fo_4_11, fo_4_14, fo_4_15]
  simp only [sz_6_2, sz_6_3, sz_6_6, sz_6_7, sz_6_10, sz_6_11, sz_6_14, sz_6_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exO_5_0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef5 w0 =
      star (c y2) * d z0 + star (c y3) * d z1 + star (c y6) * d z4 + star (c y7) * d z5 + star (c y10) * d z8 + star (c y11) * d z9 + star (c y14) * d z12 + star (c y15) * d z13 := by
  unfold offSum
  rw [incO_5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fo_5_0, fo_5_1, fo_5_4, fo_5_5, fo_5_8, fo_5_9, fo_5_12, fo_5_13]
  simp only [sz_0_0, sz_0_1, sz_0_4, sz_0_5, sz_0_8, sz_0_9, sz_0_12, sz_0_13, SixQubit.signMul_false]
  try ring

theorem exO_5_2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef5 w2 =
      - star (c y2) * d z0 + star (c y3) * d z1 + star (c y6) * d z4 - star (c y7) * d z5 - star (c y10) * d z8 + star (c y11) * d z9 + star (c y14) * d z12 - star (c y15) * d z13 := by
  unfold offSum
  rw [incO_5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fo_5_0, fo_5_1, fo_5_4, fo_5_5, fo_5_8, fo_5_9, fo_5_12, fo_5_13]
  simp only [sz_2_0, sz_2_1, sz_2_4, sz_2_5, sz_2_8, sz_2_9, sz_2_12, sz_2_13, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exO_6_0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w0 =
      star (c y3) * d z0 + star (c y2) * d z1 + star (c y7) * d z4 + star (c y6) * d z5 + star (c y11) * d z8 + star (c y10) * d z9 + star (c y15) * d z12 + star (c y14) * d z13 := by
  unfold offSum
  rw [incO_6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fo_6_0, fo_6_1, fo_6_4, fo_6_5, fo_6_8, fo_6_9, fo_6_12, fo_6_13]
  simp only [sz_0_0, sz_0_1, sz_0_4, sz_0_5, sz_0_8, sz_0_9, sz_0_12, sz_0_13, SixQubit.signMul_false]
  try ring

theorem exO_6_3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w3 =
      star (c y3) * d z0 - star (c y2) * d z1 + star (c y7) * d z4 - star (c y6) * d z5 + star (c y11) * d z8 - star (c y10) * d z9 + star (c y15) * d z12 - star (c y14) * d z13 := by
  unfold offSum
  rw [incO_6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fo_6_0, fo_6_1, fo_6_4, fo_6_5, fo_6_8, fo_6_9, fo_6_12, fo_6_13]
  simp only [sz_3_0, sz_3_1, sz_3_4, sz_3_5, sz_3_8, sz_3_9, sz_3_12, sz_3_13, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exO_7_0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef7 w0 =
      star (c y0) * d z4 + star (c y1) * d z5 + star (c y2) * d z6 + star (c y3) * d z7 + star (c y8) * d z12 + star (c y9) * d z13 + star (c y10) * d z14 + star (c y11) * d z15 := by
  unfold offSum
  rw [incO_7]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fo_7_4, fo_7_5, fo_7_6, fo_7_7, fo_7_12, fo_7_13, fo_7_14, fo_7_15]
  simp only [sz_0_4, sz_0_5, sz_0_6, sz_0_7, sz_0_12, sz_0_13, sz_0_14, sz_0_15, SixQubit.signMul_false]
  try ring

theorem exO_7_6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef7 w6 =
      star (c y0) * d z4 + star (c y1) * d z5 + star (c y2) * d z6 + star (c y3) * d z7 - star (c y8) * d z12 - star (c y9) * d z13 - star (c y10) * d z14 - star (c y11) * d z15 := by
  unfold offSum
  rw [incO_7]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fo_7_4, fo_7_5, fo_7_6, fo_7_7, fo_7_12, fo_7_13, fo_7_14, fo_7_15]
  simp only [sz_6_4, sz_6_5, sz_6_6, sz_6_7, sz_6_12, sz_6_13, sz_6_14, sz_6_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exO_8_0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef8 w0 =
      star (c y4) * d z0 + star (c y5) * d z1 + star (c y6) * d z2 + star (c y7) * d z3 + star (c y12) * d z8 + star (c y13) * d z9 + star (c y14) * d z10 + star (c y15) * d z11 := by
  unfold offSum
  rw [incO_8]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fo_8_0, fo_8_1, fo_8_2, fo_8_3, fo_8_8, fo_8_9, fo_8_10, fo_8_11]
  simp only [sz_0_0, sz_0_1, sz_0_2, sz_0_3, sz_0_8, sz_0_9, sz_0_10, sz_0_11, SixQubit.signMul_false]
  try ring

theorem exO_8_2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef8 w2 =
      - star (c y4) * d z0 + star (c y5) * d z1 + star (c y6) * d z2 - star (c y7) * d z3 - star (c y12) * d z8 + star (c y13) * d z9 + star (c y14) * d z10 - star (c y15) * d z11 := by
  unfold offSum
  rw [incO_8]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fo_8_0, fo_8_1, fo_8_2, fo_8_3, fo_8_8, fo_8_9, fo_8_10, fo_8_11]
  simp only [sz_2_0, sz_2_1, sz_2_2, sz_2_3, sz_2_8, sz_2_9, sz_2_10, sz_2_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exO_9_0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef9 w0 =
      star (c y5) * d z0 + star (c y4) * d z1 + star (c y7) * d z2 + star (c y6) * d z3 + star (c y13) * d z8 + star (c y12) * d z9 + star (c y15) * d z10 + star (c y14) * d z11 := by
  unfold offSum
  rw [incO_9]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fo_9_0, fo_9_1, fo_9_2, fo_9_3, fo_9_8, fo_9_9, fo_9_10, fo_9_11]
  simp only [sz_0_0, sz_0_1, sz_0_2, sz_0_3, sz_0_8, sz_0_9, sz_0_10, sz_0_11, SixQubit.signMul_false]
  try ring

theorem exO_9_3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef9 w3 =
      star (c y5) * d z0 - star (c y4) * d z1 + star (c y7) * d z2 - star (c y6) * d z3 + star (c y13) * d z8 - star (c y12) * d z9 + star (c y15) * d z10 - star (c y14) * d z11 := by
  unfold offSum
  rw [incO_9]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fo_9_0, fo_9_1, fo_9_2, fo_9_3, fo_9_8, fo_9_9, fo_9_10, fo_9_11]
  simp only [sz_3_0, sz_3_1, sz_3_2, sz_3_3, sz_3_8, sz_3_9, sz_3_10, sz_3_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exO_11_0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef11 w0 =
      star (c y10) * d z2 + star (c y11) * d z3 + star (c y12) * d z4 + star (c y13) * d z5 + star (c y2) * d z10 + star (c y3) * d z11 + star (c y4) * d z12 + star (c y5) * d z13 := by
  unfold offSum
  rw [incO_11]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fo_11_2, fo_11_3, fo_11_4, fo_11_5, fo_11_10, fo_11_11, fo_11_12, fo_11_13]
  simp only [sz_0_2, sz_0_3, sz_0_4, sz_0_5, sz_0_10, sz_0_11, sz_0_12, sz_0_13, SixQubit.signMul_false]
  try ring

theorem exO_11_6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef11 w6 =
      star (c y10) * d z2 + star (c y11) * d z3 + star (c y12) * d z4 + star (c y13) * d z5 - star (c y2) * d z10 - star (c y3) * d z11 - star (c y4) * d z12 - star (c y5) * d z13 := by
  unfold offSum
  rw [incO_11]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fo_11_2, fo_11_3, fo_11_4, fo_11_5, fo_11_10, fo_11_11, fo_11_12, fo_11_13]
  simp only [sz_6_2, sz_6_3, sz_6_4, sz_6_5, sz_6_10, sz_6_11, sz_6_12, sz_6_13, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exO_12_0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef12 w0 =
      star (c y8) * d z2 + star (c y9) * d z3 + star (c y12) * d z6 + star (c y13) * d z7 + star (c y0) * d z10 + star (c y1) * d z11 + star (c y4) * d z14 + star (c y5) * d z15 := by
  unfold offSum
  rw [incO_12]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fo_12_2, fo_12_3, fo_12_6, fo_12_7, fo_12_10, fo_12_11, fo_12_14, fo_12_15]
  simp only [sz_0_2, sz_0_3, sz_0_6, sz_0_7, sz_0_10, sz_0_11, sz_0_14, sz_0_15, SixQubit.signMul_false]
  try ring

theorem exO_12_6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef12 w6 =
      star (c y8) * d z2 + star (c y9) * d z3 + star (c y12) * d z6 + star (c y13) * d z7 - star (c y0) * d z10 - star (c y1) * d z11 - star (c y4) * d z14 - star (c y5) * d z15 := by
  unfold offSum
  rw [incO_12]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fo_12_2, fo_12_3, fo_12_6, fo_12_7, fo_12_10, fo_12_11, fo_12_14, fo_12_15]
  simp only [sz_6_2, sz_6_3, sz_6_6, sz_6_7, sz_6_10, sz_6_11, sz_6_14, sz_6_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exO_13_0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef13 w0 =
      star (c y8) * d z4 + star (c y9) * d z5 + star (c y10) * d z6 + star (c y11) * d z7 + star (c y0) * d z12 + star (c y1) * d z13 + star (c y2) * d z14 + star (c y3) * d z15 := by
  unfold offSum
  rw [incO_13]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fo_13_4, fo_13_5, fo_13_6, fo_13_7, fo_13_12, fo_13_13, fo_13_14, fo_13_15]
  simp only [sz_0_4, sz_0_5, sz_0_6, sz_0_7, sz_0_12, sz_0_13, sz_0_14, sz_0_15, SixQubit.signMul_false]
  try ring

theorem exO_13_6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef13 w6 =
      star (c y8) * d z4 + star (c y9) * d z5 + star (c y10) * d z6 + star (c y11) * d z7 - star (c y0) * d z12 - star (c y1) * d z13 - star (c y2) * d z14 - star (c y3) * d z15 := by
  unfold offSum
  rw [incO_13]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fo_13_4, fo_13_5, fo_13_6, fo_13_7, fo_13_12, fo_13_13, fo_13_14, fo_13_15]
  simp only [sz_6_4, sz_6_5, sz_6_6, sz_6_7, sz_6_12, sz_6_13, sz_6_14, sz_6_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exB_0_0 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef0 w0 =
      star (c y0) * c y0 + star (c y1) * c y1 + star (c y2) * c y2 + star (c y3) * c y3 + star (c y4) * c y4 + star (c y5) * c y5 + star (c y6) * c y6 + star (c y7) * c y7 + star (c y8) * c y8 + star (c y9) * c y9 + star (c y10) * c y10 + star (c y11) * c y11 + star (c y12) * c y12 + star (c y13) * c y13 + star (c y14) * c y14 + star (c y15) * c y15 := by
  unfold diagBot
  rw [incB_0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fb_0_0, fb_0_1, fb_0_2, fb_0_3, fb_0_4, fb_0_5, fb_0_6, fb_0_7, fb_0_8, fb_0_9, fb_0_10, fb_0_11, fb_0_12, fb_0_13, fb_0_14, fb_0_15]
  simp only [sy_0_0, sy_0_1, sy_0_2, sy_0_3, sy_0_4, sy_0_5, sy_0_6, sy_0_7, sy_0_8, sy_0_9, sy_0_10, sy_0_11, sy_0_12, sy_0_13, sy_0_14, sy_0_15, SixQubit.signMul_false]
  try ring

theorem exT_0_0 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef0 w0 =
      star (d z0) * d z0 + star (d z1) * d z1 + star (d z2) * d z2 + star (d z3) * d z3 + star (d z4) * d z4 + star (d z5) * d z5 + star (d z6) * d z6 + star (d z7) * d z7 + star (d z8) * d z8 + star (d z9) * d z9 + star (d z10) * d z10 + star (d z11) * d z11 + star (d z12) * d z12 + star (d z13) * d z13 + star (d z14) * d z14 + star (d z15) * d z15 := by
  unfold diagTop
  rw [incT_0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [ft_0_0, ft_0_1, ft_0_2, ft_0_3, ft_0_4, ft_0_5, ft_0_6, ft_0_7, ft_0_8, ft_0_9, ft_0_10, ft_0_11, ft_0_12, ft_0_13, ft_0_14, ft_0_15]
  simp only [sz_0_0, sz_0_1, sz_0_2, sz_0_3, sz_0_4, sz_0_5, sz_0_6, sz_0_7, sz_0_8, sz_0_9, sz_0_10, sz_0_11, sz_0_12, sz_0_13, sz_0_14, sz_0_15, SixQubit.signMul_false]
  try ring

theorem exB_0_5 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef0 w5 =
      star (c y0) * c y0 + star (c y1) * c y1 + star (c y2) * c y2 + star (c y3) * c y3 - star (c y4) * c y4 - star (c y5) * c y5 - star (c y6) * c y6 - star (c y7) * c y7 + star (c y8) * c y8 + star (c y9) * c y9 + star (c y10) * c y10 + star (c y11) * c y11 - star (c y12) * c y12 - star (c y13) * c y13 - star (c y14) * c y14 - star (c y15) * c y15 := by
  unfold diagBot
  rw [incB_0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fb_0_0, fb_0_1, fb_0_2, fb_0_3, fb_0_4, fb_0_5, fb_0_6, fb_0_7, fb_0_8, fb_0_9, fb_0_10, fb_0_11, fb_0_12, fb_0_13, fb_0_14, fb_0_15]
  simp only [sy_5_0, sy_5_1, sy_5_2, sy_5_3, sy_5_4, sy_5_5, sy_5_6, sy_5_7, sy_5_8, sy_5_9, sy_5_10, sy_5_11, sy_5_12, sy_5_13, sy_5_14, sy_5_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exT_0_5 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef0 w5 =
      star (d z0) * d z0 + star (d z1) * d z1 + star (d z2) * d z2 + star (d z3) * d z3 - star (d z4) * d z4 - star (d z5) * d z5 - star (d z6) * d z6 - star (d z7) * d z7 + star (d z8) * d z8 + star (d z9) * d z9 + star (d z10) * d z10 + star (d z11) * d z11 - star (d z12) * d z12 - star (d z13) * d z13 - star (d z14) * d z14 - star (d z15) * d z15 := by
  unfold diagTop
  rw [incT_0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [ft_0_0, ft_0_1, ft_0_2, ft_0_3, ft_0_4, ft_0_5, ft_0_6, ft_0_7, ft_0_8, ft_0_9, ft_0_10, ft_0_11, ft_0_12, ft_0_13, ft_0_14, ft_0_15]
  simp only [sz_5_0, sz_5_1, sz_5_2, sz_5_3, sz_5_4, sz_5_5, sz_5_6, sz_5_7, sz_5_8, sz_5_9, sz_5_10, sz_5_11, sz_5_12, sz_5_13, sz_5_14, sz_5_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exB_0_4 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef0 w4 =
      star (c y0) * c y0 + star (c y1) * c y1 - star (c y2) * c y2 - star (c y3) * c y3 + star (c y4) * c y4 + star (c y5) * c y5 - star (c y6) * c y6 - star (c y7) * c y7 + star (c y8) * c y8 + star (c y9) * c y9 - star (c y10) * c y10 - star (c y11) * c y11 + star (c y12) * c y12 + star (c y13) * c y13 - star (c y14) * c y14 - star (c y15) * c y15 := by
  unfold diagBot
  rw [incB_0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fb_0_0, fb_0_1, fb_0_2, fb_0_3, fb_0_4, fb_0_5, fb_0_6, fb_0_7, fb_0_8, fb_0_9, fb_0_10, fb_0_11, fb_0_12, fb_0_13, fb_0_14, fb_0_15]
  simp only [sy_4_0, sy_4_1, sy_4_2, sy_4_3, sy_4_4, sy_4_5, sy_4_6, sy_4_7, sy_4_8, sy_4_9, sy_4_10, sy_4_11, sy_4_12, sy_4_13, sy_4_14, sy_4_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exT_0_4 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef0 w4 =
      star (d z0) * d z0 + star (d z1) * d z1 - star (d z2) * d z2 - star (d z3) * d z3 + star (d z4) * d z4 + star (d z5) * d z5 - star (d z6) * d z6 - star (d z7) * d z7 + star (d z8) * d z8 + star (d z9) * d z9 - star (d z10) * d z10 - star (d z11) * d z11 + star (d z12) * d z12 + star (d z13) * d z13 - star (d z14) * d z14 - star (d z15) * d z15 := by
  unfold diagTop
  rw [incT_0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [ft_0_0, ft_0_1, ft_0_2, ft_0_3, ft_0_4, ft_0_5, ft_0_6, ft_0_7, ft_0_8, ft_0_9, ft_0_10, ft_0_11, ft_0_12, ft_0_13, ft_0_14, ft_0_15]
  simp only [sz_4_0, sz_4_1, sz_4_2, sz_4_3, sz_4_4, sz_4_5, sz_4_6, sz_4_7, sz_4_8, sz_4_9, sz_4_10, sz_4_11, sz_4_12, sz_4_13, sz_4_14, sz_4_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exB_0_1 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef0 w1 =
      star (c y0) * c y0 + star (c y1) * c y1 - star (c y2) * c y2 - star (c y3) * c y3 - star (c y4) * c y4 - star (c y5) * c y5 + star (c y6) * c y6 + star (c y7) * c y7 + star (c y8) * c y8 + star (c y9) * c y9 - star (c y10) * c y10 - star (c y11) * c y11 - star (c y12) * c y12 - star (c y13) * c y13 + star (c y14) * c y14 + star (c y15) * c y15 := by
  unfold diagBot
  rw [incB_0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fb_0_0, fb_0_1, fb_0_2, fb_0_3, fb_0_4, fb_0_5, fb_0_6, fb_0_7, fb_0_8, fb_0_9, fb_0_10, fb_0_11, fb_0_12, fb_0_13, fb_0_14, fb_0_15]
  simp only [sy_1_0, sy_1_1, sy_1_2, sy_1_3, sy_1_4, sy_1_5, sy_1_6, sy_1_7, sy_1_8, sy_1_9, sy_1_10, sy_1_11, sy_1_12, sy_1_13, sy_1_14, sy_1_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exT_0_1 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef0 w1 =
      - star (d z0) * d z0 - star (d z1) * d z1 + star (d z2) * d z2 + star (d z3) * d z3 + star (d z4) * d z4 + star (d z5) * d z5 - star (d z6) * d z6 - star (d z7) * d z7 - star (d z8) * d z8 - star (d z9) * d z9 + star (d z10) * d z10 + star (d z11) * d z11 + star (d z12) * d z12 + star (d z13) * d z13 - star (d z14) * d z14 - star (d z15) * d z15 := by
  unfold diagTop
  rw [incT_0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [ft_0_0, ft_0_1, ft_0_2, ft_0_3, ft_0_4, ft_0_5, ft_0_6, ft_0_7, ft_0_8, ft_0_9, ft_0_10, ft_0_11, ft_0_12, ft_0_13, ft_0_14, ft_0_15]
  simp only [sz_1_0, sz_1_1, sz_1_2, sz_1_3, sz_1_4, sz_1_5, sz_1_6, sz_1_7, sz_1_8, sz_1_9, sz_1_10, sz_1_11, sz_1_12, sz_1_13, sz_1_14, sz_1_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exB_0_6 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef0 w6 =
      star (c y0) * c y0 + star (c y1) * c y1 + star (c y2) * c y2 + star (c y3) * c y3 + star (c y4) * c y4 + star (c y5) * c y5 + star (c y6) * c y6 + star (c y7) * c y7 - star (c y8) * c y8 - star (c y9) * c y9 - star (c y10) * c y10 - star (c y11) * c y11 - star (c y12) * c y12 - star (c y13) * c y13 - star (c y14) * c y14 - star (c y15) * c y15 := by
  unfold diagBot
  rw [incB_0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fb_0_0, fb_0_1, fb_0_2, fb_0_3, fb_0_4, fb_0_5, fb_0_6, fb_0_7, fb_0_8, fb_0_9, fb_0_10, fb_0_11, fb_0_12, fb_0_13, fb_0_14, fb_0_15]
  simp only [sy_6_0, sy_6_1, sy_6_2, sy_6_3, sy_6_4, sy_6_5, sy_6_6, sy_6_7, sy_6_8, sy_6_9, sy_6_10, sy_6_11, sy_6_12, sy_6_13, sy_6_14, sy_6_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exT_0_6 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef0 w6 =
      star (d z0) * d z0 + star (d z1) * d z1 + star (d z2) * d z2 + star (d z3) * d z3 + star (d z4) * d z4 + star (d z5) * d z5 + star (d z6) * d z6 + star (d z7) * d z7 - star (d z8) * d z8 - star (d z9) * d z9 - star (d z10) * d z10 - star (d z11) * d z11 - star (d z12) * d z12 - star (d z13) * d z13 - star (d z14) * d z14 - star (d z15) * d z15 := by
  unfold diagTop
  rw [incT_0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [ft_0_0, ft_0_1, ft_0_2, ft_0_3, ft_0_4, ft_0_5, ft_0_6, ft_0_7, ft_0_8, ft_0_9, ft_0_10, ft_0_11, ft_0_12, ft_0_13, ft_0_14, ft_0_15]
  simp only [sz_6_0, sz_6_1, sz_6_2, sz_6_3, sz_6_4, sz_6_5, sz_6_6, sz_6_7, sz_6_8, sz_6_9, sz_6_10, sz_6_11, sz_6_12, sz_6_13, sz_6_14, sz_6_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exB_0_9 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef0 w9 =
      star (c y0) * c y0 + star (c y1) * c y1 + star (c y2) * c y2 + star (c y3) * c y3 - star (c y4) * c y4 - star (c y5) * c y5 - star (c y6) * c y6 - star (c y7) * c y7 - star (c y8) * c y8 - star (c y9) * c y9 - star (c y10) * c y10 - star (c y11) * c y11 + star (c y12) * c y12 + star (c y13) * c y13 + star (c y14) * c y14 + star (c y15) * c y15 := by
  unfold diagBot
  rw [incB_0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fb_0_0, fb_0_1, fb_0_2, fb_0_3, fb_0_4, fb_0_5, fb_0_6, fb_0_7, fb_0_8, fb_0_9, fb_0_10, fb_0_11, fb_0_12, fb_0_13, fb_0_14, fb_0_15]
  simp only [sy_9_0, sy_9_1, sy_9_2, sy_9_3, sy_9_4, sy_9_5, sy_9_6, sy_9_7, sy_9_8, sy_9_9, sy_9_10, sy_9_11, sy_9_12, sy_9_13, sy_9_14, sy_9_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exT_0_9 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef0 w9 =
      star (d z0) * d z0 + star (d z1) * d z1 + star (d z2) * d z2 + star (d z3) * d z3 - star (d z4) * d z4 - star (d z5) * d z5 - star (d z6) * d z6 - star (d z7) * d z7 - star (d z8) * d z8 - star (d z9) * d z9 - star (d z10) * d z10 - star (d z11) * d z11 + star (d z12) * d z12 + star (d z13) * d z13 + star (d z14) * d z14 + star (d z15) * d z15 := by
  unfold diagTop
  rw [incT_0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [ft_0_0, ft_0_1, ft_0_2, ft_0_3, ft_0_4, ft_0_5, ft_0_6, ft_0_7, ft_0_8, ft_0_9, ft_0_10, ft_0_11, ft_0_12, ft_0_13, ft_0_14, ft_0_15]
  simp only [sz_9_0, sz_9_1, sz_9_2, sz_9_3, sz_9_4, sz_9_5, sz_9_6, sz_9_7, sz_9_8, sz_9_9, sz_9_10, sz_9_11, sz_9_12, sz_9_13, sz_9_14, sz_9_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exB_0_8 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef0 w8 =
      star (c y0) * c y0 + star (c y1) * c y1 - star (c y2) * c y2 - star (c y3) * c y3 + star (c y4) * c y4 + star (c y5) * c y5 - star (c y6) * c y6 - star (c y7) * c y7 - star (c y8) * c y8 - star (c y9) * c y9 + star (c y10) * c y10 + star (c y11) * c y11 - star (c y12) * c y12 - star (c y13) * c y13 + star (c y14) * c y14 + star (c y15) * c y15 := by
  unfold diagBot
  rw [incB_0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fb_0_0, fb_0_1, fb_0_2, fb_0_3, fb_0_4, fb_0_5, fb_0_6, fb_0_7, fb_0_8, fb_0_9, fb_0_10, fb_0_11, fb_0_12, fb_0_13, fb_0_14, fb_0_15]
  simp only [sy_8_0, sy_8_1, sy_8_2, sy_8_3, sy_8_4, sy_8_5, sy_8_6, sy_8_7, sy_8_8, sy_8_9, sy_8_10, sy_8_11, sy_8_12, sy_8_13, sy_8_14, sy_8_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exT_0_8 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef0 w8 =
      star (d z0) * d z0 + star (d z1) * d z1 - star (d z2) * d z2 - star (d z3) * d z3 + star (d z4) * d z4 + star (d z5) * d z5 - star (d z6) * d z6 - star (d z7) * d z7 - star (d z8) * d z8 - star (d z9) * d z9 + star (d z10) * d z10 + star (d z11) * d z11 - star (d z12) * d z12 - star (d z13) * d z13 + star (d z14) * d z14 + star (d z15) * d z15 := by
  unfold diagTop
  rw [incT_0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [ft_0_0, ft_0_1, ft_0_2, ft_0_3, ft_0_4, ft_0_5, ft_0_6, ft_0_7, ft_0_8, ft_0_9, ft_0_10, ft_0_11, ft_0_12, ft_0_13, ft_0_14, ft_0_15]
  simp only [sz_8_0, sz_8_1, sz_8_2, sz_8_3, sz_8_4, sz_8_5, sz_8_6, sz_8_7, sz_8_8, sz_8_9, sz_8_10, sz_8_11, sz_8_12, sz_8_13, sz_8_14, sz_8_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exB_0_7 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef0 w7 =
      star (c y0) * c y0 + star (c y1) * c y1 - star (c y2) * c y2 - star (c y3) * c y3 - star (c y4) * c y4 - star (c y5) * c y5 + star (c y6) * c y6 + star (c y7) * c y7 - star (c y8) * c y8 - star (c y9) * c y9 + star (c y10) * c y10 + star (c y11) * c y11 + star (c y12) * c y12 + star (c y13) * c y13 - star (c y14) * c y14 - star (c y15) * c y15 := by
  unfold diagBot
  rw [incB_0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fb_0_0, fb_0_1, fb_0_2, fb_0_3, fb_0_4, fb_0_5, fb_0_6, fb_0_7, fb_0_8, fb_0_9, fb_0_10, fb_0_11, fb_0_12, fb_0_13, fb_0_14, fb_0_15]
  simp only [sy_7_0, sy_7_1, sy_7_2, sy_7_3, sy_7_4, sy_7_5, sy_7_6, sy_7_7, sy_7_8, sy_7_9, sy_7_10, sy_7_11, sy_7_12, sy_7_13, sy_7_14, sy_7_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exT_0_7 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef0 w7 =
      - star (d z0) * d z0 - star (d z1) * d z1 + star (d z2) * d z2 + star (d z3) * d z3 + star (d z4) * d z4 + star (d z5) * d z5 - star (d z6) * d z6 - star (d z7) * d z7 + star (d z8) * d z8 + star (d z9) * d z9 - star (d z10) * d z10 - star (d z11) * d z11 - star (d z12) * d z12 - star (d z13) * d z13 + star (d z14) * d z14 + star (d z15) * d z15 := by
  unfold diagTop
  rw [incT_0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [ft_0_0, ft_0_1, ft_0_2, ft_0_3, ft_0_4, ft_0_5, ft_0_6, ft_0_7, ft_0_8, ft_0_9, ft_0_10, ft_0_11, ft_0_12, ft_0_13, ft_0_14, ft_0_15]
  simp only [sz_7_0, sz_7_1, sz_7_2, sz_7_3, sz_7_4, sz_7_5, sz_7_6, sz_7_7, sz_7_8, sz_7_9, sz_7_10, sz_7_11, sz_7_12, sz_7_13, sz_7_14, sz_7_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exB_10_0 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef10 w0 =
      star (c y8) * c y0 + star (c y9) * c y1 + star (c y10) * c y2 + star (c y11) * c y3 + star (c y12) * c y4 + star (c y13) * c y5 + star (c y14) * c y6 + star (c y15) * c y7 + star (c y0) * c y8 + star (c y1) * c y9 + star (c y2) * c y10 + star (c y3) * c y11 + star (c y4) * c y12 + star (c y5) * c y13 + star (c y6) * c y14 + star (c y7) * c y15 := by
  unfold diagBot
  rw [incB_10]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fb_10_0, fb_10_1, fb_10_2, fb_10_3, fb_10_4, fb_10_5, fb_10_6, fb_10_7, fb_10_8, fb_10_9, fb_10_10, fb_10_11, fb_10_12, fb_10_13, fb_10_14, fb_10_15]
  simp only [sy_0_0, sy_0_1, sy_0_2, sy_0_3, sy_0_4, sy_0_5, sy_0_6, sy_0_7, sy_0_8, sy_0_9, sy_0_10, sy_0_11, sy_0_12, sy_0_13, sy_0_14, sy_0_15, SixQubit.signMul_false]
  try ring

theorem exT_10_0 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef10 w0 =
      star (d z8) * d z0 + star (d z9) * d z1 + star (d z10) * d z2 + star (d z11) * d z3 + star (d z12) * d z4 + star (d z13) * d z5 + star (d z14) * d z6 + star (d z15) * d z7 + star (d z0) * d z8 + star (d z1) * d z9 + star (d z2) * d z10 + star (d z3) * d z11 + star (d z4) * d z12 + star (d z5) * d z13 + star (d z6) * d z14 + star (d z7) * d z15 := by
  unfold diagTop
  rw [incT_10]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [ft_10_0, ft_10_1, ft_10_2, ft_10_3, ft_10_4, ft_10_5, ft_10_6, ft_10_7, ft_10_8, ft_10_9, ft_10_10, ft_10_11, ft_10_12, ft_10_13, ft_10_14, ft_10_15]
  simp only [sz_0_0, sz_0_1, sz_0_2, sz_0_3, sz_0_4, sz_0_5, sz_0_6, sz_0_7, sz_0_8, sz_0_9, sz_0_10, sz_0_11, sz_0_12, sz_0_13, sz_0_14, sz_0_15, SixQubit.signMul_false]
  try ring

theorem exB_10_5 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef10 w5 =
      star (c y8) * c y0 + star (c y9) * c y1 + star (c y10) * c y2 + star (c y11) * c y3 - star (c y12) * c y4 - star (c y13) * c y5 - star (c y14) * c y6 - star (c y15) * c y7 + star (c y0) * c y8 + star (c y1) * c y9 + star (c y2) * c y10 + star (c y3) * c y11 - star (c y4) * c y12 - star (c y5) * c y13 - star (c y6) * c y14 - star (c y7) * c y15 := by
  unfold diagBot
  rw [incB_10]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fb_10_0, fb_10_1, fb_10_2, fb_10_3, fb_10_4, fb_10_5, fb_10_6, fb_10_7, fb_10_8, fb_10_9, fb_10_10, fb_10_11, fb_10_12, fb_10_13, fb_10_14, fb_10_15]
  simp only [sy_5_0, sy_5_1, sy_5_2, sy_5_3, sy_5_4, sy_5_5, sy_5_6, sy_5_7, sy_5_8, sy_5_9, sy_5_10, sy_5_11, sy_5_12, sy_5_13, sy_5_14, sy_5_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exT_10_5 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef10 w5 =
      star (d z8) * d z0 + star (d z9) * d z1 + star (d z10) * d z2 + star (d z11) * d z3 - star (d z12) * d z4 - star (d z13) * d z5 - star (d z14) * d z6 - star (d z15) * d z7 + star (d z0) * d z8 + star (d z1) * d z9 + star (d z2) * d z10 + star (d z3) * d z11 - star (d z4) * d z12 - star (d z5) * d z13 - star (d z6) * d z14 - star (d z7) * d z15 := by
  unfold diagTop
  rw [incT_10]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [ft_10_0, ft_10_1, ft_10_2, ft_10_3, ft_10_4, ft_10_5, ft_10_6, ft_10_7, ft_10_8, ft_10_9, ft_10_10, ft_10_11, ft_10_12, ft_10_13, ft_10_14, ft_10_15]
  simp only [sz_5_0, sz_5_1, sz_5_2, sz_5_3, sz_5_4, sz_5_5, sz_5_6, sz_5_7, sz_5_8, sz_5_9, sz_5_10, sz_5_11, sz_5_12, sz_5_13, sz_5_14, sz_5_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exB_10_4 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef10 w4 =
      star (c y8) * c y0 + star (c y9) * c y1 - star (c y10) * c y2 - star (c y11) * c y3 + star (c y12) * c y4 + star (c y13) * c y5 - star (c y14) * c y6 - star (c y15) * c y7 + star (c y0) * c y8 + star (c y1) * c y9 - star (c y2) * c y10 - star (c y3) * c y11 + star (c y4) * c y12 + star (c y5) * c y13 - star (c y6) * c y14 - star (c y7) * c y15 := by
  unfold diagBot
  rw [incB_10]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fb_10_0, fb_10_1, fb_10_2, fb_10_3, fb_10_4, fb_10_5, fb_10_6, fb_10_7, fb_10_8, fb_10_9, fb_10_10, fb_10_11, fb_10_12, fb_10_13, fb_10_14, fb_10_15]
  simp only [sy_4_0, sy_4_1, sy_4_2, sy_4_3, sy_4_4, sy_4_5, sy_4_6, sy_4_7, sy_4_8, sy_4_9, sy_4_10, sy_4_11, sy_4_12, sy_4_13, sy_4_14, sy_4_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exT_10_4 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef10 w4 =
      star (d z8) * d z0 + star (d z9) * d z1 - star (d z10) * d z2 - star (d z11) * d z3 + star (d z12) * d z4 + star (d z13) * d z5 - star (d z14) * d z6 - star (d z15) * d z7 + star (d z0) * d z8 + star (d z1) * d z9 - star (d z2) * d z10 - star (d z3) * d z11 + star (d z4) * d z12 + star (d z5) * d z13 - star (d z6) * d z14 - star (d z7) * d z15 := by
  unfold diagTop
  rw [incT_10]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [ft_10_0, ft_10_1, ft_10_2, ft_10_3, ft_10_4, ft_10_5, ft_10_6, ft_10_7, ft_10_8, ft_10_9, ft_10_10, ft_10_11, ft_10_12, ft_10_13, ft_10_14, ft_10_15]
  simp only [sz_4_0, sz_4_1, sz_4_2, sz_4_3, sz_4_4, sz_4_5, sz_4_6, sz_4_7, sz_4_8, sz_4_9, sz_4_10, sz_4_11, sz_4_12, sz_4_13, sz_4_14, sz_4_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exB_10_1 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef10 w1 =
      star (c y8) * c y0 + star (c y9) * c y1 - star (c y10) * c y2 - star (c y11) * c y3 - star (c y12) * c y4 - star (c y13) * c y5 + star (c y14) * c y6 + star (c y15) * c y7 + star (c y0) * c y8 + star (c y1) * c y9 - star (c y2) * c y10 - star (c y3) * c y11 - star (c y4) * c y12 - star (c y5) * c y13 + star (c y6) * c y14 + star (c y7) * c y15 := by
  unfold diagBot
  rw [incB_10]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fb_10_0, fb_10_1, fb_10_2, fb_10_3, fb_10_4, fb_10_5, fb_10_6, fb_10_7, fb_10_8, fb_10_9, fb_10_10, fb_10_11, fb_10_12, fb_10_13, fb_10_14, fb_10_15]
  simp only [sy_1_0, sy_1_1, sy_1_2, sy_1_3, sy_1_4, sy_1_5, sy_1_6, sy_1_7, sy_1_8, sy_1_9, sy_1_10, sy_1_11, sy_1_12, sy_1_13, sy_1_14, sy_1_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exT_10_1 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef10 w1 =
      - star (d z8) * d z0 - star (d z9) * d z1 + star (d z10) * d z2 + star (d z11) * d z3 + star (d z12) * d z4 + star (d z13) * d z5 - star (d z14) * d z6 - star (d z15) * d z7 - star (d z0) * d z8 - star (d z1) * d z9 + star (d z2) * d z10 + star (d z3) * d z11 + star (d z4) * d z12 + star (d z5) * d z13 - star (d z6) * d z14 - star (d z7) * d z15 := by
  unfold diagTop
  rw [incT_10]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [ft_10_0, ft_10_1, ft_10_2, ft_10_3, ft_10_4, ft_10_5, ft_10_6, ft_10_7, ft_10_8, ft_10_9, ft_10_10, ft_10_11, ft_10_12, ft_10_13, ft_10_14, ft_10_15]
  simp only [sz_1_0, sz_1_1, sz_1_2, sz_1_3, sz_1_4, sz_1_5, sz_1_6, sz_1_7, sz_1_8, sz_1_9, sz_1_10, sz_1_11, sz_1_12, sz_1_13, sz_1_14, sz_1_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exB_10_6 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef10 w6 =
      star (c y8) * c y0 + star (c y9) * c y1 + star (c y10) * c y2 + star (c y11) * c y3 + star (c y12) * c y4 + star (c y13) * c y5 + star (c y14) * c y6 + star (c y15) * c y7 - star (c y0) * c y8 - star (c y1) * c y9 - star (c y2) * c y10 - star (c y3) * c y11 - star (c y4) * c y12 - star (c y5) * c y13 - star (c y6) * c y14 - star (c y7) * c y15 := by
  unfold diagBot
  rw [incB_10]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fb_10_0, fb_10_1, fb_10_2, fb_10_3, fb_10_4, fb_10_5, fb_10_6, fb_10_7, fb_10_8, fb_10_9, fb_10_10, fb_10_11, fb_10_12, fb_10_13, fb_10_14, fb_10_15]
  simp only [sy_6_0, sy_6_1, sy_6_2, sy_6_3, sy_6_4, sy_6_5, sy_6_6, sy_6_7, sy_6_8, sy_6_9, sy_6_10, sy_6_11, sy_6_12, sy_6_13, sy_6_14, sy_6_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exT_10_6 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef10 w6 =
      star (d z8) * d z0 + star (d z9) * d z1 + star (d z10) * d z2 + star (d z11) * d z3 + star (d z12) * d z4 + star (d z13) * d z5 + star (d z14) * d z6 + star (d z15) * d z7 - star (d z0) * d z8 - star (d z1) * d z9 - star (d z2) * d z10 - star (d z3) * d z11 - star (d z4) * d z12 - star (d z5) * d z13 - star (d z6) * d z14 - star (d z7) * d z15 := by
  unfold diagTop
  rw [incT_10]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [ft_10_0, ft_10_1, ft_10_2, ft_10_3, ft_10_4, ft_10_5, ft_10_6, ft_10_7, ft_10_8, ft_10_9, ft_10_10, ft_10_11, ft_10_12, ft_10_13, ft_10_14, ft_10_15]
  simp only [sz_6_0, sz_6_1, sz_6_2, sz_6_3, sz_6_4, sz_6_5, sz_6_6, sz_6_7, sz_6_8, sz_6_9, sz_6_10, sz_6_11, sz_6_12, sz_6_13, sz_6_14, sz_6_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exB_10_9 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef10 w9 =
      star (c y8) * c y0 + star (c y9) * c y1 + star (c y10) * c y2 + star (c y11) * c y3 - star (c y12) * c y4 - star (c y13) * c y5 - star (c y14) * c y6 - star (c y15) * c y7 - star (c y0) * c y8 - star (c y1) * c y9 - star (c y2) * c y10 - star (c y3) * c y11 + star (c y4) * c y12 + star (c y5) * c y13 + star (c y6) * c y14 + star (c y7) * c y15 := by
  unfold diagBot
  rw [incB_10]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fb_10_0, fb_10_1, fb_10_2, fb_10_3, fb_10_4, fb_10_5, fb_10_6, fb_10_7, fb_10_8, fb_10_9, fb_10_10, fb_10_11, fb_10_12, fb_10_13, fb_10_14, fb_10_15]
  simp only [sy_9_0, sy_9_1, sy_9_2, sy_9_3, sy_9_4, sy_9_5, sy_9_6, sy_9_7, sy_9_8, sy_9_9, sy_9_10, sy_9_11, sy_9_12, sy_9_13, sy_9_14, sy_9_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exT_10_9 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef10 w9 =
      star (d z8) * d z0 + star (d z9) * d z1 + star (d z10) * d z2 + star (d z11) * d z3 - star (d z12) * d z4 - star (d z13) * d z5 - star (d z14) * d z6 - star (d z15) * d z7 - star (d z0) * d z8 - star (d z1) * d z9 - star (d z2) * d z10 - star (d z3) * d z11 + star (d z4) * d z12 + star (d z5) * d z13 + star (d z6) * d z14 + star (d z7) * d z15 := by
  unfold diagTop
  rw [incT_10]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [ft_10_0, ft_10_1, ft_10_2, ft_10_3, ft_10_4, ft_10_5, ft_10_6, ft_10_7, ft_10_8, ft_10_9, ft_10_10, ft_10_11, ft_10_12, ft_10_13, ft_10_14, ft_10_15]
  simp only [sz_9_0, sz_9_1, sz_9_2, sz_9_3, sz_9_4, sz_9_5, sz_9_6, sz_9_7, sz_9_8, sz_9_9, sz_9_10, sz_9_11, sz_9_12, sz_9_13, sz_9_14, sz_9_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exB_10_8 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef10 w8 =
      star (c y8) * c y0 + star (c y9) * c y1 - star (c y10) * c y2 - star (c y11) * c y3 + star (c y12) * c y4 + star (c y13) * c y5 - star (c y14) * c y6 - star (c y15) * c y7 - star (c y0) * c y8 - star (c y1) * c y9 + star (c y2) * c y10 + star (c y3) * c y11 - star (c y4) * c y12 - star (c y5) * c y13 + star (c y6) * c y14 + star (c y7) * c y15 := by
  unfold diagBot
  rw [incB_10]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fb_10_0, fb_10_1, fb_10_2, fb_10_3, fb_10_4, fb_10_5, fb_10_6, fb_10_7, fb_10_8, fb_10_9, fb_10_10, fb_10_11, fb_10_12, fb_10_13, fb_10_14, fb_10_15]
  simp only [sy_8_0, sy_8_1, sy_8_2, sy_8_3, sy_8_4, sy_8_5, sy_8_6, sy_8_7, sy_8_8, sy_8_9, sy_8_10, sy_8_11, sy_8_12, sy_8_13, sy_8_14, sy_8_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exT_10_8 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef10 w8 =
      star (d z8) * d z0 + star (d z9) * d z1 - star (d z10) * d z2 - star (d z11) * d z3 + star (d z12) * d z4 + star (d z13) * d z5 - star (d z14) * d z6 - star (d z15) * d z7 - star (d z0) * d z8 - star (d z1) * d z9 + star (d z2) * d z10 + star (d z3) * d z11 - star (d z4) * d z12 - star (d z5) * d z13 + star (d z6) * d z14 + star (d z7) * d z15 := by
  unfold diagTop
  rw [incT_10]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [ft_10_0, ft_10_1, ft_10_2, ft_10_3, ft_10_4, ft_10_5, ft_10_6, ft_10_7, ft_10_8, ft_10_9, ft_10_10, ft_10_11, ft_10_12, ft_10_13, ft_10_14, ft_10_15]
  simp only [sz_8_0, sz_8_1, sz_8_2, sz_8_3, sz_8_4, sz_8_5, sz_8_6, sz_8_7, sz_8_8, sz_8_9, sz_8_10, sz_8_11, sz_8_12, sz_8_13, sz_8_14, sz_8_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exB_10_7 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef10 w7 =
      star (c y8) * c y0 + star (c y9) * c y1 - star (c y10) * c y2 - star (c y11) * c y3 - star (c y12) * c y4 - star (c y13) * c y5 + star (c y14) * c y6 + star (c y15) * c y7 - star (c y0) * c y8 - star (c y1) * c y9 + star (c y2) * c y10 + star (c y3) * c y11 + star (c y4) * c y12 + star (c y5) * c y13 - star (c y6) * c y14 - star (c y7) * c y15 := by
  unfold diagBot
  rw [incB_10]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fb_10_0, fb_10_1, fb_10_2, fb_10_3, fb_10_4, fb_10_5, fb_10_6, fb_10_7, fb_10_8, fb_10_9, fb_10_10, fb_10_11, fb_10_12, fb_10_13, fb_10_14, fb_10_15]
  simp only [sy_7_0, sy_7_1, sy_7_2, sy_7_3, sy_7_4, sy_7_5, sy_7_6, sy_7_7, sy_7_8, sy_7_9, sy_7_10, sy_7_11, sy_7_12, sy_7_13, sy_7_14, sy_7_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem exT_10_7 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef10 w7 =
      - star (d z8) * d z0 - star (d z9) * d z1 + star (d z10) * d z2 + star (d z11) * d z3 + star (d z12) * d z4 + star (d z13) * d z5 - star (d z14) * d z6 - star (d z15) * d z7 + star (d z0) * d z8 + star (d z1) * d z9 - star (d z2) * d z10 - star (d z3) * d z11 - star (d z4) * d z12 - star (d z5) * d z13 + star (d z6) * d z14 + star (d z7) * d z15 := by
  unfold diagTop
  rw [incT_10]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [ft_10_0, ft_10_1, ft_10_2, ft_10_3, ft_10_4, ft_10_5, ft_10_6, ft_10_7, ft_10_8, ft_10_9, ft_10_10, ft_10_11, ft_10_12, ft_10_13, ft_10_14, ft_10_15]
  simp only [sz_7_0, sz_7_1, sz_7_2, sz_7_3, sz_7_4, sz_7_5, sz_7_6, sz_7_7, sz_7_8, sz_7_9, sz_7_10, sz_7_11, sz_7_12, sz_7_13, sz_7_14, sz_7_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

/-! ## The outer identities -/

/-- For a pair `(g, h)` of non-anchor groups and each of the four matrix
entries, `sum_c C_{2g+c}^† D_{2h+1-c} + sum_c C_{2h+c}^† D_{2g+1-c} = 0`. -/
theorem outer_g0h1_a0b0 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef7 w0 = 0) (h1 : offSum c d ef7 w6 = 0) :
    star (c y0) * d z4 + star (c y1) * d z5 + star (c y2) * d z6 + star (c y3) * d z7 = 0 := by
  rw [exO_7_0 c d] at h0
  rw [exO_7_6 c d] at h1
  linear_combination (1/2) * h0 + (1/2) * h1

theorem outer_g0h1_a0b1 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef13 w0 = 0) (h1 : offSum c d ef13 w6 = 0) :
    star (c y0) * d z12 + star (c y1) * d z13 + star (c y2) * d z14 + star (c y3) * d z15 = 0 := by
  rw [exO_13_0 c d] at h0
  rw [exO_13_6 c d] at h1
  linear_combination (1/2) * h0 + (-1/2) * h1

theorem outer_g0h1_a1b0 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef13 w0 = 0) (h1 : offSum c d ef13 w6 = 0) :
    star (c y8) * d z4 + star (c y9) * d z5 + star (c y10) * d z6 + star (c y11) * d z7 = 0 := by
  rw [exO_13_0 c d] at h0
  rw [exO_13_6 c d] at h1
  linear_combination (1/2) * h0 + (1/2) * h1

theorem outer_g0h1_a1b1 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef7 w0 = 0) (h1 : offSum c d ef7 w6 = 0) :
    star (c y8) * d z12 + star (c y9) * d z13 + star (c y10) * d z14 + star (c y11) * d z15 = 0 := by
  rw [exO_7_0 c d] at h0
  rw [exO_7_6 c d] at h1
  linear_combination (1/2) * h0 + (-1/2) * h1

theorem outer_g0h2_a0b0 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef4 w0 = 0) (h1 : offSum c d ef4 w6 = 0) :
    star (c y0) * d z2 + star (c y1) * d z3 + star (c y4) * d z6 + star (c y5) * d z7 = 0 := by
  rw [exO_4_0 c d] at h0
  rw [exO_4_6 c d] at h1
  linear_combination (1/2) * h0 + (1/2) * h1

theorem outer_g0h2_a0b1 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef12 w0 = 0) (h1 : offSum c d ef12 w6 = 0) :
    star (c y0) * d z10 + star (c y1) * d z11 + star (c y4) * d z14 + star (c y5) * d z15 = 0 := by
  rw [exO_12_0 c d] at h0
  rw [exO_12_6 c d] at h1
  linear_combination (1/2) * h0 + (-1/2) * h1

theorem outer_g0h2_a1b0 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef12 w0 = 0) (h1 : offSum c d ef12 w6 = 0) :
    star (c y8) * d z2 + star (c y9) * d z3 + star (c y12) * d z6 + star (c y13) * d z7 = 0 := by
  rw [exO_12_0 c d] at h0
  rw [exO_12_6 c d] at h1
  linear_combination (1/2) * h0 + (1/2) * h1

theorem outer_g0h2_a1b1 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef4 w0 = 0) (h1 : offSum c d ef4 w6 = 0) :
    star (c y8) * d z10 + star (c y9) * d z11 + star (c y12) * d z14 + star (c y13) * d z15 = 0 := by
  rw [exO_4_0 c d] at h0
  rw [exO_4_6 c d] at h1
  linear_combination (1/2) * h0 + (-1/2) * h1

theorem outer_g1h2_a0b0 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef1 w0 = 0) (h1 : offSum c d ef1 w6 = 0) :
    star (c y2) * d z2 + star (c y3) * d z3 + star (c y4) * d z4 + star (c y5) * d z5 = 0 := by
  rw [exO_1_0 c d] at h0
  rw [exO_1_6 c d] at h1
  linear_combination (1/2) * h0 + (1/2) * h1

theorem outer_g1h2_a0b1 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef11 w0 = 0) (h1 : offSum c d ef11 w6 = 0) :
    star (c y2) * d z10 + star (c y3) * d z11 + star (c y4) * d z12 + star (c y5) * d z13 = 0 := by
  rw [exO_11_0 c d] at h0
  rw [exO_11_6 c d] at h1
  linear_combination (1/2) * h0 + (-1/2) * h1

theorem outer_g1h2_a1b0 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef11 w0 = 0) (h1 : offSum c d ef11 w6 = 0) :
    star (c y10) * d z2 + star (c y11) * d z3 + star (c y12) * d z4 + star (c y13) * d z5 = 0 := by
  rw [exO_11_0 c d] at h0
  rw [exO_11_6 c d] at h1
  linear_combination (1/2) * h0 + (1/2) * h1

theorem outer_g1h2_a1b1 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef1 w0 = 0) (h1 : offSum c d ef1 w6 = 0) :
    star (c y10) * d z10 + star (c y11) * d z11 + star (c y12) * d z12 + star (c y13) * d z13 = 0 := by
  rw [exO_1_0 c d] at h0
  rw [exO_1_6 c d] at h1
  linear_combination (1/2) * h0 + (-1/2) * h1

/-! ## The anchor scalars -/

/-- For a non-anchor block `i` and an anchor `j`,
`ip C_i D_j + ip C_j D_i = 0`. -/
theorem anch_i0_j6 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef3 w0 = 0) (h1 : offSum c d ef3 w3 = 0) :
    star (c y0) * d z1 + star (c y8) * d z9 + star (c y6) * d z7 + star (c y14) * d z15 = 0 := by
  rw [exO_3_0 c d] at h0
  rw [exO_3_3 c d] at h1
  linear_combination (1/2) * h0 + (-1/2) * h1

theorem anch_i0_j7 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef2 w0 = 0) (h1 : offSum c d ef2 w2 = 0) :
    star (c y0) * d z0 + star (c y8) * d z8 + star (c y7) * d z7 + star (c y15) * d z15 = 0 := by
  rw [exO_2_0 c d] at h0
  rw [exO_2_2 c d] at h1
  linear_combination (1/2) * h0 + (-1/2) * h1

theorem anch_i1_j6 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef2 w0 = 0) (h1 : offSum c d ef2 w2 = 0) :
    star (c y1) * d z1 + star (c y9) * d z9 + star (c y6) * d z6 + star (c y14) * d z14 = 0 := by
  rw [exO_2_0 c d] at h0
  rw [exO_2_2 c d] at h1
  linear_combination (1/2) * h0 + (1/2) * h1

theorem anch_i1_j7 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef3 w0 = 0) (h1 : offSum c d ef3 w3 = 0) :
    star (c y1) * d z0 + star (c y9) * d z8 + star (c y7) * d z6 + star (c y15) * d z14 = 0 := by
  rw [exO_3_0 c d] at h0
  rw [exO_3_3 c d] at h1
  linear_combination (1/2) * h0 + (1/2) * h1

theorem anch_i2_j6 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef6 w0 = 0) (h1 : offSum c d ef6 w3 = 0) :
    star (c y2) * d z1 + star (c y10) * d z9 + star (c y6) * d z5 + star (c y14) * d z13 = 0 := by
  rw [exO_6_0 c d] at h0
  rw [exO_6_3 c d] at h1
  linear_combination (1/2) * h0 + (-1/2) * h1

theorem anch_i2_j7 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef5 w0 = 0) (h1 : offSum c d ef5 w2 = 0) :
    star (c y2) * d z0 + star (c y10) * d z8 + star (c y7) * d z5 + star (c y15) * d z13 = 0 := by
  rw [exO_5_0 c d] at h0
  rw [exO_5_2 c d] at h1
  linear_combination (1/2) * h0 + (-1/2) * h1

theorem anch_i3_j6 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef5 w0 = 0) (h1 : offSum c d ef5 w2 = 0) :
    star (c y3) * d z1 + star (c y11) * d z9 + star (c y6) * d z4 + star (c y14) * d z12 = 0 := by
  rw [exO_5_0 c d] at h0
  rw [exO_5_2 c d] at h1
  linear_combination (1/2) * h0 + (1/2) * h1

theorem anch_i3_j7 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef6 w0 = 0) (h1 : offSum c d ef6 w3 = 0) :
    star (c y3) * d z0 + star (c y11) * d z8 + star (c y7) * d z4 + star (c y15) * d z12 = 0 := by
  rw [exO_6_0 c d] at h0
  rw [exO_6_3 c d] at h1
  linear_combination (1/2) * h0 + (1/2) * h1

theorem anch_i4_j6 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef9 w0 = 0) (h1 : offSum c d ef9 w3 = 0) :
    star (c y4) * d z1 + star (c y12) * d z9 + star (c y6) * d z3 + star (c y14) * d z11 = 0 := by
  rw [exO_9_0 c d] at h0
  rw [exO_9_3 c d] at h1
  linear_combination (1/2) * h0 + (-1/2) * h1

theorem anch_i4_j7 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef8 w0 = 0) (h1 : offSum c d ef8 w2 = 0) :
    star (c y4) * d z0 + star (c y12) * d z8 + star (c y7) * d z3 + star (c y15) * d z11 = 0 := by
  rw [exO_8_0 c d] at h0
  rw [exO_8_2 c d] at h1
  linear_combination (1/2) * h0 + (-1/2) * h1

theorem anch_i5_j6 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef8 w0 = 0) (h1 : offSum c d ef8 w2 = 0) :
    star (c y5) * d z1 + star (c y13) * d z9 + star (c y6) * d z2 + star (c y14) * d z10 = 0 := by
  rw [exO_8_0 c d] at h0
  rw [exO_8_2 c d] at h1
  linear_combination (1/2) * h0 + (1/2) * h1

theorem anch_i5_j7 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef9 w0 = 0) (h1 : offSum c d ef9 w3 = 0) :
    star (c y5) * d z0 + star (c y13) * d z8 + star (c y7) * d z2 + star (c y15) * d z10 = 0 := by
  rw [exO_9_0 c d] at h0
  rw [exO_9_3 c d] at h1
  linear_combination (1/2) * h0 + (1/2) * h1

/-! ## The matrix moment identity -/

/-! `C_g C_g^† + D_g D_g^† = ρ/2` with `ρ = sum_g C_g C_g^†`, per group and
per matrix entry. -/

set_option maxHeartbeats 2000000 in
theorem mom_g0_a0b0 (c d : SS.BitString 6 -> ℂ)
    (D0 : diagBot c ef0 w0 = diagTop d ef0 w0)
    (D1 : diagBot c ef0 w5 = diagTop d ef0 w5)
    (D2 : diagBot c ef0 w4 = diagTop d ef0 w4)
    (D3 : diagBot c ef0 w1 = diagTop d ef0 w1)
    (D4 : diagBot c ef0 w6 = diagTop d ef0 w6)
    (D5 : diagBot c ef0 w9 = diagTop d ef0 w9)
    (D6 : diagBot c ef0 w8 = diagTop d ef0 w8)
    (D7 : diagBot c ef0 w7 = diagTop d ef0 w7)
    : c y0 * star (c y0) + d z7 * star (d z7) + c y1 * star (c y1) + d z6 * star (d z6)
      = 1/2 * (c y0 * star (c y0) + c y1 * star (c y1) + c y2 * star (c y2) + c y3 * star (c y3) + c y4 * star (c y4) + c y5 * star (c y5) + c y6 * star (c y6) + c y7 * star (c y7)) := by
  rw [exB_0_0 c, exT_0_0 d] at D0
  rw [exB_0_5 c, exT_0_5 d] at D1
  rw [exB_0_4 c, exT_0_4 d] at D2
  rw [exB_0_1 c, exT_0_1 d] at D3
  rw [exB_0_6 c, exT_0_6 d] at D4
  rw [exB_0_9 c, exT_0_9 d] at D5
  rw [exB_0_8 c, exT_0_8 d] at D6
  rw [exB_0_7 c, exT_0_7 d] at D7
  linear_combination (-1/8) * D0 + (1/8) * D1 + (1/8) * D2 + (1/8) * D3 + (-1/8) * D4 + (1/8) * D5 + (1/8) * D6 + (1/8) * D7

set_option maxHeartbeats 2000000 in
theorem mom_g0_a0b1 (c d : SS.BitString 6 -> ℂ)
    (D0 : diagBot c ef10 w0 = diagTop d ef10 w0)
    (D1 : diagBot c ef10 w5 = diagTop d ef10 w5)
    (D2 : diagBot c ef10 w4 = diagTop d ef10 w4)
    (D3 : diagBot c ef10 w1 = diagTop d ef10 w1)
    (D4 : diagBot c ef10 w6 = diagTop d ef10 w6)
    (D5 : diagBot c ef10 w9 = diagTop d ef10 w9)
    (D6 : diagBot c ef10 w8 = diagTop d ef10 w8)
    (D7 : diagBot c ef10 w7 = diagTop d ef10 w7)
    : c y0 * star (c y8) + d z7 * star (d z15) + c y1 * star (c y9) + d z6 * star (d z14)
      = 1/2 * (c y0 * star (c y8) + c y1 * star (c y9) + c y2 * star (c y10) + c y3 * star (c y11) + c y4 * star (c y12) + c y5 * star (c y13) + c y6 * star (c y14) + c y7 * star (c y15)) := by
  rw [exB_10_0 c, exT_10_0 d] at D0
  rw [exB_10_5 c, exT_10_5 d] at D1
  rw [exB_10_4 c, exT_10_4 d] at D2
  rw [exB_10_1 c, exT_10_1 d] at D3
  rw [exB_10_6 c, exT_10_6 d] at D4
  rw [exB_10_9 c, exT_10_9 d] at D5
  rw [exB_10_8 c, exT_10_8 d] at D6
  rw [exB_10_7 c, exT_10_7 d] at D7
  linear_combination (-1/8) * D0 + (1/8) * D1 + (1/8) * D2 + (1/8) * D3 + (-1/8) * D4 + (1/8) * D5 + (1/8) * D6 + (1/8) * D7

set_option maxHeartbeats 2000000 in
theorem mom_g0_a1b0 (c d : SS.BitString 6 -> ℂ)
    (D0 : diagBot c ef10 w0 = diagTop d ef10 w0)
    (D1 : diagBot c ef10 w5 = diagTop d ef10 w5)
    (D2 : diagBot c ef10 w4 = diagTop d ef10 w4)
    (D3 : diagBot c ef10 w1 = diagTop d ef10 w1)
    (D4 : diagBot c ef10 w6 = diagTop d ef10 w6)
    (D5 : diagBot c ef10 w9 = diagTop d ef10 w9)
    (D6 : diagBot c ef10 w8 = diagTop d ef10 w8)
    (D7 : diagBot c ef10 w7 = diagTop d ef10 w7)
    : c y8 * star (c y0) + d z15 * star (d z7) + c y9 * star (c y1) + d z14 * star (d z6)
      = 1/2 * (c y8 * star (c y0) + c y9 * star (c y1) + c y10 * star (c y2) + c y11 * star (c y3) + c y12 * star (c y4) + c y13 * star (c y5) + c y14 * star (c y6) + c y15 * star (c y7)) := by
  rw [exB_10_0 c, exT_10_0 d] at D0
  rw [exB_10_5 c, exT_10_5 d] at D1
  rw [exB_10_4 c, exT_10_4 d] at D2
  rw [exB_10_1 c, exT_10_1 d] at D3
  rw [exB_10_6 c, exT_10_6 d] at D4
  rw [exB_10_9 c, exT_10_9 d] at D5
  rw [exB_10_8 c, exT_10_8 d] at D6
  rw [exB_10_7 c, exT_10_7 d] at D7
  linear_combination (-1/8) * D0 + (1/8) * D1 + (1/8) * D2 + (1/8) * D3 + (1/8) * D4 + (-1/8) * D5 + (-1/8) * D6 + (-1/8) * D7

set_option maxHeartbeats 2000000 in
theorem mom_g0_a1b1 (c d : SS.BitString 6 -> ℂ)
    (D0 : diagBot c ef0 w0 = diagTop d ef0 w0)
    (D1 : diagBot c ef0 w5 = diagTop d ef0 w5)
    (D2 : diagBot c ef0 w4 = diagTop d ef0 w4)
    (D3 : diagBot c ef0 w1 = diagTop d ef0 w1)
    (D4 : diagBot c ef0 w6 = diagTop d ef0 w6)
    (D5 : diagBot c ef0 w9 = diagTop d ef0 w9)
    (D6 : diagBot c ef0 w8 = diagTop d ef0 w8)
    (D7 : diagBot c ef0 w7 = diagTop d ef0 w7)
    : c y8 * star (c y8) + d z15 * star (d z15) + c y9 * star (c y9) + d z14 * star (d z14)
      = 1/2 * (c y8 * star (c y8) + c y9 * star (c y9) + c y10 * star (c y10) + c y11 * star (c y11) + c y12 * star (c y12) + c y13 * star (c y13) + c y14 * star (c y14) + c y15 * star (c y15)) := by
  rw [exB_0_0 c, exT_0_0 d] at D0
  rw [exB_0_5 c, exT_0_5 d] at D1
  rw [exB_0_4 c, exT_0_4 d] at D2
  rw [exB_0_1 c, exT_0_1 d] at D3
  rw [exB_0_6 c, exT_0_6 d] at D4
  rw [exB_0_9 c, exT_0_9 d] at D5
  rw [exB_0_8 c, exT_0_8 d] at D6
  rw [exB_0_7 c, exT_0_7 d] at D7
  linear_combination (-1/8) * D0 + (1/8) * D1 + (1/8) * D2 + (1/8) * D3 + (1/8) * D4 + (-1/8) * D5 + (-1/8) * D6 + (-1/8) * D7

set_option maxHeartbeats 2000000 in
theorem mom_g1_a0b0 (c d : SS.BitString 6 -> ℂ)
    (D0 : diagBot c ef0 w0 = diagTop d ef0 w0)
    (D1 : diagBot c ef0 w5 = diagTop d ef0 w5)
    (D2 : diagBot c ef0 w4 = diagTop d ef0 w4)
    (D3 : diagBot c ef0 w1 = diagTop d ef0 w1)
    (D4 : diagBot c ef0 w6 = diagTop d ef0 w6)
    (D5 : diagBot c ef0 w9 = diagTop d ef0 w9)
    (D6 : diagBot c ef0 w8 = diagTop d ef0 w8)
    (D7 : diagBot c ef0 w7 = diagTop d ef0 w7)
    : c y2 * star (c y2) + d z5 * star (d z5) + c y3 * star (c y3) + d z4 * star (d z4)
      = 1/2 * (c y0 * star (c y0) + c y1 * star (c y1) + c y2 * star (c y2) + c y3 * star (c y3) + c y4 * star (c y4) + c y5 * star (c y5) + c y6 * star (c y6) + c y7 * star (c y7)) := by
  rw [exB_0_0 c, exT_0_0 d] at D0
  rw [exB_0_5 c, exT_0_5 d] at D1
  rw [exB_0_4 c, exT_0_4 d] at D2
  rw [exB_0_1 c, exT_0_1 d] at D3
  rw [exB_0_6 c, exT_0_6 d] at D4
  rw [exB_0_9 c, exT_0_9 d] at D5
  rw [exB_0_8 c, exT_0_8 d] at D6
  rw [exB_0_7 c, exT_0_7 d] at D7
  linear_combination (-1/8) * D0 + (1/8) * D1 + (-1/8) * D2 + (-1/8) * D3 + (-1/8) * D4 + (1/8) * D5 + (-1/8) * D6 + (-1/8) * D7

set_option maxHeartbeats 2000000 in
theorem mom_g1_a0b1 (c d : SS.BitString 6 -> ℂ)
    (D0 : diagBot c ef10 w0 = diagTop d ef10 w0)
    (D1 : diagBot c ef10 w5 = diagTop d ef10 w5)
    (D2 : diagBot c ef10 w4 = diagTop d ef10 w4)
    (D3 : diagBot c ef10 w1 = diagTop d ef10 w1)
    (D4 : diagBot c ef10 w6 = diagTop d ef10 w6)
    (D5 : diagBot c ef10 w9 = diagTop d ef10 w9)
    (D6 : diagBot c ef10 w8 = diagTop d ef10 w8)
    (D7 : diagBot c ef10 w7 = diagTop d ef10 w7)
    : c y2 * star (c y10) + d z5 * star (d z13) + c y3 * star (c y11) + d z4 * star (d z12)
      = 1/2 * (c y0 * star (c y8) + c y1 * star (c y9) + c y2 * star (c y10) + c y3 * star (c y11) + c y4 * star (c y12) + c y5 * star (c y13) + c y6 * star (c y14) + c y7 * star (c y15)) := by
  rw [exB_10_0 c, exT_10_0 d] at D0
  rw [exB_10_5 c, exT_10_5 d] at D1
  rw [exB_10_4 c, exT_10_4 d] at D2
  rw [exB_10_1 c, exT_10_1 d] at D3
  rw [exB_10_6 c, exT_10_6 d] at D4
  rw [exB_10_9 c, exT_10_9 d] at D5
  rw [exB_10_8 c, exT_10_8 d] at D6
  rw [exB_10_7 c, exT_10_7 d] at D7
  linear_combination (-1/8) * D0 + (1/8) * D1 + (-1/8) * D2 + (-1/8) * D3 + (-1/8) * D4 + (1/8) * D5 + (-1/8) * D6 + (-1/8) * D7

set_option maxHeartbeats 2000000 in
theorem mom_g1_a1b0 (c d : SS.BitString 6 -> ℂ)
    (D0 : diagBot c ef10 w0 = diagTop d ef10 w0)
    (D1 : diagBot c ef10 w5 = diagTop d ef10 w5)
    (D2 : diagBot c ef10 w4 = diagTop d ef10 w4)
    (D3 : diagBot c ef10 w1 = diagTop d ef10 w1)
    (D4 : diagBot c ef10 w6 = diagTop d ef10 w6)
    (D5 : diagBot c ef10 w9 = diagTop d ef10 w9)
    (D6 : diagBot c ef10 w8 = diagTop d ef10 w8)
    (D7 : diagBot c ef10 w7 = diagTop d ef10 w7)
    : c y10 * star (c y2) + d z13 * star (d z5) + c y11 * star (c y3) + d z12 * star (d z4)
      = 1/2 * (c y8 * star (c y0) + c y9 * star (c y1) + c y10 * star (c y2) + c y11 * star (c y3) + c y12 * star (c y4) + c y13 * star (c y5) + c y14 * star (c y6) + c y15 * star (c y7)) := by
  rw [exB_10_0 c, exT_10_0 d] at D0
  rw [exB_10_5 c, exT_10_5 d] at D1
  rw [exB_10_4 c, exT_10_4 d] at D2
  rw [exB_10_1 c, exT_10_1 d] at D3
  rw [exB_10_6 c, exT_10_6 d] at D4
  rw [exB_10_9 c, exT_10_9 d] at D5
  rw [exB_10_8 c, exT_10_8 d] at D6
  rw [exB_10_7 c, exT_10_7 d] at D7
  linear_combination (-1/8) * D0 + (1/8) * D1 + (-1/8) * D2 + (-1/8) * D3 + (1/8) * D4 + (-1/8) * D5 + (1/8) * D6 + (1/8) * D7

set_option maxHeartbeats 2000000 in
theorem mom_g1_a1b1 (c d : SS.BitString 6 -> ℂ)
    (D0 : diagBot c ef0 w0 = diagTop d ef0 w0)
    (D1 : diagBot c ef0 w5 = diagTop d ef0 w5)
    (D2 : diagBot c ef0 w4 = diagTop d ef0 w4)
    (D3 : diagBot c ef0 w1 = diagTop d ef0 w1)
    (D4 : diagBot c ef0 w6 = diagTop d ef0 w6)
    (D5 : diagBot c ef0 w9 = diagTop d ef0 w9)
    (D6 : diagBot c ef0 w8 = diagTop d ef0 w8)
    (D7 : diagBot c ef0 w7 = diagTop d ef0 w7)
    : c y10 * star (c y10) + d z13 * star (d z13) + c y11 * star (c y11) + d z12 * star (d z12)
      = 1/2 * (c y8 * star (c y8) + c y9 * star (c y9) + c y10 * star (c y10) + c y11 * star (c y11) + c y12 * star (c y12) + c y13 * star (c y13) + c y14 * star (c y14) + c y15 * star (c y15)) := by
  rw [exB_0_0 c, exT_0_0 d] at D0
  rw [exB_0_5 c, exT_0_5 d] at D1
  rw [exB_0_4 c, exT_0_4 d] at D2
  rw [exB_0_1 c, exT_0_1 d] at D3
  rw [exB_0_6 c, exT_0_6 d] at D4
  rw [exB_0_9 c, exT_0_9 d] at D5
  rw [exB_0_8 c, exT_0_8 d] at D6
  rw [exB_0_7 c, exT_0_7 d] at D7
  linear_combination (-1/8) * D0 + (1/8) * D1 + (-1/8) * D2 + (-1/8) * D3 + (1/8) * D4 + (-1/8) * D5 + (1/8) * D6 + (1/8) * D7

set_option maxHeartbeats 2000000 in
theorem mom_g2_a0b0 (c d : SS.BitString 6 -> ℂ)
    (D0 : diagBot c ef0 w0 = diagTop d ef0 w0)
    (D1 : diagBot c ef0 w5 = diagTop d ef0 w5)
    (D2 : diagBot c ef0 w4 = diagTop d ef0 w4)
    (D3 : diagBot c ef0 w1 = diagTop d ef0 w1)
    (D4 : diagBot c ef0 w6 = diagTop d ef0 w6)
    (D5 : diagBot c ef0 w9 = diagTop d ef0 w9)
    (D6 : diagBot c ef0 w8 = diagTop d ef0 w8)
    (D7 : diagBot c ef0 w7 = diagTop d ef0 w7)
    : c y4 * star (c y4) + d z3 * star (d z3) + c y5 * star (c y5) + d z2 * star (d z2)
      = 1/2 * (c y0 * star (c y0) + c y1 * star (c y1) + c y2 * star (c y2) + c y3 * star (c y3) + c y4 * star (c y4) + c y5 * star (c y5) + c y6 * star (c y6) + c y7 * star (c y7)) := by
  rw [exB_0_0 c, exT_0_0 d] at D0
  rw [exB_0_5 c, exT_0_5 d] at D1
  rw [exB_0_4 c, exT_0_4 d] at D2
  rw [exB_0_1 c, exT_0_1 d] at D3
  rw [exB_0_6 c, exT_0_6 d] at D4
  rw [exB_0_9 c, exT_0_9 d] at D5
  rw [exB_0_8 c, exT_0_8 d] at D6
  rw [exB_0_7 c, exT_0_7 d] at D7
  linear_combination (-1/8) * D0 + (-1/8) * D1 + (1/8) * D2 + (-1/8) * D3 + (-1/8) * D4 + (-1/8) * D5 + (1/8) * D6 + (-1/8) * D7

set_option maxHeartbeats 2000000 in
theorem mom_g2_a0b1 (c d : SS.BitString 6 -> ℂ)
    (D0 : diagBot c ef10 w0 = diagTop d ef10 w0)
    (D1 : diagBot c ef10 w5 = diagTop d ef10 w5)
    (D2 : diagBot c ef10 w4 = diagTop d ef10 w4)
    (D3 : diagBot c ef10 w1 = diagTop d ef10 w1)
    (D4 : diagBot c ef10 w6 = diagTop d ef10 w6)
    (D5 : diagBot c ef10 w9 = diagTop d ef10 w9)
    (D6 : diagBot c ef10 w8 = diagTop d ef10 w8)
    (D7 : diagBot c ef10 w7 = diagTop d ef10 w7)
    : c y4 * star (c y12) + d z3 * star (d z11) + c y5 * star (c y13) + d z2 * star (d z10)
      = 1/2 * (c y0 * star (c y8) + c y1 * star (c y9) + c y2 * star (c y10) + c y3 * star (c y11) + c y4 * star (c y12) + c y5 * star (c y13) + c y6 * star (c y14) + c y7 * star (c y15)) := by
  rw [exB_10_0 c, exT_10_0 d] at D0
  rw [exB_10_5 c, exT_10_5 d] at D1
  rw [exB_10_4 c, exT_10_4 d] at D2
  rw [exB_10_1 c, exT_10_1 d] at D3
  rw [exB_10_6 c, exT_10_6 d] at D4
  rw [exB_10_9 c, exT_10_9 d] at D5
  rw [exB_10_8 c, exT_10_8 d] at D6
  rw [exB_10_7 c, exT_10_7 d] at D7
  linear_combination (-1/8) * D0 + (-1/8) * D1 + (1/8) * D2 + (-1/8) * D3 + (-1/8) * D4 + (-1/8) * D5 + (1/8) * D6 + (-1/8) * D7

set_option maxHeartbeats 2000000 in
theorem mom_g2_a1b0 (c d : SS.BitString 6 -> ℂ)
    (D0 : diagBot c ef10 w0 = diagTop d ef10 w0)
    (D1 : diagBot c ef10 w5 = diagTop d ef10 w5)
    (D2 : diagBot c ef10 w4 = diagTop d ef10 w4)
    (D3 : diagBot c ef10 w1 = diagTop d ef10 w1)
    (D4 : diagBot c ef10 w6 = diagTop d ef10 w6)
    (D5 : diagBot c ef10 w9 = diagTop d ef10 w9)
    (D6 : diagBot c ef10 w8 = diagTop d ef10 w8)
    (D7 : diagBot c ef10 w7 = diagTop d ef10 w7)
    : c y12 * star (c y4) + d z11 * star (d z3) + c y13 * star (c y5) + d z10 * star (d z2)
      = 1/2 * (c y8 * star (c y0) + c y9 * star (c y1) + c y10 * star (c y2) + c y11 * star (c y3) + c y12 * star (c y4) + c y13 * star (c y5) + c y14 * star (c y6) + c y15 * star (c y7)) := by
  rw [exB_10_0 c, exT_10_0 d] at D0
  rw [exB_10_5 c, exT_10_5 d] at D1
  rw [exB_10_4 c, exT_10_4 d] at D2
  rw [exB_10_1 c, exT_10_1 d] at D3
  rw [exB_10_6 c, exT_10_6 d] at D4
  rw [exB_10_9 c, exT_10_9 d] at D5
  rw [exB_10_8 c, exT_10_8 d] at D6
  rw [exB_10_7 c, exT_10_7 d] at D7
  linear_combination (-1/8) * D0 + (-1/8) * D1 + (1/8) * D2 + (-1/8) * D3 + (1/8) * D4 + (1/8) * D5 + (-1/8) * D6 + (1/8) * D7

set_option maxHeartbeats 2000000 in
theorem mom_g2_a1b1 (c d : SS.BitString 6 -> ℂ)
    (D0 : diagBot c ef0 w0 = diagTop d ef0 w0)
    (D1 : diagBot c ef0 w5 = diagTop d ef0 w5)
    (D2 : diagBot c ef0 w4 = diagTop d ef0 w4)
    (D3 : diagBot c ef0 w1 = diagTop d ef0 w1)
    (D4 : diagBot c ef0 w6 = diagTop d ef0 w6)
    (D5 : diagBot c ef0 w9 = diagTop d ef0 w9)
    (D6 : diagBot c ef0 w8 = diagTop d ef0 w8)
    (D7 : diagBot c ef0 w7 = diagTop d ef0 w7)
    : c y12 * star (c y12) + d z11 * star (d z11) + c y13 * star (c y13) + d z10 * star (d z10)
      = 1/2 * (c y8 * star (c y8) + c y9 * star (c y9) + c y10 * star (c y10) + c y11 * star (c y11) + c y12 * star (c y12) + c y13 * star (c y13) + c y14 * star (c y14) + c y15 * star (c y15)) := by
  rw [exB_0_0 c, exT_0_0 d] at D0
  rw [exB_0_5 c, exT_0_5 d] at D1
  rw [exB_0_4 c, exT_0_4 d] at D2
  rw [exB_0_1 c, exT_0_1 d] at D3
  rw [exB_0_6 c, exT_0_6 d] at D4
  rw [exB_0_9 c, exT_0_9 d] at D5
  rw [exB_0_8 c, exT_0_8 d] at D6
  rw [exB_0_7 c, exT_0_7 d] at D7
  linear_combination (-1/8) * D0 + (-1/8) * D1 + (1/8) * D2 + (-1/8) * D3 + (1/8) * D4 + (1/8) * D5 + (-1/8) * D6 + (1/8) * D7

set_option maxHeartbeats 2000000 in
theorem mom_g3_a0b0 (c d : SS.BitString 6 -> ℂ)
    (D0 : diagBot c ef0 w0 = diagTop d ef0 w0)
    (D1 : diagBot c ef0 w5 = diagTop d ef0 w5)
    (D2 : diagBot c ef0 w4 = diagTop d ef0 w4)
    (D3 : diagBot c ef0 w1 = diagTop d ef0 w1)
    (D4 : diagBot c ef0 w6 = diagTop d ef0 w6)
    (D5 : diagBot c ef0 w9 = diagTop d ef0 w9)
    (D6 : diagBot c ef0 w8 = diagTop d ef0 w8)
    (D7 : diagBot c ef0 w7 = diagTop d ef0 w7)
    : c y6 * star (c y6) + d z1 * star (d z1) + c y7 * star (c y7) + d z0 * star (d z0)
      = 1/2 * (c y0 * star (c y0) + c y1 * star (c y1) + c y2 * star (c y2) + c y3 * star (c y3) + c y4 * star (c y4) + c y5 * star (c y5) + c y6 * star (c y6) + c y7 * star (c y7)) := by
  rw [exB_0_0 c, exT_0_0 d] at D0
  rw [exB_0_5 c, exT_0_5 d] at D1
  rw [exB_0_4 c, exT_0_4 d] at D2
  rw [exB_0_1 c, exT_0_1 d] at D3
  rw [exB_0_6 c, exT_0_6 d] at D4
  rw [exB_0_9 c, exT_0_9 d] at D5
  rw [exB_0_8 c, exT_0_8 d] at D6
  rw [exB_0_7 c, exT_0_7 d] at D7
  linear_combination (-1/8) * D0 + (-1/8) * D1 + (-1/8) * D2 + (1/8) * D3 + (-1/8) * D4 + (-1/8) * D5 + (-1/8) * D6 + (1/8) * D7

set_option maxHeartbeats 2000000 in
theorem mom_g3_a0b1 (c d : SS.BitString 6 -> ℂ)
    (D0 : diagBot c ef10 w0 = diagTop d ef10 w0)
    (D1 : diagBot c ef10 w5 = diagTop d ef10 w5)
    (D2 : diagBot c ef10 w4 = diagTop d ef10 w4)
    (D3 : diagBot c ef10 w1 = diagTop d ef10 w1)
    (D4 : diagBot c ef10 w6 = diagTop d ef10 w6)
    (D5 : diagBot c ef10 w9 = diagTop d ef10 w9)
    (D6 : diagBot c ef10 w8 = diagTop d ef10 w8)
    (D7 : diagBot c ef10 w7 = diagTop d ef10 w7)
    : c y6 * star (c y14) + d z1 * star (d z9) + c y7 * star (c y15) + d z0 * star (d z8)
      = 1/2 * (c y0 * star (c y8) + c y1 * star (c y9) + c y2 * star (c y10) + c y3 * star (c y11) + c y4 * star (c y12) + c y5 * star (c y13) + c y6 * star (c y14) + c y7 * star (c y15)) := by
  rw [exB_10_0 c, exT_10_0 d] at D0
  rw [exB_10_5 c, exT_10_5 d] at D1
  rw [exB_10_4 c, exT_10_4 d] at D2
  rw [exB_10_1 c, exT_10_1 d] at D3
  rw [exB_10_6 c, exT_10_6 d] at D4
  rw [exB_10_9 c, exT_10_9 d] at D5
  rw [exB_10_8 c, exT_10_8 d] at D6
  rw [exB_10_7 c, exT_10_7 d] at D7
  linear_combination (-1/8) * D0 + (-1/8) * D1 + (-1/8) * D2 + (1/8) * D3 + (-1/8) * D4 + (-1/8) * D5 + (-1/8) * D6 + (1/8) * D7

set_option maxHeartbeats 2000000 in
theorem mom_g3_a1b0 (c d : SS.BitString 6 -> ℂ)
    (D0 : diagBot c ef10 w0 = diagTop d ef10 w0)
    (D1 : diagBot c ef10 w5 = diagTop d ef10 w5)
    (D2 : diagBot c ef10 w4 = diagTop d ef10 w4)
    (D3 : diagBot c ef10 w1 = diagTop d ef10 w1)
    (D4 : diagBot c ef10 w6 = diagTop d ef10 w6)
    (D5 : diagBot c ef10 w9 = diagTop d ef10 w9)
    (D6 : diagBot c ef10 w8 = diagTop d ef10 w8)
    (D7 : diagBot c ef10 w7 = diagTop d ef10 w7)
    : c y14 * star (c y6) + d z9 * star (d z1) + c y15 * star (c y7) + d z8 * star (d z0)
      = 1/2 * (c y8 * star (c y0) + c y9 * star (c y1) + c y10 * star (c y2) + c y11 * star (c y3) + c y12 * star (c y4) + c y13 * star (c y5) + c y14 * star (c y6) + c y15 * star (c y7)) := by
  rw [exB_10_0 c, exT_10_0 d] at D0
  rw [exB_10_5 c, exT_10_5 d] at D1
  rw [exB_10_4 c, exT_10_4 d] at D2
  rw [exB_10_1 c, exT_10_1 d] at D3
  rw [exB_10_6 c, exT_10_6 d] at D4
  rw [exB_10_9 c, exT_10_9 d] at D5
  rw [exB_10_8 c, exT_10_8 d] at D6
  rw [exB_10_7 c, exT_10_7 d] at D7
  linear_combination (-1/8) * D0 + (-1/8) * D1 + (-1/8) * D2 + (1/8) * D3 + (1/8) * D4 + (1/8) * D5 + (1/8) * D6 + (-1/8) * D7

set_option maxHeartbeats 2000000 in
theorem mom_g3_a1b1 (c d : SS.BitString 6 -> ℂ)
    (D0 : diagBot c ef0 w0 = diagTop d ef0 w0)
    (D1 : diagBot c ef0 w5 = diagTop d ef0 w5)
    (D2 : diagBot c ef0 w4 = diagTop d ef0 w4)
    (D3 : diagBot c ef0 w1 = diagTop d ef0 w1)
    (D4 : diagBot c ef0 w6 = diagTop d ef0 w6)
    (D5 : diagBot c ef0 w9 = diagTop d ef0 w9)
    (D6 : diagBot c ef0 w8 = diagTop d ef0 w8)
    (D7 : diagBot c ef0 w7 = diagTop d ef0 w7)
    : c y14 * star (c y14) + d z9 * star (d z9) + c y15 * star (c y15) + d z8 * star (d z8)
      = 1/2 * (c y8 * star (c y8) + c y9 * star (c y9) + c y10 * star (c y10) + c y11 * star (c y11) + c y12 * star (c y12) + c y13 * star (c y13) + c y14 * star (c y14) + c y15 * star (c y15)) := by
  rw [exB_0_0 c, exT_0_0 d] at D0
  rw [exB_0_5 c, exT_0_5 d] at D1
  rw [exB_0_4 c, exT_0_4 d] at D2
  rw [exB_0_1 c, exT_0_1 d] at D3
  rw [exB_0_6 c, exT_0_6 d] at D4
  rw [exB_0_9 c, exT_0_9 d] at D5
  rw [exB_0_8 c, exT_0_8 d] at D6
  rw [exB_0_7 c, exT_0_7 d] at D7
  linear_combination (-1/8) * D0 + (-1/8) * D1 + (-1/8) * D2 + (1/8) * D3 + (1/8) * D4 + (1/8) * D5 + (1/8) * D6 + (-1/8) * D7

/-! ## Assembly

The transcribed relations are fed to the block algebra of `SixQubit.Block26`
and the moment facts, and the result is a contradiction.  The frame used
throughout is the orthogonal pair `(D_6, D_6^\perp)` inside `C^2`.
-/

open SixQubit.Block26

/-- The rank-one quadratic form, expanded on components. -/
theorem quad (v1 v2 x1 x2 : ℂ) :
    ((Complex.normSq (ip v1 v2 x1 x2) : ℝ) : ℂ)
      = star v1 * v1 * (x1 * star x1) + star v1 * v2 * (x1 * star x2)
        + star v2 * v1 * (x2 * star x1) + star v2 * v2 * (x2 * star x2) := by
  rw [← sq (ip v1 v2 x1 x2), ip_eq]
  simp only [star_add, star_mul', star_star]
  ring

/-- The pairing against the orthogonal complement of `(m1, m2)`. -/
theorem ipw (m1 m2 v1 v2 : ℂ) :
    ip (-star m2) (star m1) v1 v2 = m1 * v2 - m2 * v1 := by
  rw [ip_eq]; simp only [star_neg, star_star]; ring

set_option maxHeartbeats 1000000 in
/-- A group moment identity, sandwiched with an arbitrary vector `(v1, v2)`. -/
theorem sandwich (v1 v2 g1 g2 g3 g4 h1 h2 h3 h4 : ℂ)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : ℂ)
    (M00 : g1 * star g1 + h1 * star h1 + g3 * star g3 + h3 * star h3
      = 1/2 * (a0 * star a0 + a1 * star a1 + a2 * star a2 + a3 * star a3
        + a4 * star a4 + a5 * star a5 + a6 * star a6 + a7 * star a7))
    (M01 : g1 * star g2 + h1 * star h2 + g3 * star g4 + h3 * star h4
      = 1/2 * (a0 * star b0 + a1 * star b1 + a2 * star b2 + a3 * star b3
        + a4 * star b4 + a5 * star b5 + a6 * star b6 + a7 * star b7))
    (M10 : g2 * star g1 + h2 * star h1 + g4 * star g3 + h4 * star h3
      = 1/2 * (b0 * star a0 + b1 * star a1 + b2 * star a2 + b3 * star a3
        + b4 * star a4 + b5 * star a5 + b6 * star a6 + b7 * star a7))
    (M11 : g2 * star g2 + h2 * star h2 + g4 * star g4 + h4 * star h4
      = 1/2 * (b0 * star b0 + b1 * star b1 + b2 * star b2 + b3 * star b3
        + b4 * star b4 + b5 * star b5 + b6 * star b6 + b7 * star b7)) :
    Complex.normSq (ip v1 v2 g1 g2) + Complex.normSq (ip v1 v2 h1 h2)
        + Complex.normSq (ip v1 v2 g3 g4) + Complex.normSq (ip v1 v2 h3 h4)
      = 1/2 * (Complex.normSq (ip v1 v2 a0 b0) + Complex.normSq (ip v1 v2 a1 b1)
        + Complex.normSq (ip v1 v2 a2 b2) + Complex.normSq (ip v1 v2 a3 b3)
        + Complex.normSq (ip v1 v2 a4 b4) + Complex.normSq (ip v1 v2 a5 b5)
        + Complex.normSq (ip v1 v2 a6 b6) + Complex.normSq (ip v1 v2 a7 b7)) := by
  have key : ((Complex.normSq (ip v1 v2 g1 g2) + Complex.normSq (ip v1 v2 h1 h2)
        + Complex.normSq (ip v1 v2 g3 g4) + Complex.normSq (ip v1 v2 h3 h4) : ℝ) : ℂ)
      = ((1/2 * (Complex.normSq (ip v1 v2 a0 b0) + Complex.normSq (ip v1 v2 a1 b1)
        + Complex.normSq (ip v1 v2 a2 b2) + Complex.normSq (ip v1 v2 a3 b3)
        + Complex.normSq (ip v1 v2 a4 b4) + Complex.normSq (ip v1 v2 a5 b5)
        + Complex.normSq (ip v1 v2 a6 b6) + Complex.normSq (ip v1 v2 a7 b7)) : ℝ) : ℂ) := by
    push_cast
    rw [quad v1 v2 g1 g2, quad v1 v2 h1 h2, quad v1 v2 g3 g4, quad v1 v2 h3 h4,
      quad v1 v2 a0 b0, quad v1 v2 a1 b1, quad v1 v2 a2 b2, quad v1 v2 a3 b3,
      quad v1 v2 a4 b4, quad v1 v2 a5 b5, quad v1 v2 a6 b6, quad v1 v2 a7 b7]
    linear_combination (star v1 * v1) * M00 + (star v1 * v2) * M01
      + (star v2 * v1) * M10 + (star v2 * v2) * M11
  exact_mod_cast key

set_option maxHeartbeats 4000000 in
/-- **The orbit 26 no-go, at the level of the moment system.**  There is no
assignment of amplitudes to the two fibers satisfying the moment system, the
twenty-four off-diagonal Knill-Laflamme conditions and the sixteen diagonal
ones listed below. -/
theorem core (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 p0 p1 p2 p3 p4 p5 p6 p7 q0 q1 q2 q3 q4 q5 q6 q7 : ℂ)
    (hPQ0 : Complex.normSq a0 + Complex.normSq b0 = Complex.normSq p0 + Complex.normSq q0)
    (hPQ1 : Complex.normSq a1 + Complex.normSq b1 = Complex.normSq p1 + Complex.normSq q1)
    (hPQ2 : Complex.normSq a2 + Complex.normSq b2 = Complex.normSq p2 + Complex.normSq q2)
    (hPQ3 : Complex.normSq a3 + Complex.normSq b3 = Complex.normSq p3 + Complex.normSq q3)
    (hPQ4 : Complex.normSq a4 + Complex.normSq b4 = Complex.normSq p4 + Complex.normSq q4)
    (hPQ5 : Complex.normSq a5 + Complex.normSq b5 = Complex.normSq p5 + Complex.normSq q5)
    (hPQ6 : Complex.normSq a6 + Complex.normSq b6 = Complex.normSq p6 + Complex.normSq q6)
    (hPQ7 : Complex.normSq a7 + Complex.normSq b7 = Complex.normSq p7 + Complex.normSq q7)
    (hP6 : Complex.normSq a6 + Complex.normSq b6 = 1/8)
    (hP7 : Complex.normSq a7 + Complex.normSq b7 = 1/8)
    (hT0 : Complex.normSq a0 + Complex.normSq b0 + (Complex.normSq a1 + Complex.normSq b1) = 1/4)
    (hT1 : Complex.normSq a2 + Complex.normSq b2 + (Complex.normSq a3 + Complex.normSq b3) = 1/4)
    (hT2 : Complex.normSq a4 + Complex.normSq b4 + (Complex.normSq a5 + Complex.normSq b5) = 1/4)
    (hT2a : Complex.normSq a0 + Complex.normSq b0 + (Complex.normSq a2 + Complex.normSq b2) + (Complex.normSq a4 + Complex.normSq b4) = 3/8)
    (hT2b : Complex.normSq a1 + Complex.normSq b1 + (Complex.normSq a3 + Complex.normSq b3) + (Complex.normSq a5 + Complex.normSq b5) = 3/8)
    (O01_11 : star a0 * p3 + star a1 * p2 + star a2 * p1 + star a3 * p0 = 0)
    (O01_12 : star a0 * q3 + star a1 * q2 + star a2 * q1 + star a3 * q0 = 0)
    (O01_21 : star b0 * p3 + star b1 * p2 + star b2 * p1 + star b3 * p0 = 0)
    (O01_22 : star b0 * q3 + star b1 * q2 + star b2 * q1 + star b3 * q0 = 0)
    (O02_11 : star a0 * p5 + star a1 * p4 + star a4 * p1 + star a5 * p0 = 0)
    (O02_12 : star a0 * q5 + star a1 * q4 + star a4 * q1 + star a5 * q0 = 0)
    (O02_21 : star b0 * p5 + star b1 * p4 + star b4 * p1 + star b5 * p0 = 0)
    (O02_22 : star b0 * q5 + star b1 * q4 + star b4 * q1 + star b5 * q0 = 0)
    (O12_11 : star a2 * p5 + star a3 * p4 + star a4 * p3 + star a5 * p2 = 0)
    (O12_12 : star a2 * q5 + star a3 * q4 + star a4 * q3 + star a5 * q2 = 0)
    (O12_21 : star b2 * p5 + star b3 * p4 + star b4 * p3 + star b5 * p2 = 0)
    (O12_22 : star b2 * q5 + star b3 * q4 + star b4 * q3 + star b5 * q2 = 0)
    (An0_6 : ip a0 b0 p6 q6 + ip a6 b6 p0 q0 = 0)
    (An0_7 : ip a0 b0 p7 q7 + ip a7 b7 p0 q0 = 0)
    (An1_6 : ip a1 b1 p6 q6 + ip a6 b6 p1 q1 = 0)
    (An1_7 : ip a1 b1 p7 q7 + ip a7 b7 p1 q1 = 0)
    (An2_6 : ip a2 b2 p6 q6 + ip a6 b6 p2 q2 = 0)
    (An2_7 : ip a2 b2 p7 q7 + ip a7 b7 p2 q2 = 0)
    (An3_6 : ip a3 b3 p6 q6 + ip a6 b6 p3 q3 = 0)
    (An3_7 : ip a3 b3 p7 q7 + ip a7 b7 p3 q3 = 0)
    (An4_6 : ip a4 b4 p6 q6 + ip a6 b6 p4 q4 = 0)
    (An4_7 : ip a4 b4 p7 q7 + ip a7 b7 p4 q4 = 0)
    (An5_6 : ip a5 b5 p6 q6 + ip a6 b6 p5 q5 = 0)
    (An5_7 : ip a5 b5 p7 q7 + ip a7 b7 p5 q5 = 0)
    (M0_11 : a0 * star a0 + p0 * star p0 + a1 * star a1 + p1 * star p1
      = 1/2 * (a0 * star a0 + a1 * star a1 + a2 * star a2 + a3 * star a3 + a4 * star a4 + a5 * star a5 + a6 * star a6 + a7 * star a7))
    (M0_12 : a0 * star b0 + p0 * star q0 + a1 * star b1 + p1 * star q1
      = 1/2 * (a0 * star b0 + a1 * star b1 + a2 * star b2 + a3 * star b3 + a4 * star b4 + a5 * star b5 + a6 * star b6 + a7 * star b7))
    (M0_21 : b0 * star a0 + q0 * star p0 + b1 * star a1 + q1 * star p1
      = 1/2 * (b0 * star a0 + b1 * star a1 + b2 * star a2 + b3 * star a3 + b4 * star a4 + b5 * star a5 + b6 * star a6 + b7 * star a7))
    (M0_22 : b0 * star b0 + q0 * star q0 + b1 * star b1 + q1 * star q1
      = 1/2 * (b0 * star b0 + b1 * star b1 + b2 * star b2 + b3 * star b3 + b4 * star b4 + b5 * star b5 + b6 * star b6 + b7 * star b7))
    (M1_11 : a2 * star a2 + p2 * star p2 + a3 * star a3 + p3 * star p3
      = 1/2 * (a0 * star a0 + a1 * star a1 + a2 * star a2 + a3 * star a3 + a4 * star a4 + a5 * star a5 + a6 * star a6 + a7 * star a7))
    (M1_12 : a2 * star b2 + p2 * star q2 + a3 * star b3 + p3 * star q3
      = 1/2 * (a0 * star b0 + a1 * star b1 + a2 * star b2 + a3 * star b3 + a4 * star b4 + a5 * star b5 + a6 * star b6 + a7 * star b7))
    (M1_21 : b2 * star a2 + q2 * star p2 + b3 * star a3 + q3 * star p3
      = 1/2 * (b0 * star a0 + b1 * star a1 + b2 * star a2 + b3 * star a3 + b4 * star a4 + b5 * star a5 + b6 * star a6 + b7 * star a7))
    (M1_22 : b2 * star b2 + q2 * star q2 + b3 * star b3 + q3 * star q3
      = 1/2 * (b0 * star b0 + b1 * star b1 + b2 * star b2 + b3 * star b3 + b4 * star b4 + b5 * star b5 + b6 * star b6 + b7 * star b7))
    (M2_11 : a4 * star a4 + p4 * star p4 + a5 * star a5 + p5 * star p5
      = 1/2 * (a0 * star a0 + a1 * star a1 + a2 * star a2 + a3 * star a3 + a4 * star a4 + a5 * star a5 + a6 * star a6 + a7 * star a7))
    (M2_12 : a4 * star b4 + p4 * star q4 + a5 * star b5 + p5 * star q5
      = 1/2 * (a0 * star b0 + a1 * star b1 + a2 * star b2 + a3 * star b3 + a4 * star b4 + a5 * star b5 + a6 * star b6 + a7 * star b7))
    (M2_21 : b4 * star a4 + q4 * star p4 + b5 * star a5 + q5 * star p5
      = 1/2 * (b0 * star a0 + b1 * star a1 + b2 * star a2 + b3 * star a3 + b4 * star a4 + b5 * star a5 + b6 * star a6 + b7 * star a7))
    (M2_22 : b4 * star b4 + q4 * star q4 + b5 * star b5 + q5 * star q5
      = 1/2 * (b0 * star b0 + b1 * star b1 + b2 * star b2 + b3 * star b3 + b4 * star b4 + b5 * star b5 + b6 * star b6 + b7 * star b7))
    (M3_11 : a6 * star a6 + p6 * star p6 + a7 * star a7 + p7 * star p7
      = 1/2 * (a0 * star a0 + a1 * star a1 + a2 * star a2 + a3 * star a3 + a4 * star a4 + a5 * star a5 + a6 * star a6 + a7 * star a7))
    (M3_12 : a6 * star b6 + p6 * star q6 + a7 * star b7 + p7 * star q7
      = 1/2 * (a0 * star b0 + a1 * star b1 + a2 * star b2 + a3 * star b3 + a4 * star b4 + a5 * star b5 + a6 * star b6 + a7 * star b7))
    (M3_21 : b6 * star a6 + q6 * star p6 + b7 * star a7 + q7 * star p7
      = 1/2 * (b0 * star a0 + b1 * star a1 + b2 * star a2 + b3 * star a3 + b4 * star a4 + b5 * star a5 + b6 * star a6 + b7 * star a7))
    (M3_22 : b6 * star b6 + q6 * star q6 + b7 * star b7 + q7 * star q7
      = 1/2 * (b0 * star b0 + b1 * star b1 + b2 * star b2 + b3 * star b3 + b4 * star b4 + b5 * star b5 + b6 * star b6 + b7 * star b7))
    : False := by
  -- the two anchor top blocks have squared norm 1/8
  have hQ6 : Complex.normSq p6 + Complex.normSq q6 = 1/8 := by linarith only [hPQ6, hP6]
  have hQ7 : Complex.normSq p7 + Complex.normSq q7 = 1/8 := by linarith only [hPQ7, hP7]
  -- Parseval in the frame determined by the first anchor
  have parC0 : Complex.normSq (ip p6 q6 a0 b0) + Complex.normSq (ip (-star q6) (star p6) a0 b0) = 1/8 * (Complex.normSq a0 + Complex.normSq b0) := by
    have h := lagrange p6 q6 a0 b0
    rw [ipw]
    rw [hQ6] at h
    linarith only [h, hQ6]
  have parD0 : Complex.normSq (ip p6 q6 p0 q0) + Complex.normSq (ip (-star q6) (star p6) p0 q0) = 1/8 * (Complex.normSq p0 + Complex.normSq q0) := by
    have h := lagrange p6 q6 p0 q0
    rw [ipw]
    rw [hQ6] at h
    linarith only [h, hQ6]
  have parC1 : Complex.normSq (ip p6 q6 a1 b1) + Complex.normSq (ip (-star q6) (star p6) a1 b1) = 1/8 * (Complex.normSq a1 + Complex.normSq b1) := by
    have h := lagrange p6 q6 a1 b1
    rw [ipw]
    rw [hQ6] at h
    linarith only [h, hQ6]
  have parD1 : Complex.normSq (ip p6 q6 p1 q1) + Complex.normSq (ip (-star q6) (star p6) p1 q1) = 1/8 * (Complex.normSq p1 + Complex.normSq q1) := by
    have h := lagrange p6 q6 p1 q1
    rw [ipw]
    rw [hQ6] at h
    linarith only [h, hQ6]
  have parC2 : Complex.normSq (ip p6 q6 a2 b2) + Complex.normSq (ip (-star q6) (star p6) a2 b2) = 1/8 * (Complex.normSq a2 + Complex.normSq b2) := by
    have h := lagrange p6 q6 a2 b2
    rw [ipw]
    rw [hQ6] at h
    linarith only [h, hQ6]
  have parD2 : Complex.normSq (ip p6 q6 p2 q2) + Complex.normSq (ip (-star q6) (star p6) p2 q2) = 1/8 * (Complex.normSq p2 + Complex.normSq q2) := by
    have h := lagrange p6 q6 p2 q2
    rw [ipw]
    rw [hQ6] at h
    linarith only [h, hQ6]
  have parC3 : Complex.normSq (ip p6 q6 a3 b3) + Complex.normSq (ip (-star q6) (star p6) a3 b3) = 1/8 * (Complex.normSq a3 + Complex.normSq b3) := by
    have h := lagrange p6 q6 a3 b3
    rw [ipw]
    rw [hQ6] at h
    linarith only [h, hQ6]
  have parD3 : Complex.normSq (ip p6 q6 p3 q3) + Complex.normSq (ip (-star q6) (star p6) p3 q3) = 1/8 * (Complex.normSq p3 + Complex.normSq q3) := by
    have h := lagrange p6 q6 p3 q3
    rw [ipw]
    rw [hQ6] at h
    linarith only [h, hQ6]
  have parC4 : Complex.normSq (ip p6 q6 a4 b4) + Complex.normSq (ip (-star q6) (star p6) a4 b4) = 1/8 * (Complex.normSq a4 + Complex.normSq b4) := by
    have h := lagrange p6 q6 a4 b4
    rw [ipw]
    rw [hQ6] at h
    linarith only [h, hQ6]
  have parD4 : Complex.normSq (ip p6 q6 p4 q4) + Complex.normSq (ip (-star q6) (star p6) p4 q4) = 1/8 * (Complex.normSq p4 + Complex.normSq q4) := by
    have h := lagrange p6 q6 p4 q4
    rw [ipw]
    rw [hQ6] at h
    linarith only [h, hQ6]
  have parC5 : Complex.normSq (ip p6 q6 a5 b5) + Complex.normSq (ip (-star q6) (star p6) a5 b5) = 1/8 * (Complex.normSq a5 + Complex.normSq b5) := by
    have h := lagrange p6 q6 a5 b5
    rw [ipw]
    rw [hQ6] at h
    linarith only [h, hQ6]
  have parD5 : Complex.normSq (ip p6 q6 p5 q5) + Complex.normSq (ip (-star q6) (star p6) p5 q5) = 1/8 * (Complex.normSq p5 + Complex.normSq q5) := by
    have h := lagrange p6 q6 p5 q5
    rw [ipw]
    rw [hQ6] at h
    linarith only [h, hQ6]
  have parC6 : Complex.normSq (ip p6 q6 a6 b6) + Complex.normSq (ip (-star q6) (star p6) a6 b6) = 1/8 * (Complex.normSq a6 + Complex.normSq b6) := by
    have h := lagrange p6 q6 a6 b6
    rw [ipw]
    rw [hQ6] at h
    linarith only [h, hQ6]
  have parD6 : Complex.normSq (ip p6 q6 p6 q6) + Complex.normSq (ip (-star q6) (star p6) p6 q6) = 1/8 * (Complex.normSq p6 + Complex.normSq q6) := by
    have h := lagrange p6 q6 p6 q6
    rw [ipw]
    rw [hQ6] at h
    linarith only [h, hQ6]
  have parC7 : Complex.normSq (ip p6 q6 a7 b7) + Complex.normSq (ip (-star q6) (star p6) a7 b7) = 1/8 * (Complex.normSq a7 + Complex.normSq b7) := by
    have h := lagrange p6 q6 a7 b7
    rw [ipw]
    rw [hQ6] at h
    linarith only [h, hQ6]
  have parD7 : Complex.normSq (ip p6 q6 p7 q7) + Complex.normSq (ip (-star q6) (star p6) p7 q7) = 1/8 * (Complex.normSq p7 + Complex.normSq q7) := by
    have h := lagrange p6 q6 p7 q7
    rw [ipw]
    rw [hQ6] at h
    linarith only [h, hQ6]
  -- nonnegativity
  have nnCM0 := Complex.normSq_nonneg (ip p6 q6 a0 b0)
  have nnCW0 := Complex.normSq_nonneg (ip (-star q6) (star p6) a0 b0)
  have nnDM0 := Complex.normSq_nonneg (ip p6 q6 p0 q0)
  have nnDW0 := Complex.normSq_nonneg (ip (-star q6) (star p6) p0 q0)
  have nnCN0 := Complex.normSq_nonneg (ip p7 q7 a0 b0)
  have nnDN0 := Complex.normSq_nonneg (ip p7 q7 p0 q0)
  have nnCM1 := Complex.normSq_nonneg (ip p6 q6 a1 b1)
  have nnCW1 := Complex.normSq_nonneg (ip (-star q6) (star p6) a1 b1)
  have nnDM1 := Complex.normSq_nonneg (ip p6 q6 p1 q1)
  have nnDW1 := Complex.normSq_nonneg (ip (-star q6) (star p6) p1 q1)
  have nnCN1 := Complex.normSq_nonneg (ip p7 q7 a1 b1)
  have nnDN1 := Complex.normSq_nonneg (ip p7 q7 p1 q1)
  have nnCM2 := Complex.normSq_nonneg (ip p6 q6 a2 b2)
  have nnCW2 := Complex.normSq_nonneg (ip (-star q6) (star p6) a2 b2)
  have nnDM2 := Complex.normSq_nonneg (ip p6 q6 p2 q2)
  have nnDW2 := Complex.normSq_nonneg (ip (-star q6) (star p6) p2 q2)
  have nnCN2 := Complex.normSq_nonneg (ip p7 q7 a2 b2)
  have nnDN2 := Complex.normSq_nonneg (ip p7 q7 p2 q2)
  have nnCM3 := Complex.normSq_nonneg (ip p6 q6 a3 b3)
  have nnCW3 := Complex.normSq_nonneg (ip (-star q6) (star p6) a3 b3)
  have nnDM3 := Complex.normSq_nonneg (ip p6 q6 p3 q3)
  have nnDW3 := Complex.normSq_nonneg (ip (-star q6) (star p6) p3 q3)
  have nnCN3 := Complex.normSq_nonneg (ip p7 q7 a3 b3)
  have nnDN3 := Complex.normSq_nonneg (ip p7 q7 p3 q3)
  have nnCM4 := Complex.normSq_nonneg (ip p6 q6 a4 b4)
  have nnCW4 := Complex.normSq_nonneg (ip (-star q6) (star p6) a4 b4)
  have nnDM4 := Complex.normSq_nonneg (ip p6 q6 p4 q4)
  have nnDW4 := Complex.normSq_nonneg (ip (-star q6) (star p6) p4 q4)
  have nnCN4 := Complex.normSq_nonneg (ip p7 q7 a4 b4)
  have nnDN4 := Complex.normSq_nonneg (ip p7 q7 p4 q4)
  have nnCM5 := Complex.normSq_nonneg (ip p6 q6 a5 b5)
  have nnCW5 := Complex.normSq_nonneg (ip (-star q6) (star p6) a5 b5)
  have nnDM5 := Complex.normSq_nonneg (ip p6 q6 p5 q5)
  have nnDW5 := Complex.normSq_nonneg (ip (-star q6) (star p6) p5 q5)
  have nnCN5 := Complex.normSq_nonneg (ip p7 q7 a5 b5)
  have nnDN5 := Complex.normSq_nonneg (ip p7 q7 p5 q5)
  have nnCM6 := Complex.normSq_nonneg (ip p6 q6 a6 b6)
  have nnCW6 := Complex.normSq_nonneg (ip (-star q6) (star p6) a6 b6)
  have nnDM6 := Complex.normSq_nonneg (ip p6 q6 p6 q6)
  have nnDW6 := Complex.normSq_nonneg (ip (-star q6) (star p6) p6 q6)
  have nnCN6 := Complex.normSq_nonneg (ip p7 q7 a6 b6)
  have nnDN6 := Complex.normSq_nonneg (ip p7 q7 p6 q6)
  have nnCM7 := Complex.normSq_nonneg (ip p6 q6 a7 b7)
  have nnCW7 := Complex.normSq_nonneg (ip (-star q6) (star p6) a7 b7)
  have nnDM7 := Complex.normSq_nonneg (ip p6 q6 p7 q7)
  have nnDW7 := Complex.normSq_nonneg (ip (-star q6) (star p6) p7 q7)
  have nnCN7 := Complex.normSq_nonneg (ip p7 q7 a7 b7)
  have nnDN7 := Complex.normSq_nonneg (ip p7 q7 p7 q7)
  -- the twelve sandwiches
  have SM0 := sandwich p6 q6 a0 b0 a1 b1 p0 q0 p1 q1 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 M0_11 M0_12 M0_21 M0_22
  have SM1 := sandwich p6 q6 a2 b2 a3 b3 p2 q2 p3 q3 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 M1_11 M1_12 M1_21 M1_22
  have SM2 := sandwich p6 q6 a4 b4 a5 b5 p4 q4 p5 q5 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 M2_11 M2_12 M2_21 M2_22
  have SM3 := sandwich p6 q6 a6 b6 a7 b7 p6 q6 p7 q7 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 M3_11 M3_12 M3_21 M3_22
  have SW0 := sandwich (-star q6) (star p6) a0 b0 a1 b1 p0 q0 p1 q1 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 M0_11 M0_12 M0_21 M0_22
  have SW1 := sandwich (-star q6) (star p6) a2 b2 a3 b3 p2 q2 p3 q3 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 M1_11 M1_12 M1_21 M1_22
  have SW2 := sandwich (-star q6) (star p6) a4 b4 a5 b5 p4 q4 p5 q5 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 M2_11 M2_12 M2_21 M2_22
  have SW3 := sandwich (-star q6) (star p6) a6 b6 a7 b7 p6 q6 p7 q7 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 M3_11 M3_12 M3_21 M3_22
  have SN0 := sandwich p7 q7 a0 b0 a1 b1 p0 q0 p1 q1 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 M0_11 M0_12 M0_21 M0_22
  have SN1 := sandwich p7 q7 a2 b2 a3 b3 p2 q2 p3 q3 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 M1_11 M1_12 M1_21 M1_22
  have SN2 := sandwich p7 q7 a4 b4 a5 b5 p4 q4 p5 q5 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 M2_11 M2_12 M2_21 M2_22
  have SN3 := sandwich p7 q7 a6 b6 a7 b7 p6 q6 p7 q7 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 M3_11 M3_12 M3_21 M3_22
  -- the anchor pairings, expressed in the frame
  have E6_0 : ip a6 b6 p0 q0 = - star (ip p6 q6 a0 b0) := by
    have h := An0_6
    rw [ip_eq, ip_eq] at h
    rw [ip_eq, ip_eq]
    simp only [star_add, star_mul', star_star]
    linear_combination h
  have E6_1 : ip a6 b6 p1 q1 = - star (ip p6 q6 a1 b1) := by
    have h := An1_6
    rw [ip_eq, ip_eq] at h
    rw [ip_eq, ip_eq]
    simp only [star_add, star_mul', star_star]
    linear_combination h
  have E6_2 : ip a6 b6 p2 q2 = - star (ip p6 q6 a2 b2) := by
    have h := An2_6
    rw [ip_eq, ip_eq] at h
    rw [ip_eq, ip_eq]
    simp only [star_add, star_mul', star_star]
    linear_combination h
  have E6_3 : ip a6 b6 p3 q3 = - star (ip p6 q6 a3 b3) := by
    have h := An3_6
    rw [ip_eq, ip_eq] at h
    rw [ip_eq, ip_eq]
    simp only [star_add, star_mul', star_star]
    linear_combination h
  have E6_4 : ip a6 b6 p4 q4 = - star (ip p6 q6 a4 b4) := by
    have h := An4_6
    rw [ip_eq, ip_eq] at h
    rw [ip_eq, ip_eq]
    simp only [star_add, star_mul', star_star]
    linear_combination h
  have E6_5 : ip a6 b6 p5 q5 = - star (ip p6 q6 a5 b5) := by
    have h := An5_6
    rw [ip_eq, ip_eq] at h
    rw [ip_eq, ip_eq]
    simp only [star_add, star_mul', star_star]
    linear_combination h
  have E7_0 : ip a7 b7 p0 q0 = - star (ip p7 q7 a0 b0) := by
    have h := An0_7
    rw [ip_eq, ip_eq] at h
    rw [ip_eq, ip_eq]
    simp only [star_add, star_mul', star_star]
    linear_combination h
  have E7_1 : ip a7 b7 p1 q1 = - star (ip p7 q7 a1 b1) := by
    have h := An1_7
    rw [ip_eq, ip_eq] at h
    rw [ip_eq, ip_eq]
    simp only [star_add, star_mul', star_star]
    linear_combination h
  have E7_2 : ip a7 b7 p2 q2 = - star (ip p7 q7 a2 b2) := by
    have h := An2_7
    rw [ip_eq, ip_eq] at h
    rw [ip_eq, ip_eq]
    simp only [star_add, star_mul', star_star]
    linear_combination h
  have E7_3 : ip a7 b7 p3 q3 = - star (ip p7 q7 a3 b3) := by
    have h := An3_7
    rw [ip_eq, ip_eq] at h
    rw [ip_eq, ip_eq]
    simp only [star_add, star_mul', star_star]
    linear_combination h
  have E7_4 : ip a7 b7 p4 q4 = - star (ip p7 q7 a4 b4) := by
    have h := An4_7
    rw [ip_eq, ip_eq] at h
    rw [ip_eq, ip_eq]
    simp only [star_add, star_mul', star_star]
    linear_combination h
  have E7_5 : ip a7 b7 p5 q5 = - star (ip p7 q7 a5 b5) := by
    have h := An5_7
    rw [ip_eq, ip_eq] at h
    rw [ip_eq, ip_eq]
    simp only [star_add, star_mul', star_star]
    linear_combination h
  -- special values in the frame
  have hdm6 : Complex.normSq (ip p6 q6 p6 q6) = 1/64 := by
    have h : ip p6 q6 p6 q6 = ((1/8 : ℝ) : ℂ) := by
      rw [ip_eq, sq, sq, ← Complex.ofReal_add, hQ6]
    rw [h, Complex.normSq_ofReal]; norm_num
  have hdn7 : Complex.normSq (ip p7 q7 p7 q7) = 1/64 := by
    have h : ip p7 q7 p7 q7 = ((1/8 : ℝ) : ℂ) := by
      rw [ip_eq, sq, sq, ← Complex.ofReal_add, hQ7]
    rw [h, Complex.normSq_ofReal]; norm_num
  have hdw6 : Complex.normSq (ip (-star q6) (star p6) p6 q6) = 0 := by
    rw [ipw, show p6 * q6 - q6 * p6 = (0:ℂ) from by ring]
    exact Complex.normSq_zero
  -- zero tests
  have nz6 : ∀ (x y u v : ℂ), ip a6 b6 u v = - star (ip p6 q6 x y) → ip a6 b6 u v = 0 →
      Complex.normSq (ip p6 q6 x y) = 0 := by
    intro x y u v hE h0
    have hs : star (ip p6 q6 x y) = 0 := by linear_combination hE - h0
    rw [star_eq_zero] at hs
    rw [hs]; exact Complex.normSq_zero
  have nz7 : ∀ (x y u v : ℂ), ip a7 b7 u v = - star (ip p7 q7 x y) → ip a7 b7 u v = 0 →
      Complex.normSq (ip p7 q7 x y) = 0 := by
    intro x y u v hE h0
    have hs : star (ip p7 q7 x y) = 0 := by linear_combination hE - h0
    rw [star_eq_zero] at hs
    rw [hs]; exact Complex.normSq_zero
  have dmz : ∀ (x y : ℂ), Complex.normSq (ip p6 q6 x y) = 0 → star p6 * x + star q6 * y = 0 := by
    intro x y h
    have h2 := Complex.normSq_eq_zero.mp h
    rwa [ip_eq] at h2
  have cmbz : ∀ (x y : ℂ), p6 * star x + q6 * star y = 0 → Complex.normSq (ip p6 q6 x y) = 0 := by
    intro x y h
    have h2 : star (ip p6 q6 x y) = 0 := by
      rw [ip_eq]; simp only [star_add, star_mul', star_star]; linear_combination h
    rw [star_eq_zero] at h2
    rw [h2]; exact Complex.normSq_zero
  have nnA0 := Complex.normSq_nonneg a0
  have nnB0 := Complex.normSq_nonneg b0
  have nnA1 := Complex.normSq_nonneg a1
  have nnB1 := Complex.normSq_nonneg b1
  have nnA2 := Complex.normSq_nonneg a2
  have nnB2 := Complex.normSq_nonneg b2
  have nnA3 := Complex.normSq_nonneg a3
  have nnB3 := Complex.normSq_nonneg b3
  have nnA4 := Complex.normSq_nonneg a4
  have nnB4 := Complex.normSq_nonneg b4
  have nnA5 := Complex.normSq_nonneg a5
  have nnB5 := Complex.normSq_nonneg b5
  have nnA6 := Complex.normSq_nonneg a6
  have nnB6 := Complex.normSq_nonneg b6
  have nnA7 := Complex.normSq_nonneg a7
  have nnB7 := Complex.normSq_nonneg b7
  have dmzero : ∀ (x y : ℂ), star p6 * x + star q6 * y = 0 → Complex.normSq (ip p6 q6 x y) = 0 := by
    intro x y h
    have h2 : ip p6 q6 x y = 0 := by rw [ip_eq]; exact h
    rw [h2]; exact Complex.normSq_zero
  have no66_01 : ¬((ip a6 b6 p0 q0 = 0 ∧ ip a6 b6 p1 q1 = 0) ∧ (ip a6 b6 p2 q2 = 0 ∧ ip a6 b6 p3 q3 = 0)) := by
    rintro ⟨⟨s0, s1⟩, ⟨s2, s3⟩⟩
    have z0 := nz6 a0 b0 p0 q0 E6_0 s0
    have z1 := nz6 a1 b1 p1 q1 E6_1 s1
    have z2 := nz6 a2 b2 p2 q2 E6_2 s2
    have z3 := nz6 a3 b3 p3 q3 E6_3 s3
    linarith only [SM0, SM1, SM2, SM3, hdm6, z0, z1, z2, z3, nnDM0, nnDM1, nnDM2, nnDM3, nnDM4, nnDM5, nnDM6, nnDM7, nnCM0, nnCM1, nnCM2, nnCM3, nnCM4, nnCM5, nnCM6, nnCM7]
  have no77_01 : ¬((ip a7 b7 p0 q0 = 0 ∧ ip a7 b7 p1 q1 = 0) ∧ (ip a7 b7 p2 q2 = 0 ∧ ip a7 b7 p3 q3 = 0)) := by
    rintro ⟨⟨s0, s1⟩, ⟨s2, s3⟩⟩
    have z0 := nz7 a0 b0 p0 q0 E7_0 s0
    have z1 := nz7 a1 b1 p1 q1 E7_1 s1
    have z2 := nz7 a2 b2 p2 q2 E7_2 s2
    have z3 := nz7 a3 b3 p3 q3 E7_3 s3
    linarith only [SN0, SN1, SN2, SN3, hdn7, z0, z1, z2, z3, nnDN0, nnDN1, nnDN2, nnDN3, nnDN4, nnDN5, nnDN6, nnDN7, nnCN0, nnCN1, nnCN2, nnCN3, nnCN4, nnCN5, nnCN6, nnCN7]
  have no66_02 : ¬((ip a6 b6 p0 q0 = 0 ∧ ip a6 b6 p1 q1 = 0) ∧ (ip a6 b6 p4 q4 = 0 ∧ ip a6 b6 p5 q5 = 0)) := by
    rintro ⟨⟨s0, s1⟩, ⟨s2, s3⟩⟩
    have z0 := nz6 a0 b0 p0 q0 E6_0 s0
    have z1 := nz6 a1 b1 p1 q1 E6_1 s1
    have z4 := nz6 a4 b4 p4 q4 E6_4 s2
    have z5 := nz6 a5 b5 p5 q5 E6_5 s3
    linarith only [SM0, SM1, SM2, SM3, hdm6, z0, z1, z4, z5, nnDM0, nnDM1, nnDM2, nnDM3, nnDM4, nnDM5, nnDM6, nnDM7, nnCM0, nnCM1, nnCM2, nnCM3, nnCM4, nnCM5, nnCM6, nnCM7]
  have no77_02 : ¬((ip a7 b7 p0 q0 = 0 ∧ ip a7 b7 p1 q1 = 0) ∧ (ip a7 b7 p4 q4 = 0 ∧ ip a7 b7 p5 q5 = 0)) := by
    rintro ⟨⟨s0, s1⟩, ⟨s2, s3⟩⟩
    have z0 := nz7 a0 b0 p0 q0 E7_0 s0
    have z1 := nz7 a1 b1 p1 q1 E7_1 s1
    have z4 := nz7 a4 b4 p4 q4 E7_4 s2
    have z5 := nz7 a5 b5 p5 q5 E7_5 s3
    linarith only [SN0, SN1, SN2, SN3, hdn7, z0, z1, z4, z5, nnDN0, nnDN1, nnDN2, nnDN3, nnDN4, nnDN5, nnDN6, nnDN7, nnCN0, nnCN1, nnCN2, nnCN3, nnCN4, nnCN5, nnCN6, nnCN7]
  have no66_12 : ¬((ip a6 b6 p2 q2 = 0 ∧ ip a6 b6 p3 q3 = 0) ∧ (ip a6 b6 p4 q4 = 0 ∧ ip a6 b6 p5 q5 = 0)) := by
    rintro ⟨⟨s0, s1⟩, ⟨s2, s3⟩⟩
    have z2 := nz6 a2 b2 p2 q2 E6_2 s0
    have z3 := nz6 a3 b3 p3 q3 E6_3 s1
    have z4 := nz6 a4 b4 p4 q4 E6_4 s2
    have z5 := nz6 a5 b5 p5 q5 E6_5 s3
    linarith only [SM0, SM1, SM2, SM3, hdm6, z2, z3, z4, z5, nnDM0, nnDM1, nnDM2, nnDM3, nnDM4, nnDM5, nnDM6, nnDM7, nnCM0, nnCM1, nnCM2, nnCM3, nnCM4, nnCM5, nnCM6, nnCM7]
  have no77_12 : ¬((ip a7 b7 p2 q2 = 0 ∧ ip a7 b7 p3 q3 = 0) ∧ (ip a7 b7 p4 q4 = 0 ∧ ip a7 b7 p5 q5 = 0)) := by
    rintro ⟨⟨s0, s1⟩, ⟨s2, s3⟩⟩
    have z2 := nz7 a2 b2 p2 q2 E7_2 s0
    have z3 := nz7 a3 b3 p3 q3 E7_3 s1
    have z4 := nz7 a4 b4 p4 q4 E7_4 s2
    have z5 := nz7 a5 b5 p5 q5 E7_5 s3
    linarith only [SN0, SN1, SN2, SN3, hdn7, z2, z3, z4, z5, nnDN0, nnDN1, nnDN2, nnDN3, nnDN4, nnDN5, nnDN6, nnDN7, nnCN0, nnCN1, nnCN2, nnCN3, nnCN4, nnCN5, nnCN6, nnCN7]
  have A6_01 := per_anchor a0 b0 a1 b1 a2 b2 a3 b3 p0 q0 p1 q1 p2 q2 p3 q3 p6 q6 a6 b6 O01_11 O01_12 O01_21 O01_22 An0_6 An1_6 An2_6 An3_6
  have A7_01 := per_anchor a0 b0 a1 b1 a2 b2 a3 b3 p0 q0 p1 q1 p2 q2 p3 q3 p7 q7 a7 b7 O01_11 O01_12 O01_21 O01_22 An0_7 An1_7 An2_7 An3_7
  have C_01 := cross_anchor a0 b0 a1 b1 a2 b2 a3 b3 p0 q0 p1 q1 p2 q2 p3 q3 p7 q7 a6 b6 (ip a7 b7 p0 q0) (ip a7 b7 p1 q1) (ip a7 b7 p2 q2) (ip a7 b7 p3 q3) O01_11 O01_12 O01_21 O01_22 An0_7 An1_7 An2_7 An3_7
  have A6_02 := per_anchor a0 b0 a1 b1 a4 b4 a5 b5 p0 q0 p1 q1 p4 q4 p5 q5 p6 q6 a6 b6 O02_11 O02_12 O02_21 O02_22 An0_6 An1_6 An4_6 An5_6
  have A7_02 := per_anchor a0 b0 a1 b1 a4 b4 a5 b5 p0 q0 p1 q1 p4 q4 p5 q5 p7 q7 a7 b7 O02_11 O02_12 O02_21 O02_22 An0_7 An1_7 An4_7 An5_7
  have C_02 := cross_anchor a0 b0 a1 b1 a4 b4 a5 b5 p0 q0 p1 q1 p4 q4 p5 q5 p7 q7 a6 b6 (ip a7 b7 p0 q0) (ip a7 b7 p1 q1) (ip a7 b7 p4 q4) (ip a7 b7 p5 q5) O02_11 O02_12 O02_21 O02_22 An0_7 An1_7 An4_7 An5_7
  have A6_12 := per_anchor a2 b2 a3 b3 a4 b4 a5 b5 p2 q2 p3 q3 p4 q4 p5 q5 p6 q6 a6 b6 O12_11 O12_12 O12_21 O12_22 An2_6 An3_6 An4_6 An5_6
  have A7_12 := per_anchor a2 b2 a3 b3 a4 b4 a5 b5 p2 q2 p3 q3 p4 q4 p5 q5 p7 q7 a7 b7 O12_11 O12_12 O12_21 O12_22 An2_7 An3_7 An4_7 An5_7
  have C_12 := cross_anchor a2 b2 a3 b3 a4 b4 a5 b5 p2 q2 p3 q3 p4 q4 p5 q5 p7 q7 a6 b6 (ip a7 b7 p2 q2) (ip a7 b7 p3 q3) (ip a7 b7 p4 q4) (ip a7 b7 p5 q5) O12_11 O12_12 O12_21 O12_22 An2_7 An3_7 An4_7 An5_7
  by_cases hdet : ip (-star q6) (star p6) p7 q7 = 0
  · have hdw7 : Complex.normSq (ip (-star q6) (star p6) p7 q7) = 0 := by
      rw [hdet]; exact Complex.normSq_zero
    by_cases hY60 : (ip a6 b6 p0 q0 = 0 ∧ ip a6 b6 p1 q1 = 0)
    ·
      by_cases hY61 : (ip a6 b6 p2 q2 = 0 ∧ ip a6 b6 p3 q3 = 0)
      ·
        by_cases hY62 : (ip a6 b6 p4 q4 = 0 ∧ ip a6 b6 p5 q5 = 0)
        ·
          exact no66_01 ⟨hY60, hY61⟩
        ·
          exact no66_01 ⟨hY60, hY61⟩
      ·
        by_cases hY62 : (ip a6 b6 p4 q4 = 0 ∧ ip a6 b6 p5 q5 = 0)
        ·
          exact no66_02 ⟨hY60, hY62⟩
        ·
          have tc0 := nz6 a0 b0 p0 q0 E6_0 hY60.1
          have tc1 := nz6 a1 b1 p1 q1 E6_1 hY60.2
          have hu2 : Complex.normSq (ip (-star q6) (star p6) a2 b2) = 0 := by linarith only [SW3, hdw6, hdw7, parC6, parC7, hP6, hP7, nnCM6, nnCM7, parC0, parC1, tc0, tc1, hT0, nnCW2, nnCW3, nnCW4, nnCW5]
          have hu3 : Complex.normSq (ip (-star q6) (star p6) a3 b3) = 0 := by linarith only [SW3, hdw6, hdw7, parC6, parC7, hP6, hP7, nnCM6, nnCM7, parC0, parC1, tc0, tc1, hT0, nnCW2, nnCW3, nnCW4, nnCW5]
          have hu4 : Complex.normSq (ip (-star q6) (star p6) a4 b4) = 0 := by linarith only [SW3, hdw6, hdw7, parC6, parC7, hP6, hP7, nnCM6, nnCM7, parC0, parC1, tc0, tc1, hT0, nnCW2, nnCW3, nnCW4, nnCW5]
          have hu5 : Complex.normSq (ip (-star q6) (star p6) a5 b5) = 0 := by linarith only [SW3, hdw6, hdw7, parC6, parC7, hP6, hP7, nnCM6, nnCM7, parC0, parC1, tc0, tc1, hT0, nnCW2, nnCW3, nnCW4, nnCW5]
          have hUC67 : Complex.normSq (ip (-star q6) (star p6) a6 b6) + Complex.normSq (ip (-star q6) (star p6) a7 b7) = 1/32 := by linarith only [SW3, hdw6, hdw7, parC0, parC1, tc0, tc1, hT0, hu2, hu3, hu4, hu5]
          have hdm2 : Complex.normSq (ip p6 q6 p2 q2) = 0 := by linarith only [SW1, hUC67, hu2, hu3, hu4, hu5, parC0, parC1, tc0, tc1, hT0, parD2, parD3, hPQ2, hPQ3, hT1, nnDM2, nnDM3]
          have hdm3 : Complex.normSq (ip p6 q6 p3 q3) = 0 := by linarith only [SW1, hUC67, hu2, hu3, hu4, hu5, parC0, parC1, tc0, tc1, hT0, parD2, parD3, hPQ2, hPQ3, hT1, nnDM2, nnDM3]
          have hdm4 : Complex.normSq (ip p6 q6 p4 q4) = 0 := by linarith only [SW2, hUC67, hu2, hu3, hu4, hu5, parC0, parC1, tc0, tc1, hT0, parD4, parD5, hPQ4, hPQ5, hT2, nnDM4, nnDM5]
          have hdm5 : Complex.normSq (ip p6 q6 p5 q5) = 0 := by linarith only [SW2, hUC67, hu2, hu3, hu4, hu5, parC0, parC1, tc0, tc1, hT0, parD4, parD5, hPQ4, hPQ5, hT2, nnDM4, nnDM5]
          have hDg : Complex.normSq (ip p6 q6 p0 q0) + Complex.normSq (ip p6 q6 p1 q1) = 1/32 := by linarith only [SW0, hUC67, hu2, hu3, hu4, hu5, parC0, parC1, tc0, tc1, hT0, parD0, parD1, hPQ0, hPQ1]
          have ez2 := dmz p2 q2 hdm2
          have ez3 := dmz p3 q3 hdm3
          have ez4 := dmz p4 q4 hdm4
          have ez5 := dmz p5 q5 hdm5
          have Bh : (p6 * star a2 + q6 * star b2) * (star p6 * p1 + star q6 * q1) + (p6 * star a3 + q6 * star b3) * (star p6 * p0 + star q6 * q0) = 0 := by
            linear_combination (p6 * star p6) * O01_11 + (p6 * star q6) * O01_12
              + (q6 * star p6) * O01_21 + (q6 * star q6) * O01_22
              - (p6 * star a0 + q6 * star b0) * ez3 - (p6 * star a1 + q6 * star b1) * ez2
          have Bk : (p6 * star a4 + q6 * star b4) * (star p6 * p1 + star q6 * q1) + (p6 * star a5 + q6 * star b5) * (star p6 * p0 + star q6 * q0) = 0 := by
            linear_combination (p6 * star p6) * O02_11 + (p6 * star q6) * O02_12
              + (q6 * star p6) * O02_21 + (q6 * star q6) * O02_22
              - (p6 * star a0 + q6 * star b0) * ez5 - (p6 * star a1 + q6 * star b1) * ez4
          have hDelta : (p6 * star a2 + q6 * star b2) * (p6 * star a5 + q6 * star b5) - (p6 * star a3 + q6 * star b3) * (p6 * star a4 + q6 * star b4) = 0 := by
            have k1 : (star p6 * p1 + star q6 * q1) * ((p6 * star a2 + q6 * star b2) * (p6 * star a5 + q6 * star b5) - (p6 * star a3 + q6 * star b3) * (p6 * star a4 + q6 * star b4)) = 0 := by
              linear_combination (p6 * star a5 + q6 * star b5) * Bh - (p6 * star a3 + q6 * star b3) * Bk
            have k2 : (star p6 * p0 + star q6 * q0) * ((p6 * star a2 + q6 * star b2) * (p6 * star a5 + q6 * star b5) - (p6 * star a3 + q6 * star b3) * (p6 * star a4 + q6 * star b4)) = 0 := by
              linear_combination (-(p6 * star a4 + q6 * star b4)) * Bh + (p6 * star a2 + q6 * star b2) * Bk
            rcases mul_eq_zero.mp k1 with e | e
            · rcases mul_eq_zero.mp k2 with e2 | e2
              · exact absurd hDg (by rw [dmzero p0 q0 e2, dmzero p1 q1 e]; norm_num)
              · exact e2
            · exact e
          have hSig : (p6 * star a2 + q6 * star b2) * (p6 * star a5 + q6 * star b5) + (p6 * star a3 + q6 * star b3) * (p6 * star a4 + q6 * star b4) = 0 := by
            have hA := A6_12
            simp only [Jform] at hA
            rw [E6_2, E6_3, E6_4, E6_5] at hA
            simp only [ip_eq, star_add, star_mul', star_star] at hA
            linear_combination hA
          have hzz1 : (p6 * star a2 + q6 * star b2) * (p6 * star a5 + q6 * star b5) = 0 := by linear_combination hDelta/2 + hSig/2
          have hzz2 : (p6 * star a3 + q6 * star b3) * (p6 * star a4 + q6 * star b4) = 0 := by linear_combination hSig/2 - hDelta/2
          rcases mul_eq_zero.mp hzz1 with e1 | e1
          · have v2 := cmbz a2 b2 e1
            rcases mul_eq_zero.mp hzz2 with e2 | e2
            · have v3 := cmbz a3 b3 e2
              linarith only [parC2, parC3, v2, v3, hu2, hu3, hT1]
            · have v4 := cmbz a4 b4 e2
              linarith only [parC2, parC4, v2, v4, hu2, hu4, hT2a, hT0, nnA1, nnB1]
          · have v5 := cmbz a5 b5 e1
            rcases mul_eq_zero.mp hzz2 with e2 | e2
            · have v3 := cmbz a3 b3 e2
              linarith only [parC3, parC5, v3, v5, hu3, hu5, hT2b, hT0, nnA0, nnB0]
            · have v4 := cmbz a4 b4 e2
              linarith only [parC4, parC5, v4, v5, hu4, hu5, hT2]
    ·
      by_cases hY61 : (ip a6 b6 p2 q2 = 0 ∧ ip a6 b6 p3 q3 = 0)
      ·
        by_cases hY62 : (ip a6 b6 p4 q4 = 0 ∧ ip a6 b6 p5 q5 = 0)
        ·
          exact no66_12 ⟨hY61, hY62⟩
        ·
          have tc2 := nz6 a2 b2 p2 q2 E6_2 hY61.1
          have tc3 := nz6 a3 b3 p3 q3 E6_3 hY61.2
          have hu0 : Complex.normSq (ip (-star q6) (star p6) a0 b0) = 0 := by linarith only [SW3, hdw6, hdw7, parC6, parC7, hP6, hP7, nnCM6, nnCM7, parC2, parC3, tc2, tc3, hT1, nnCW0, nnCW1, nnCW4, nnCW5]
          have hu1 : Complex.normSq (ip (-star q6) (star p6) a1 b1) = 0 := by linarith only [SW3, hdw6, hdw7, parC6, parC7, hP6, hP7, nnCM6, nnCM7, parC2, parC3, tc2, tc3, hT1, nnCW0, nnCW1, nnCW4, nnCW5]
          have hu4 : Complex.normSq (ip (-star q6) (star p6) a4 b4) = 0 := by linarith only [SW3, hdw6, hdw7, parC6, parC7, hP6, hP7, nnCM6, nnCM7, parC2, parC3, tc2, tc3, hT1, nnCW0, nnCW1, nnCW4, nnCW5]
          have hu5 : Complex.normSq (ip (-star q6) (star p6) a5 b5) = 0 := by linarith only [SW3, hdw6, hdw7, parC6, parC7, hP6, hP7, nnCM6, nnCM7, parC2, parC3, tc2, tc3, hT1, nnCW0, nnCW1, nnCW4, nnCW5]
          have hUC67 : Complex.normSq (ip (-star q6) (star p6) a6 b6) + Complex.normSq (ip (-star q6) (star p6) a7 b7) = 1/32 := by linarith only [SW3, hdw6, hdw7, parC2, parC3, tc2, tc3, hT1, hu0, hu1, hu4, hu5]
          have hdm0 : Complex.normSq (ip p6 q6 p0 q0) = 0 := by linarith only [SW0, hUC67, hu0, hu1, hu4, hu5, parC2, parC3, tc2, tc3, hT1, parD0, parD1, hPQ0, hPQ1, hT0, nnDM0, nnDM1]
          have hdm1 : Complex.normSq (ip p6 q6 p1 q1) = 0 := by linarith only [SW0, hUC67, hu0, hu1, hu4, hu5, parC2, parC3, tc2, tc3, hT1, parD0, parD1, hPQ0, hPQ1, hT0, nnDM0, nnDM1]
          have hdm4 : Complex.normSq (ip p6 q6 p4 q4) = 0 := by linarith only [SW2, hUC67, hu0, hu1, hu4, hu5, parC2, parC3, tc2, tc3, hT1, parD4, parD5, hPQ4, hPQ5, hT2, nnDM4, nnDM5]
          have hdm5 : Complex.normSq (ip p6 q6 p5 q5) = 0 := by linarith only [SW2, hUC67, hu0, hu1, hu4, hu5, parC2, parC3, tc2, tc3, hT1, parD4, parD5, hPQ4, hPQ5, hT2, nnDM4, nnDM5]
          have hDg : Complex.normSq (ip p6 q6 p2 q2) + Complex.normSq (ip p6 q6 p3 q3) = 1/32 := by linarith only [SW1, hUC67, hu0, hu1, hu4, hu5, parC2, parC3, tc2, tc3, hT1, parD2, parD3, hPQ2, hPQ3]
          have ez0 := dmz p0 q0 hdm0
          have ez1 := dmz p1 q1 hdm1
          have ez4 := dmz p4 q4 hdm4
          have ez5 := dmz p5 q5 hdm5
          have Bh : (p6 * star a0 + q6 * star b0) * (star p6 * p3 + star q6 * q3) + (p6 * star a1 + q6 * star b1) * (star p6 * p2 + star q6 * q2) = 0 := by
            linear_combination (p6 * star p6) * O01_11 + (p6 * star q6) * O01_12
              + (q6 * star p6) * O01_21 + (q6 * star q6) * O01_22
              - (p6 * star a2 + q6 * star b2) * ez1 - (p6 * star a3 + q6 * star b3) * ez0
          have Bk : (p6 * star a4 + q6 * star b4) * (star p6 * p3 + star q6 * q3) + (p6 * star a5 + q6 * star b5) * (star p6 * p2 + star q6 * q2) = 0 := by
            linear_combination (p6 * star p6) * O12_11 + (p6 * star q6) * O12_12
              + (q6 * star p6) * O12_21 + (q6 * star q6) * O12_22
              - (p6 * star a2 + q6 * star b2) * ez5 - (p6 * star a3 + q6 * star b3) * ez4
          have hDelta : (p6 * star a0 + q6 * star b0) * (p6 * star a5 + q6 * star b5) - (p6 * star a1 + q6 * star b1) * (p6 * star a4 + q6 * star b4) = 0 := by
            have k1 : (star p6 * p3 + star q6 * q3) * ((p6 * star a0 + q6 * star b0) * (p6 * star a5 + q6 * star b5) - (p6 * star a1 + q6 * star b1) * (p6 * star a4 + q6 * star b4)) = 0 := by
              linear_combination (p6 * star a5 + q6 * star b5) * Bh - (p6 * star a1 + q6 * star b1) * Bk
            have k2 : (star p6 * p2 + star q6 * q2) * ((p6 * star a0 + q6 * star b0) * (p6 * star a5 + q6 * star b5) - (p6 * star a1 + q6 * star b1) * (p6 * star a4 + q6 * star b4)) = 0 := by
              linear_combination (-(p6 * star a4 + q6 * star b4)) * Bh + (p6 * star a0 + q6 * star b0) * Bk
            rcases mul_eq_zero.mp k1 with e | e
            · rcases mul_eq_zero.mp k2 with e2 | e2
              · exact absurd hDg (by rw [dmzero p2 q2 e2, dmzero p3 q3 e]; norm_num)
              · exact e2
            · exact e
          have hSig : (p6 * star a0 + q6 * star b0) * (p6 * star a5 + q6 * star b5) + (p6 * star a1 + q6 * star b1) * (p6 * star a4 + q6 * star b4) = 0 := by
            have hA := A6_02
            simp only [Jform] at hA
            rw [E6_0, E6_1, E6_4, E6_5] at hA
            simp only [ip_eq, star_add, star_mul', star_star] at hA
            linear_combination hA
          have hzz1 : (p6 * star a0 + q6 * star b0) * (p6 * star a5 + q6 * star b5) = 0 := by linear_combination hDelta/2 + hSig/2
          have hzz2 : (p6 * star a1 + q6 * star b1) * (p6 * star a4 + q6 * star b4) = 0 := by linear_combination hSig/2 - hDelta/2
          rcases mul_eq_zero.mp hzz1 with e1 | e1
          · have v0 := cmbz a0 b0 e1
            rcases mul_eq_zero.mp hzz2 with e2 | e2
            · have v1 := cmbz a1 b1 e2
              linarith only [parC0, parC1, v0, v1, hu0, hu1, hT0]
            · have v4 := cmbz a4 b4 e2
              linarith only [parC0, parC4, v0, v4, hu0, hu4, hT2a, hT1, nnA3, nnB3]
          · have v5 := cmbz a5 b5 e1
            rcases mul_eq_zero.mp hzz2 with e2 | e2
            · have v1 := cmbz a1 b1 e2
              linarith only [parC1, parC5, v1, v5, hu1, hu5, hT2b, hT1, nnA2, nnB2]
            · have v4 := cmbz a4 b4 e2
              linarith only [parC4, parC5, v4, v5, hu4, hu5, hT2]
      ·
        by_cases hY62 : (ip a6 b6 p4 q4 = 0 ∧ ip a6 b6 p5 q5 = 0)
        ·
          have tc4 := nz6 a4 b4 p4 q4 E6_4 hY62.1
          have tc5 := nz6 a5 b5 p5 q5 E6_5 hY62.2
          have hu0 : Complex.normSq (ip (-star q6) (star p6) a0 b0) = 0 := by linarith only [SW3, hdw6, hdw7, parC6, parC7, hP6, hP7, nnCM6, nnCM7, parC4, parC5, tc4, tc5, hT2, nnCW0, nnCW1, nnCW2, nnCW3]
          have hu1 : Complex.normSq (ip (-star q6) (star p6) a1 b1) = 0 := by linarith only [SW3, hdw6, hdw7, parC6, parC7, hP6, hP7, nnCM6, nnCM7, parC4, parC5, tc4, tc5, hT2, nnCW0, nnCW1, nnCW2, nnCW3]
          have hu2 : Complex.normSq (ip (-star q6) (star p6) a2 b2) = 0 := by linarith only [SW3, hdw6, hdw7, parC6, parC7, hP6, hP7, nnCM6, nnCM7, parC4, parC5, tc4, tc5, hT2, nnCW0, nnCW1, nnCW2, nnCW3]
          have hu3 : Complex.normSq (ip (-star q6) (star p6) a3 b3) = 0 := by linarith only [SW3, hdw6, hdw7, parC6, parC7, hP6, hP7, nnCM6, nnCM7, parC4, parC5, tc4, tc5, hT2, nnCW0, nnCW1, nnCW2, nnCW3]
          have hUC67 : Complex.normSq (ip (-star q6) (star p6) a6 b6) + Complex.normSq (ip (-star q6) (star p6) a7 b7) = 1/32 := by linarith only [SW3, hdw6, hdw7, parC4, parC5, tc4, tc5, hT2, hu0, hu1, hu2, hu3]
          have hdm0 : Complex.normSq (ip p6 q6 p0 q0) = 0 := by linarith only [SW0, hUC67, hu0, hu1, hu2, hu3, parC4, parC5, tc4, tc5, hT2, parD0, parD1, hPQ0, hPQ1, hT0, nnDM0, nnDM1]
          have hdm1 : Complex.normSq (ip p6 q6 p1 q1) = 0 := by linarith only [SW0, hUC67, hu0, hu1, hu2, hu3, parC4, parC5, tc4, tc5, hT2, parD0, parD1, hPQ0, hPQ1, hT0, nnDM0, nnDM1]
          have hdm2 : Complex.normSq (ip p6 q6 p2 q2) = 0 := by linarith only [SW1, hUC67, hu0, hu1, hu2, hu3, parC4, parC5, tc4, tc5, hT2, parD2, parD3, hPQ2, hPQ3, hT1, nnDM2, nnDM3]
          have hdm3 : Complex.normSq (ip p6 q6 p3 q3) = 0 := by linarith only [SW1, hUC67, hu0, hu1, hu2, hu3, parC4, parC5, tc4, tc5, hT2, parD2, parD3, hPQ2, hPQ3, hT1, nnDM2, nnDM3]
          have hDg : Complex.normSq (ip p6 q6 p4 q4) + Complex.normSq (ip p6 q6 p5 q5) = 1/32 := by linarith only [SW2, hUC67, hu0, hu1, hu2, hu3, parC4, parC5, tc4, tc5, hT2, parD4, parD5, hPQ4, hPQ5]
          have ez0 := dmz p0 q0 hdm0
          have ez1 := dmz p1 q1 hdm1
          have ez2 := dmz p2 q2 hdm2
          have ez3 := dmz p3 q3 hdm3
          have Bh : (p6 * star a0 + q6 * star b0) * (star p6 * p5 + star q6 * q5) + (p6 * star a1 + q6 * star b1) * (star p6 * p4 + star q6 * q4) = 0 := by
            linear_combination (p6 * star p6) * O02_11 + (p6 * star q6) * O02_12
              + (q6 * star p6) * O02_21 + (q6 * star q6) * O02_22
              - (p6 * star a4 + q6 * star b4) * ez1 - (p6 * star a5 + q6 * star b5) * ez0
          have Bk : (p6 * star a2 + q6 * star b2) * (star p6 * p5 + star q6 * q5) + (p6 * star a3 + q6 * star b3) * (star p6 * p4 + star q6 * q4) = 0 := by
            linear_combination (p6 * star p6) * O12_11 + (p6 * star q6) * O12_12
              + (q6 * star p6) * O12_21 + (q6 * star q6) * O12_22
              - (p6 * star a4 + q6 * star b4) * ez3 - (p6 * star a5 + q6 * star b5) * ez2
          have hDelta : (p6 * star a0 + q6 * star b0) * (p6 * star a3 + q6 * star b3) - (p6 * star a1 + q6 * star b1) * (p6 * star a2 + q6 * star b2) = 0 := by
            have k1 : (star p6 * p5 + star q6 * q5) * ((p6 * star a0 + q6 * star b0) * (p6 * star a3 + q6 * star b3) - (p6 * star a1 + q6 * star b1) * (p6 * star a2 + q6 * star b2)) = 0 := by
              linear_combination (p6 * star a3 + q6 * star b3) * Bh - (p6 * star a1 + q6 * star b1) * Bk
            have k2 : (star p6 * p4 + star q6 * q4) * ((p6 * star a0 + q6 * star b0) * (p6 * star a3 + q6 * star b3) - (p6 * star a1 + q6 * star b1) * (p6 * star a2 + q6 * star b2)) = 0 := by
              linear_combination (-(p6 * star a2 + q6 * star b2)) * Bh + (p6 * star a0 + q6 * star b0) * Bk
            rcases mul_eq_zero.mp k1 with e | e
            · rcases mul_eq_zero.mp k2 with e2 | e2
              · exact absurd hDg (by rw [dmzero p4 q4 e2, dmzero p5 q5 e]; norm_num)
              · exact e2
            · exact e
          have hSig : (p6 * star a0 + q6 * star b0) * (p6 * star a3 + q6 * star b3) + (p6 * star a1 + q6 * star b1) * (p6 * star a2 + q6 * star b2) = 0 := by
            have hA := A6_01
            simp only [Jform] at hA
            rw [E6_0, E6_1, E6_2, E6_3] at hA
            simp only [ip_eq, star_add, star_mul', star_star] at hA
            linear_combination hA
          have hzz1 : (p6 * star a0 + q6 * star b0) * (p6 * star a3 + q6 * star b3) = 0 := by linear_combination hDelta/2 + hSig/2
          have hzz2 : (p6 * star a1 + q6 * star b1) * (p6 * star a2 + q6 * star b2) = 0 := by linear_combination hSig/2 - hDelta/2
          rcases mul_eq_zero.mp hzz1 with e1 | e1
          · have v0 := cmbz a0 b0 e1
            rcases mul_eq_zero.mp hzz2 with e2 | e2
            · have v1 := cmbz a1 b1 e2
              linarith only [parC0, parC1, v0, v1, hu0, hu1, hT0]
            · have v2 := cmbz a2 b2 e2
              linarith only [parC0, parC2, v0, v2, hu0, hu2, hT2a, hT2, nnA5, nnB5]
          · have v3 := cmbz a3 b3 e1
            rcases mul_eq_zero.mp hzz2 with e2 | e2
            · have v1 := cmbz a1 b1 e2
              linarith only [parC1, parC3, v1, v3, hu1, hu3, hT2b, hT2, nnA4, nnB4]
            · have v2 := cmbz a2 b2 e2
              linarith only [parC2, parC3, v2, v3, hu2, hu3, hT1]
        ·
          have HX := axis_lemma (ip a6 b6 p0 q0) (ip a6 b6 p1 q1) (ip a6 b6 p2 q2) (ip a6 b6 p3 q3) (ip a6 b6 p4 q4) (ip a6 b6 p5 q5)
            hY60 hY61 hY62 A6_01 A6_02 A6_12
          rcases HX with ⟨o1, o3, o5⟩ | ⟨o0, o2, o4⟩
          ·
            have z1 := nz6 a1 b1 p1 q1 E6_1 o1
            have z3 := nz6 a3 b3 p3 q3 E6_3 o3
            have z5 := nz6 a5 b5 p5 q5 E6_5 o5
            linarith only [SW3, hdw6, hdw7, parC6, parC7, hP6, hP7, nnCM6, nnCM7, parC1, parC3, parC5, z1, z3, z5, nnCW0, nnCW2, nnCW4, hT2b]
          ·
            have z0 := nz6 a0 b0 p0 q0 E6_0 o0
            have z2 := nz6 a2 b2 p2 q2 E6_2 o2
            have z4 := nz6 a4 b4 p4 q4 E6_4 o4
            linarith only [SW3, hdw6, hdw7, parC6, parC7, hP6, hP7, nnCM6, nnCM7, parC0, parC2, parC4, z0, z2, z4, nnCW1, nnCW3, nnCW5, hT2a]
  · have hdetc : star p6 * star q7 - star q6 * star p7 ≠ 0 := by
      intro h
      apply hdet
      rw [ipw]
      have h2 : star (p6 * q7 - q6 * p7) = 0 := by
        simp only [star_sub, star_mul']
        linear_combination h
      exact star_eq_zero.mp h2
    have kill : ∀ (x y : ℂ), star (ip p6 q6 x y) = 0 → star (ip p7 q7 x y) = 0 →
        Complex.normSq x + Complex.normSq y = 0 := by
      intro x y h6 h7
      rw [star_eq_zero, ip_eq] at h6
      rw [star_eq_zero, ip_eq] at h7
      have hx : x = 0 := by
        have kk : x * (star p6 * star q7 - star q6 * star p7) = 0 := by
          linear_combination (star q7) * h6 - (star q6) * h7
        exact (mul_eq_zero.mp kk).resolve_right hdetc
      have hy : y = 0 := by
        have kk : y * (star p6 * star q7 - star q6 * star p7) = 0 := by
          linear_combination (-(star p7)) * h6 + (star p6) * h7
        exact (mul_eq_zero.mp kk).resolve_right hdetc
      rw [hx, hy]; simp
    have no67_0 : ¬((ip a6 b6 p0 q0 = 0 ∧ ip a6 b6 p1 q1 = 0) ∧ (ip a7 b7 p0 q0 = 0 ∧ ip a7 b7 p1 q1 = 0)) := by
      rintro ⟨⟨s0, s1⟩, ⟨t0, t1⟩⟩
      have z0 := kill a0 b0 (by linear_combination E6_0 - s0) (by linear_combination E7_0 - t0)
      have z1 := kill a1 b1 (by linear_combination E6_1 - s1) (by linear_combination E7_1 - t1)
      linarith only [z0, z1, hT0]
    have no67_1 : ¬((ip a6 b6 p2 q2 = 0 ∧ ip a6 b6 p3 q3 = 0) ∧ (ip a7 b7 p2 q2 = 0 ∧ ip a7 b7 p3 q3 = 0)) := by
      rintro ⟨⟨s0, s1⟩, ⟨t0, t1⟩⟩
      have z2 := kill a2 b2 (by linear_combination E6_2 - s0) (by linear_combination E7_2 - t0)
      have z3 := kill a3 b3 (by linear_combination E6_3 - s1) (by linear_combination E7_3 - t1)
      linarith only [z2, z3, hT1]
    have no67_2 : ¬((ip a6 b6 p4 q4 = 0 ∧ ip a6 b6 p5 q5 = 0) ∧ (ip a7 b7 p4 q4 = 0 ∧ ip a7 b7 p5 q5 = 0)) := by
      rintro ⟨⟨s0, s1⟩, ⟨t0, t1⟩⟩
      have z4 := kill a4 b4 (by linear_combination E6_4 - s0) (by linear_combination E7_4 - t0)
      have z5 := kill a5 b5 (by linear_combination E6_5 - s1) (by linear_combination E7_5 - t1)
      linarith only [z4, z5, hT2]
    have closeA : (ip a6 b6 p1 q1 = 0 ∧ ip a6 b6 p3 q3 = 0 ∧ ip a6 b6 p5 q5 = 0 ∧ ip a7 b7 p1 q1 = 0 ∧ ip a7 b7 p3 q3 = 0 ∧ ip a7 b7 p5 q5 = 0)
        ∨ (ip a6 b6 p0 q0 = 0 ∧ ip a6 b6 p2 q2 = 0 ∧ ip a6 b6 p4 q4 = 0 ∧ ip a7 b7 p0 q0 = 0 ∧ ip a7 b7 p2 q2 = 0 ∧ ip a7 b7 p4 q4 = 0) → False := by
      rintro (⟨u1, u3, u5, v1, v3, v5⟩ | ⟨u0, u2, u4, v0, v2, v4⟩)
      · have z1 := kill a1 b1 (by linear_combination E6_1 - u1) (by linear_combination E7_1 - v1)
        have z3 := kill a3 b3 (by linear_combination E6_3 - u3) (by linear_combination E7_3 - v3)
        have z5 := kill a5 b5 (by linear_combination E6_5 - u5) (by linear_combination E7_5 - v5)
        linarith only [z1, z3, z5, hT2b]
      · have z0 := kill a0 b0 (by linear_combination E6_0 - u0) (by linear_combination E7_0 - v0)
        have z2 := kill a2 b2 (by linear_combination E6_2 - u2) (by linear_combination E7_2 - v2)
        have z4 := kill a4 b4 (by linear_combination E6_4 - u4) (by linear_combination E7_4 - v4)
        linarith only [z0, z2, z4, hT2a]
    by_cases hY60 : (ip a6 b6 p0 q0 = 0 ∧ ip a6 b6 p1 q1 = 0)
    ·
      by_cases hY61 : (ip a6 b6 p2 q2 = 0 ∧ ip a6 b6 p3 q3 = 0)
      ·
        by_cases hY62 : (ip a6 b6 p4 q4 = 0 ∧ ip a6 b6 p5 q5 = 0)
        ·
          exact no66_01 ⟨hY60, hY61⟩
        ·
          exact no66_01 ⟨hY60, hY61⟩
      ·
        by_cases hY62 : (ip a6 b6 p4 q4 = 0 ∧ ip a6 b6 p5 q5 = 0)
        ·
          exact no66_02 ⟨hY60, hY62⟩
        ·
          have H := branch3_aligned (ip a6 b6 p0 q0) (ip a6 b6 p1 q1) (ip a6 b6 p2 q2) (ip a6 b6 p3 q3) (ip a6 b6 p4 q4) (ip a6 b6 p5 q5) (ip a7 b7 p0 q0) (ip a7 b7 p1 q1) (ip a7 b7 p2 q2) (ip a7 b7 p3 q3) (ip a7 b7 p4 q4) (ip a7 b7 p5 q5)
            hY60.1 hY60.2 hY61 hY62 (fun hh => no67_0 ⟨hY60, hh⟩)
            (by simp only [Jform] at A6_12 ⊢; linear_combination A6_12)
            (by simp only [Jform] at A7_01 ⊢; linear_combination A7_01)
            (by simp only [Jform] at A7_02 ⊢; linear_combination A7_02)
            (by simp only [Jform] at C_01 ⊢; linear_combination C_01)
            (by simp only [Jform] at C_02 ⊢; linear_combination C_02)
          rcases H with ⟨m6_1, m6_3, m6_5, m7_1, m7_3, m7_5⟩ | ⟨m6_0, m6_2, m6_4, m7_0, m7_2, m7_4⟩
          · exact closeA (Or.inl ⟨m6_1, m6_3, m6_5, m7_1, m7_3, m7_5⟩)
          · exact closeA (Or.inr ⟨m6_0, m6_2, m6_4, m7_0, m7_2, m7_4⟩)
    ·
      by_cases hY61 : (ip a6 b6 p2 q2 = 0 ∧ ip a6 b6 p3 q3 = 0)
      ·
        by_cases hY62 : (ip a6 b6 p4 q4 = 0 ∧ ip a6 b6 p5 q5 = 0)
        ·
          exact no66_12 ⟨hY61, hY62⟩
        ·
          have H := branch3_aligned (ip a6 b6 p2 q2) (ip a6 b6 p3 q3) (ip a6 b6 p0 q0) (ip a6 b6 p1 q1) (ip a6 b6 p4 q4) (ip a6 b6 p5 q5) (ip a7 b7 p2 q2) (ip a7 b7 p3 q3) (ip a7 b7 p0 q0) (ip a7 b7 p1 q1) (ip a7 b7 p4 q4) (ip a7 b7 p5 q5)
            hY61.1 hY61.2 hY60 hY62 (fun hh => no67_1 ⟨hY61, hh⟩)
            (by simp only [Jform] at A6_02 ⊢; linear_combination A6_02)
            (by simp only [Jform] at A7_01 ⊢; linear_combination A7_01)
            (by simp only [Jform] at A7_12 ⊢; linear_combination A7_12)
            (by simp only [Jform] at C_01 ⊢; linear_combination C_01)
            (by simp only [Jform] at C_12 ⊢; linear_combination C_12)
          rcases H with ⟨m6_3, m6_1, m6_5, m7_3, m7_1, m7_5⟩ | ⟨m6_2, m6_0, m6_4, m7_2, m7_0, m7_4⟩
          · exact closeA (Or.inl ⟨m6_1, m6_3, m6_5, m7_1, m7_3, m7_5⟩)
          · exact closeA (Or.inr ⟨m6_0, m6_2, m6_4, m7_0, m7_2, m7_4⟩)
      ·
        by_cases hY62 : (ip a6 b6 p4 q4 = 0 ∧ ip a6 b6 p5 q5 = 0)
        ·
          have H := branch3_aligned (ip a6 b6 p4 q4) (ip a6 b6 p5 q5) (ip a6 b6 p0 q0) (ip a6 b6 p1 q1) (ip a6 b6 p2 q2) (ip a6 b6 p3 q3) (ip a7 b7 p4 q4) (ip a7 b7 p5 q5) (ip a7 b7 p0 q0) (ip a7 b7 p1 q1) (ip a7 b7 p2 q2) (ip a7 b7 p3 q3)
            hY62.1 hY62.2 hY60 hY61 (fun hh => no67_2 ⟨hY62, hh⟩)
            (by simp only [Jform] at A6_01 ⊢; linear_combination A6_01)
            (by simp only [Jform] at A7_02 ⊢; linear_combination A7_02)
            (by simp only [Jform] at A7_12 ⊢; linear_combination A7_12)
            (by simp only [Jform] at C_02 ⊢; linear_combination C_02)
            (by simp only [Jform] at C_12 ⊢; linear_combination C_12)
          rcases H with ⟨m6_5, m6_1, m6_3, m7_5, m7_1, m7_3⟩ | ⟨m6_4, m6_0, m6_2, m7_4, m7_0, m7_2⟩
          · exact closeA (Or.inl ⟨m6_1, m6_3, m6_5, m7_1, m7_3, m7_5⟩)
          · exact closeA (Or.inr ⟨m6_0, m6_2, m6_4, m7_0, m7_2, m7_4⟩)
        ·
          by_cases hY70 : (ip a7 b7 p0 q0 = 0 ∧ ip a7 b7 p1 q1 = 0)
          ·
            by_cases hY71 : (ip a7 b7 p2 q2 = 0 ∧ ip a7 b7 p3 q3 = 0)
            ·
              by_cases hY72 : (ip a7 b7 p4 q4 = 0 ∧ ip a7 b7 p5 q5 = 0)
              ·
                exact no77_01 ⟨hY70, hY71⟩
              ·
                exact no77_01 ⟨hY70, hY71⟩
            ·
              by_cases hY72 : (ip a7 b7 p4 q4 = 0 ∧ ip a7 b7 p5 q5 = 0)
              ·
                exact no77_02 ⟨hY70, hY72⟩
              ·
                have H := branch3_aligned (ip a7 b7 p0 q0) (ip a7 b7 p1 q1) (ip a7 b7 p2 q2) (ip a7 b7 p3 q3) (ip a7 b7 p4 q4) (ip a7 b7 p5 q5) (ip a6 b6 p0 q0) (ip a6 b6 p1 q1) (ip a6 b6 p2 q2) (ip a6 b6 p3 q3) (ip a6 b6 p4 q4) (ip a6 b6 p5 q5)
                  hY70.1 hY70.2 hY71 hY72 hY60
                  (by simp only [Jform] at A7_12 ⊢; linear_combination A7_12)
                  (by simp only [Jform] at A6_01 ⊢; linear_combination A6_01)
                  (by simp only [Jform] at A6_02 ⊢; linear_combination A6_02)
                  (by simp only [Jform] at C_01 ⊢; linear_combination C_01)
                  (by simp only [Jform] at C_02 ⊢; linear_combination C_02)
                rcases H with ⟨m7_1, m7_3, m7_5, m6_1, m6_3, m6_5⟩ | ⟨m7_0, m7_2, m7_4, m6_0, m6_2, m6_4⟩
                · exact closeA (Or.inl ⟨m6_1, m6_3, m6_5, m7_1, m7_3, m7_5⟩)
                · exact closeA (Or.inr ⟨m6_0, m6_2, m6_4, m7_0, m7_2, m7_4⟩)
          ·
            by_cases hY71 : (ip a7 b7 p2 q2 = 0 ∧ ip a7 b7 p3 q3 = 0)
            ·
              by_cases hY72 : (ip a7 b7 p4 q4 = 0 ∧ ip a7 b7 p5 q5 = 0)
              ·
                exact no77_12 ⟨hY71, hY72⟩
              ·
                have H := branch3_aligned (ip a7 b7 p2 q2) (ip a7 b7 p3 q3) (ip a7 b7 p0 q0) (ip a7 b7 p1 q1) (ip a7 b7 p4 q4) (ip a7 b7 p5 q5) (ip a6 b6 p2 q2) (ip a6 b6 p3 q3) (ip a6 b6 p0 q0) (ip a6 b6 p1 q1) (ip a6 b6 p4 q4) (ip a6 b6 p5 q5)
                  hY71.1 hY71.2 hY70 hY72 hY61
                  (by simp only [Jform] at A7_02 ⊢; linear_combination A7_02)
                  (by simp only [Jform] at A6_01 ⊢; linear_combination A6_01)
                  (by simp only [Jform] at A6_12 ⊢; linear_combination A6_12)
                  (by simp only [Jform] at C_01 ⊢; linear_combination C_01)
                  (by simp only [Jform] at C_12 ⊢; linear_combination C_12)
                rcases H with ⟨m7_3, m7_1, m7_5, m6_3, m6_1, m6_5⟩ | ⟨m7_2, m7_0, m7_4, m6_2, m6_0, m6_4⟩
                · exact closeA (Or.inl ⟨m6_1, m6_3, m6_5, m7_1, m7_3, m7_5⟩)
                · exact closeA (Or.inr ⟨m6_0, m6_2, m6_4, m7_0, m7_2, m7_4⟩)
            ·
              by_cases hY72 : (ip a7 b7 p4 q4 = 0 ∧ ip a7 b7 p5 q5 = 0)
              ·
                have H := branch3_aligned (ip a7 b7 p4 q4) (ip a7 b7 p5 q5) (ip a7 b7 p0 q0) (ip a7 b7 p1 q1) (ip a7 b7 p2 q2) (ip a7 b7 p3 q3) (ip a6 b6 p4 q4) (ip a6 b6 p5 q5) (ip a6 b6 p0 q0) (ip a6 b6 p1 q1) (ip a6 b6 p2 q2) (ip a6 b6 p3 q3)
                  hY72.1 hY72.2 hY70 hY71 hY62
                  (by simp only [Jform] at A7_01 ⊢; linear_combination A7_01)
                  (by simp only [Jform] at A6_02 ⊢; linear_combination A6_02)
                  (by simp only [Jform] at A6_12 ⊢; linear_combination A6_12)
                  (by simp only [Jform] at C_02 ⊢; linear_combination C_02)
                  (by simp only [Jform] at C_12 ⊢; linear_combination C_12)
                rcases H with ⟨m7_5, m7_1, m7_3, m6_5, m6_1, m6_3⟩ | ⟨m7_4, m7_0, m7_2, m6_4, m6_0, m6_2⟩
                · exact closeA (Or.inl ⟨m6_1, m6_3, m6_5, m7_1, m7_3, m7_5⟩)
                · exact closeA (Or.inr ⟨m6_0, m6_2, m6_4, m7_0, m7_2, m7_4⟩)
              ·
                have H := branch4_aligned (ip a6 b6 p0 q0) (ip a6 b6 p1 q1) (ip a6 b6 p2 q2) (ip a6 b6 p3 q3) (ip a6 b6 p4 q4) (ip a6 b6 p5 q5) (ip a7 b7 p0 q0) (ip a7 b7 p1 q1) (ip a7 b7 p2 q2) (ip a7 b7 p3 q3) (ip a7 b7 p4 q4) (ip a7 b7 p5 q5)
                  hY60 hY61 hY62 hY70 hY71 hY72
                  (by simp only [Jform] at A6_01 ⊢; linear_combination A6_01) (by simp only [Jform] at A6_02 ⊢; linear_combination A6_02) (by simp only [Jform] at A6_12 ⊢; linear_combination A6_12)
                  (by simp only [Jform] at A7_01 ⊢; linear_combination A7_01) (by simp only [Jform] at A7_02 ⊢; linear_combination A7_02) (by simp only [Jform] at A7_12 ⊢; linear_combination A7_12)
                  (by simp only [Jform] at C_01 ⊢; linear_combination C_01) (by simp only [Jform] at C_02 ⊢; linear_combination C_02) (by simp only [Jform] at C_12 ⊢; linear_combination C_12)
                rcases H with ⟨m6_1, m6_3, m6_5, m7_1, m7_3, m7_5⟩ | ⟨m6_0, m6_2, m6_4, m7_0, m7_2, m7_4⟩
                · exact closeA (Or.inl ⟨m6_1, m6_3, m6_5, m7_1, m7_3, m7_5⟩)
                · exact closeA (Or.inr ⟨m6_0, m6_2, m6_4, m7_0, m7_2, m7_4⟩)

set_option maxHeartbeats 4000000 in
/-- **Headline.**  The Knill-Laflamme system for orbit 26 has no solution. -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11)) (Complex.normSq (c y12)) (Complex.normSq (c y13)) (Complex.normSq (c y14)) (Complex.normSq (c y15)) (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)) (Complex.normSq (d z12)) (Complex.normSq (d z13)) (Complex.normSq (d z14)) (Complex.normSq (d z15)))
    (hO1_0 : offSum c d ef1 w0 = 0)
    (hO1_6 : offSum c d ef1 w6 = 0)
    (hO2_0 : offSum c d ef2 w0 = 0)
    (hO2_2 : offSum c d ef2 w2 = 0)
    (hO3_0 : offSum c d ef3 w0 = 0)
    (hO3_3 : offSum c d ef3 w3 = 0)
    (hO4_0 : offSum c d ef4 w0 = 0)
    (hO4_6 : offSum c d ef4 w6 = 0)
    (hO5_0 : offSum c d ef5 w0 = 0)
    (hO5_2 : offSum c d ef5 w2 = 0)
    (hO6_0 : offSum c d ef6 w0 = 0)
    (hO6_3 : offSum c d ef6 w3 = 0)
    (hO7_0 : offSum c d ef7 w0 = 0)
    (hO7_6 : offSum c d ef7 w6 = 0)
    (hO8_0 : offSum c d ef8 w0 = 0)
    (hO8_2 : offSum c d ef8 w2 = 0)
    (hO9_0 : offSum c d ef9 w0 = 0)
    (hO9_3 : offSum c d ef9 w3 = 0)
    (hO11_0 : offSum c d ef11 w0 = 0)
    (hO11_6 : offSum c d ef11 w6 = 0)
    (hO12_0 : offSum c d ef12 w0 = 0)
    (hO12_6 : offSum c d ef12 w6 = 0)
    (hO13_0 : offSum c d ef13 w0 = 0)
    (hO13_6 : offSum c d ef13 w6 = 0)
    (hD0_0 : diagBot c ef0 w0 = diagTop d ef0 w0)
    (hD0_5 : diagBot c ef0 w5 = diagTop d ef0 w5)
    (hD0_4 : diagBot c ef0 w4 = diagTop d ef0 w4)
    (hD0_1 : diagBot c ef0 w1 = diagTop d ef0 w1)
    (hD0_6 : diagBot c ef0 w6 = diagTop d ef0 w6)
    (hD0_9 : diagBot c ef0 w9 = diagTop d ef0 w9)
    (hD0_8 : diagBot c ef0 w8 = diagTop d ef0 w8)
    (hD0_7 : diagBot c ef0 w7 = diagTop d ef0 w7)
    (hD10_0 : diagBot c ef10 w0 = diagTop d ef10 w0)
    (hD10_5 : diagBot c ef10 w5 = diagTop d ef10 w5)
    (hD10_4 : diagBot c ef10 w4 = diagTop d ef10 w4)
    (hD10_1 : diagBot c ef10 w1 = diagTop d ef10 w1)
    (hD10_6 : diagBot c ef10 w6 = diagTop d ef10 w6)
    (hD10_9 : diagBot c ef10 w9 = diagTop d ef10 w9)
    (hD10_8 : diagBot c ef10 w8 = diagTop d ef10 w8)
    (hD10_7 : diagBot c ef10 w7 = diagTop d ef10 w7)
    : False := by
  exact core
    (c y0) (c y1) (c y2) (c y3) (c y4) (c y5) (c y6) (c y7)
    (c y8) (c y9) (c y10) (c y11) (c y12) (c y13) (c y14) (c y15)
    (d z7) (d z6) (d z5) (d z4) (d z3) (d z2) (d z1) (d z0)
    (d z15) (d z14) (d z13) (d z12) (d z11) (d z10) (d z9) (d z8)
    (by linarith only [mPQ0 hm])
    (by linarith only [mPQ1 hm])
    (by linarith only [mPQ2 hm])
    (by linarith only [mPQ3 hm])
    (by linarith only [mPQ4 hm])
    (by linarith only [mPQ5 hm])
    (by linarith only [mPQ6 hm])
    (by linarith only [mPQ7 hm])
    (by linarith only [mP6 hm])
    (by linarith only [mP7 hm])
    (by linarith only [mT0 hm])
    (by linarith only [mT1 hm])
    (by linarith only [mT2 hm])
    (by linarith only [mT2a hm])
    (by linarith only [mT2b hm])
    (outer_g0h1_a0b0 c d hO7_0 hO7_6)
    (outer_g0h1_a0b1 c d hO13_0 hO13_6)
    (outer_g0h1_a1b0 c d hO13_0 hO13_6)
    (outer_g0h1_a1b1 c d hO7_0 hO7_6)
    (outer_g0h2_a0b0 c d hO4_0 hO4_6)
    (outer_g0h2_a0b1 c d hO12_0 hO12_6)
    (outer_g0h2_a1b0 c d hO12_0 hO12_6)
    (outer_g0h2_a1b1 c d hO4_0 hO4_6)
    (outer_g1h2_a0b0 c d hO1_0 hO1_6)
    (outer_g1h2_a0b1 c d hO11_0 hO11_6)
    (outer_g1h2_a1b0 c d hO11_0 hO11_6)
    (outer_g1h2_a1b1 c d hO1_0 hO1_6)
    (by rw [ip_eq, ip_eq]; linear_combination anch_i0_j6 c d hO3_0 hO3_3)
    (by rw [ip_eq, ip_eq]; linear_combination anch_i0_j7 c d hO2_0 hO2_2)
    (by rw [ip_eq, ip_eq]; linear_combination anch_i1_j6 c d hO2_0 hO2_2)
    (by rw [ip_eq, ip_eq]; linear_combination anch_i1_j7 c d hO3_0 hO3_3)
    (by rw [ip_eq, ip_eq]; linear_combination anch_i2_j6 c d hO6_0 hO6_3)
    (by rw [ip_eq, ip_eq]; linear_combination anch_i2_j7 c d hO5_0 hO5_2)
    (by rw [ip_eq, ip_eq]; linear_combination anch_i3_j6 c d hO5_0 hO5_2)
    (by rw [ip_eq, ip_eq]; linear_combination anch_i3_j7 c d hO6_0 hO6_3)
    (by rw [ip_eq, ip_eq]; linear_combination anch_i4_j6 c d hO9_0 hO9_3)
    (by rw [ip_eq, ip_eq]; linear_combination anch_i4_j7 c d hO8_0 hO8_2)
    (by rw [ip_eq, ip_eq]; linear_combination anch_i5_j6 c d hO8_0 hO8_2)
    (by rw [ip_eq, ip_eq]; linear_combination anch_i5_j7 c d hO9_0 hO9_3)
    (mom_g0_a0b0 c d hD0_0 hD0_5 hD0_4 hD0_1 hD0_6 hD0_9 hD0_8 hD0_7)
    (mom_g0_a0b1 c d hD10_0 hD10_5 hD10_4 hD10_1 hD10_6 hD10_9 hD10_8 hD10_7)
    (mom_g0_a1b0 c d hD10_0 hD10_5 hD10_4 hD10_1 hD10_6 hD10_9 hD10_8 hD10_7)
    (mom_g0_a1b1 c d hD0_0 hD0_5 hD0_4 hD0_1 hD0_6 hD0_9 hD0_8 hD0_7)
    (mom_g1_a0b0 c d hD0_0 hD0_5 hD0_4 hD0_1 hD0_6 hD0_9 hD0_8 hD0_7)
    (mom_g1_a0b1 c d hD10_0 hD10_5 hD10_4 hD10_1 hD10_6 hD10_9 hD10_8 hD10_7)
    (mom_g1_a1b0 c d hD10_0 hD10_5 hD10_4 hD10_1 hD10_6 hD10_9 hD10_8 hD10_7)
    (mom_g1_a1b1 c d hD0_0 hD0_5 hD0_4 hD0_1 hD0_6 hD0_9 hD0_8 hD0_7)
    (mom_g2_a0b0 c d hD0_0 hD0_5 hD0_4 hD0_1 hD0_6 hD0_9 hD0_8 hD0_7)
    (mom_g2_a0b1 c d hD10_0 hD10_5 hD10_4 hD10_1 hD10_6 hD10_9 hD10_8 hD10_7)
    (mom_g2_a1b0 c d hD10_0 hD10_5 hD10_4 hD10_1 hD10_6 hD10_9 hD10_8 hD10_7)
    (mom_g2_a1b1 c d hD0_0 hD0_5 hD0_4 hD0_1 hD0_6 hD0_9 hD0_8 hD0_7)
    (mom_g3_a0b0 c d hD0_0 hD0_5 hD0_4 hD0_1 hD0_6 hD0_9 hD0_8 hD0_7)
    (mom_g3_a0b1 c d hD10_0 hD10_5 hD10_4 hD10_1 hD10_6 hD10_9 hD10_8 hD10_7)
    (mom_g3_a1b0 c d hD10_0 hD10_5 hD10_4 hD10_1 hD10_6 hD10_9 hD10_8 hD10_7)
    (mom_g3_a1b1 c d hD0_0 hD0_5 hD0_4 hD0_1 hD0_6 hD0_9 hD0_8 hD0_7)

end

end SixQubit.Orbit26
