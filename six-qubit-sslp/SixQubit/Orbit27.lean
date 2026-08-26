import Mathlib

import SS.FullKL
import SixQubit.Common

/-!
# Six-qubit no-go for moment orbit 27

Orbit 27 of `six_qubit_sslp_v7.tex`: q = 4, angle vector
a = (1, 1, 1, 1, 1, 1), residues 0 and 1, closed in Section 15.

No single Walsh system kills this orbit.  The certificate is a chain:

* with those eliminated, 6 Walsh systems each force one product to
  vanish, and each pairs with an anchor probability that the polytope
  forces strictly positive, turning it into a vanishing amplitude;
* the moment polytope carrying all 6 zeros is infeasible.

Everything computational is decided by the Lean kernel; `native_decide` is
not used.
-/

namespace SixQubit.Orbit27

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
def y6 : SS.BitString 6 := bs true  false false true  true  true   -- 100111
def y7 : SS.BitString 6 := bs true  false true  false true  true   -- 101011
def y8 : SS.BitString 6 := bs true  false true  true  false true   -- 101101
def y9 : SS.BitString 6 := bs true  false true  true  true  false  -- 101110
def y10 : SS.BitString 6 := bs true  true  false false true  true   -- 110011
def y11 : SS.BitString 6 := bs true  true  false true  false true   -- 110101
def y12 : SS.BitString 6 := bs true  true  false true  true  false  -- 110110
def y13 : SS.BitString 6 := bs true  true  true  false false true   -- 111001
def y14 : SS.BitString 6 := bs true  true  true  false true  false  -- 111010
def y15 : SS.BitString 6 := bs true  true  true  true  false false  -- 111100

def z0 : SS.BitString 6 := bs false false false false false true   -- 000001
def z1 : SS.BitString 6 := bs false false false false true  false  -- 000010
def z2 : SS.BitString 6 := bs false false false true  false false  -- 000100
def z3 : SS.BitString 6 := bs false false true  false false false  -- 001000
def z4 : SS.BitString 6 := bs false true  false false false false  -- 010000
def z5 : SS.BitString 6 := bs false true  true  true  true  true   -- 011111
def z6 : SS.BitString 6 := bs true  false false false false false  -- 100000
def z7 : SS.BitString 6 := bs true  false true  true  true  true   -- 101111
def z8 : SS.BitString 6 := bs true  true  false true  true  true   -- 110111
def z9 : SS.BitString 6 := bs true  true  true  false true  true   -- 111011
def z10 : SS.BitString 6 := bs true  true  true  true  false true   -- 111101
def z11 : SS.BitString 6 := bs true  true  true  true  true  false  -- 111110

def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15}
def S1 : Finset (SS.BitString 6) := {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11}

def av : Fin 6 -> ZMod 4 := ![1, 1, 1, 1, 1, 1]

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

/-- The two normalizations, the twenty-one moment equalities, and the
nonnegativity of every probability. -/
structure MomentSystem (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 : Real) : Prop where
  n0 : q0 + q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 + q9 + q10 + q11 + q12 + q13 + q14 + q15 = 1
  n1 : r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 = 1
  m1 : q6 + q7 + q8 + q9 + q10 + q11 + q12 + q13 + q14 + q15 = r6 + r7 + r8 + r9 + r10 + r11
  m2 : q2 + q3 + q4 + q5 + q10 + q11 + q12 + q13 + q14 + q15 = r4 + r5 + r8 + r9 + r10 + r11
  m3 : q1 + q3 + q4 + q5 + q7 + q8 + q9 + q13 + q14 + q15 = r3 + r5 + r7 + r9 + r10 + r11
  m4 : q1 + q2 + q4 + q5 + q6 + q8 + q9 + q11 + q12 + q15 = r2 + r5 + r7 + r8 + r10 + r11
  m5 : q1 + q2 + q3 + q5 + q6 + q7 + q9 + q10 + q12 + q14 = r1 + r5 + r7 + r8 + r9 + r11
  m6 : q1 + q2 + q3 + q4 + q6 + q7 + q8 + q10 + q11 + q13 = r0 + r5 + r7 + r8 + r9 + r10
  c12 : q10 + q11 + q12 + q13 + q14 + q15 = r8 + r9 + r10 + r11
  c13 : q7 + q8 + q9 + q13 + q14 + q15 = r7 + r9 + r10 + r11
  c14 : q6 + q8 + q9 + q11 + q12 + q15 = r7 + r8 + r10 + r11
  c15 : q6 + q7 + q9 + q10 + q12 + q14 = r7 + r8 + r9 + r11
  c16 : q6 + q7 + q8 + q10 + q11 + q13 = r7 + r8 + r9 + r10
  c23 : q3 + q4 + q5 + q13 + q14 + q15 = r5 + r9 + r10 + r11
  c24 : q2 + q4 + q5 + q11 + q12 + q15 = r5 + r8 + r10 + r11
  c25 : q2 + q3 + q5 + q10 + q12 + q14 = r5 + r8 + r9 + r11
  c26 : q2 + q3 + q4 + q10 + q11 + q13 = r5 + r8 + r9 + r10
  c34 : q1 + q4 + q5 + q8 + q9 + q15 = r5 + r7 + r10 + r11
  c35 : q1 + q3 + q5 + q7 + q9 + q14 = r5 + r7 + r9 + r11
  c36 : q1 + q3 + q4 + q7 + q8 + q13 = r5 + r7 + r9 + r10
  c45 : q1 + q2 + q5 + q6 + q9 + q12 = r5 + r7 + r8 + r11
  c46 : q1 + q2 + q4 + q6 + q8 + q11 = r5 + r7 + r8 + r10
  c56 : q1 + q2 + q3 + q6 + q7 + q10 = r5 + r7 + r8 + r9

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

/-- The anchor probabilities the chain uses are strictly positive. -/
theorem MomentSystem.anchors {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 : Real}
    (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11) :
    0 < q0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11⟩ := h
  linarith

/-- Stage 2: the polytope carrying every derived zero is infeasible. -/
theorem MomentSystem.infeasible {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 : Real}
    (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11)
    (v16 : r0 = 0)
    (v17 : r1 = 0)
    (v18 : r2 = 0)
    (v19 : r3 = 0)
    (v20 : r4 = 0)
    (v22 : r6 = 0)
    : False := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11⟩ := h
  linarith

/-! ## The Walsh systems -/

def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),
      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

theorem signMul_zero (b : Bool) : SixQubit.signMul b (0 : ℂ) = 0 := by
  cases b <;> simp [SixQubit.signMul]

/-- System 0: flip 100000. -/
def ef0 : SS.BitString 6 := bs true  false false false false false
def w0_0 : SS.BitString 6 := bs false false false false false false  -- dressing 000000
def w0_1 : SS.BitString 6 := bs false true  false false false false  -- dressing 010000
def w0_2 : SS.BitString 6 := bs false false true  false false false  -- dressing 001000
def w0_3 : SS.BitString 6 := bs false false false true  false false  -- dressing 000100
def w0_4 : SS.BitString 6 := bs false false false false true  false  -- dressing 000010
def w0_5 : SS.BitString 6 := bs false false false false false true   -- dressing 000001

theorem incidence0 :
    S1.filter (fun y => SS.bxor y ef0 ∈ S0) = {z6, z7, z8, z9, z10, z11} := by decide
theorem fl0_6 : SS.bxor z6 ef0 = y0 := by decide
theorem fl0_7 : SS.bxor z7 ef0 = y1 := by decide
theorem fl0_8 : SS.bxor z8 ef0 = y2 := by decide
theorem fl0_9 : SS.bxor z9 ef0 = y3 := by decide
theorem fl0_10 : SS.bxor z10 ef0 = y4 := by decide
theorem fl0_11 : SS.bxor z11 ef0 = y5 := by decide
theorem sg0_0_6 : SS.bdot w0_0 z6 = false := by decide
theorem sg0_0_7 : SS.bdot w0_0 z7 = false := by decide
theorem sg0_0_8 : SS.bdot w0_0 z8 = false := by decide
theorem sg0_0_9 : SS.bdot w0_0 z9 = false := by decide
theorem sg0_0_10 : SS.bdot w0_0 z10 = false := by decide
theorem sg0_0_11 : SS.bdot w0_0 z11 = false := by decide
theorem sg0_1_6 : SS.bdot w0_1 z6 = false := by decide
theorem sg0_1_7 : SS.bdot w0_1 z7 = false := by decide
theorem sg0_1_8 : SS.bdot w0_1 z8 = true := by decide
theorem sg0_1_9 : SS.bdot w0_1 z9 = true := by decide
theorem sg0_1_10 : SS.bdot w0_1 z10 = true := by decide
theorem sg0_1_11 : SS.bdot w0_1 z11 = true := by decide
theorem sg0_2_6 : SS.bdot w0_2 z6 = false := by decide
theorem sg0_2_7 : SS.bdot w0_2 z7 = true := by decide
theorem sg0_2_8 : SS.bdot w0_2 z8 = false := by decide
theorem sg0_2_9 : SS.bdot w0_2 z9 = true := by decide
theorem sg0_2_10 : SS.bdot w0_2 z10 = true := by decide
theorem sg0_2_11 : SS.bdot w0_2 z11 = true := by decide
theorem sg0_3_6 : SS.bdot w0_3 z6 = false := by decide
theorem sg0_3_7 : SS.bdot w0_3 z7 = true := by decide
theorem sg0_3_8 : SS.bdot w0_3 z8 = true := by decide
theorem sg0_3_9 : SS.bdot w0_3 z9 = false := by decide
theorem sg0_3_10 : SS.bdot w0_3 z10 = true := by decide
theorem sg0_3_11 : SS.bdot w0_3 z11 = true := by decide
theorem sg0_4_6 : SS.bdot w0_4 z6 = false := by decide
theorem sg0_4_7 : SS.bdot w0_4 z7 = true := by decide
theorem sg0_4_8 : SS.bdot w0_4 z8 = true := by decide
theorem sg0_4_9 : SS.bdot w0_4 z9 = true := by decide
theorem sg0_4_10 : SS.bdot w0_4 z10 = false := by decide
theorem sg0_4_11 : SS.bdot w0_4 z11 = true := by decide
theorem sg0_5_6 : SS.bdot w0_5 z6 = false := by decide
theorem sg0_5_7 : SS.bdot w0_5 z7 = true := by decide
theorem sg0_5_8 : SS.bdot w0_5 z8 = true := by decide
theorem sg0_5_9 : SS.bdot w0_5 z9 = true := by decide
theorem sg0_5_10 : SS.bdot w0_5 z10 = true := by decide
theorem sg0_5_11 : SS.bdot w0_5 z11 = false := by decide

theorem ex0_0 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef0 w0_0 = star (c y0) * d z6 + star (c y1) * d z7 + star (c y2) * d z8 + star (c y3) * d z9 + star (c y4) * d z10 + star (c y5) * d z11 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_6, fl0_7, fl0_8, fl0_9, fl0_10, fl0_11]
  simp only [sg0_0_6, sg0_0_7, sg0_0_8, sg0_0_9, sg0_0_10, sg0_0_11, SixQubit.signMul_false]
  try ring

theorem ex0_1 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef0 w0_1 = star (c y0) * d z6 + star (c y1) * d z7 - star (c y2) * d z8 - star (c y3) * d z9 - star (c y4) * d z10 - star (c y5) * d z11 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_6, fl0_7, fl0_8, fl0_9, fl0_10, fl0_11]
  simp only [sg0_1_6, sg0_1_7, sg0_1_8, sg0_1_9, sg0_1_10, sg0_1_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex0_2 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef0 w0_2 = star (c y0) * d z6 - star (c y1) * d z7 + star (c y2) * d z8 - star (c y3) * d z9 - star (c y4) * d z10 - star (c y5) * d z11 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_6, fl0_7, fl0_8, fl0_9, fl0_10, fl0_11]
  simp only [sg0_2_6, sg0_2_7, sg0_2_8, sg0_2_9, sg0_2_10, sg0_2_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex0_3 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef0 w0_3 = star (c y0) * d z6 - star (c y1) * d z7 - star (c y2) * d z8 + star (c y3) * d z9 - star (c y4) * d z10 - star (c y5) * d z11 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_6, fl0_7, fl0_8, fl0_9, fl0_10, fl0_11]
  simp only [sg0_3_6, sg0_3_7, sg0_3_8, sg0_3_9, sg0_3_10, sg0_3_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex0_4 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef0 w0_4 = star (c y0) * d z6 - star (c y1) * d z7 - star (c y2) * d z8 - star (c y3) * d z9 + star (c y4) * d z10 - star (c y5) * d z11 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_6, fl0_7, fl0_8, fl0_9, fl0_10, fl0_11]
  simp only [sg0_4_6, sg0_4_7, sg0_4_8, sg0_4_9, sg0_4_10, sg0_4_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex0_5 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef0 w0_5 = star (c y0) * d z6 - star (c y1) * d z7 - star (c y2) * d z8 - star (c y3) * d z9 - star (c y4) * d z10 + star (c y5) * d z11 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_6, fl0_7, fl0_8, fl0_9, fl0_10, fl0_11]
  simp only [sg0_5_6, sg0_5_7, sg0_5_8, sg0_5_9, sg0_5_10, sg0_5_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

/-- System 0 forces this product to vanish. -/
theorem tz0 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef0 w0_0 = 0)
    (h1 : offSum c d ef0 w0_1 = 0)
    (h2 : offSum c d ef0 w0_2 = 0)
    (h3 : offSum c d ef0 w0_3 = 0)
    (h4 : offSum c d ef0 w0_4 = 0)
    (h5 : offSum c d ef0 w0_5 = 0)
    : star (c y0) * d z6 = 0 := by
  rw [ex0_0 c d ] at h0
  rw [ex0_1 c d ] at h1
  rw [ex0_2 c d ] at h2
  rw [ex0_3 c d ] at h3
  rw [ex0_4 c d ] at h4
  rw [ex0_5 c d ] at h5
  linear_combination ((3 / 8) : ℂ) * h0 + ((1 / 8) : ℂ) * h1 + ((1 / 8) : ℂ) * h2 + ((1 / 8) : ℂ) * h3 + ((1 / 8) : ℂ) * h4 + ((1 / 8) : ℂ) * h5

/-- System 1: flip 010000. -/
def ef1 : SS.BitString 6 := bs false true  false false false false
def w1_0 : SS.BitString 6 := bs false false false false false false  -- dressing 000000
def w1_1 : SS.BitString 6 := bs true  false false false false false  -- dressing 100000
def w1_2 : SS.BitString 6 := bs false false true  false false false  -- dressing 001000
def w1_3 : SS.BitString 6 := bs false false false true  false false  -- dressing 000100
def w1_4 : SS.BitString 6 := bs false false false false true  false  -- dressing 000010
def w1_5 : SS.BitString 6 := bs false false false false false true   -- dressing 000001

theorem incidence1 :
    S1.filter (fun y => SS.bxor y ef1 ∈ S0) = {z4, z5, z8, z9, z10, z11} := by decide
theorem fl1_4 : SS.bxor z4 ef1 = y0 := by decide
theorem fl1_5 : SS.bxor z5 ef1 = y1 := by decide
theorem fl1_8 : SS.bxor z8 ef1 = y6 := by decide
theorem fl1_9 : SS.bxor z9 ef1 = y7 := by decide
theorem fl1_10 : SS.bxor z10 ef1 = y8 := by decide
theorem fl1_11 : SS.bxor z11 ef1 = y9 := by decide
theorem sg1_0_4 : SS.bdot w1_0 z4 = false := by decide
theorem sg1_0_5 : SS.bdot w1_0 z5 = false := by decide
theorem sg1_0_8 : SS.bdot w1_0 z8 = false := by decide
theorem sg1_0_9 : SS.bdot w1_0 z9 = false := by decide
theorem sg1_0_10 : SS.bdot w1_0 z10 = false := by decide
theorem sg1_0_11 : SS.bdot w1_0 z11 = false := by decide
theorem sg1_1_4 : SS.bdot w1_1 z4 = false := by decide
theorem sg1_1_5 : SS.bdot w1_1 z5 = false := by decide
theorem sg1_1_8 : SS.bdot w1_1 z8 = true := by decide
theorem sg1_1_9 : SS.bdot w1_1 z9 = true := by decide
theorem sg1_1_10 : SS.bdot w1_1 z10 = true := by decide
theorem sg1_1_11 : SS.bdot w1_1 z11 = true := by decide
theorem sg1_2_4 : SS.bdot w1_2 z4 = false := by decide
theorem sg1_2_5 : SS.bdot w1_2 z5 = true := by decide
theorem sg1_2_8 : SS.bdot w1_2 z8 = false := by decide
theorem sg1_2_9 : SS.bdot w1_2 z9 = true := by decide
theorem sg1_2_10 : SS.bdot w1_2 z10 = true := by decide
theorem sg1_2_11 : SS.bdot w1_2 z11 = true := by decide
theorem sg1_3_4 : SS.bdot w1_3 z4 = false := by decide
theorem sg1_3_5 : SS.bdot w1_3 z5 = true := by decide
theorem sg1_3_8 : SS.bdot w1_3 z8 = true := by decide
theorem sg1_3_9 : SS.bdot w1_3 z9 = false := by decide
theorem sg1_3_10 : SS.bdot w1_3 z10 = true := by decide
theorem sg1_3_11 : SS.bdot w1_3 z11 = true := by decide
theorem sg1_4_4 : SS.bdot w1_4 z4 = false := by decide
theorem sg1_4_5 : SS.bdot w1_4 z5 = true := by decide
theorem sg1_4_8 : SS.bdot w1_4 z8 = true := by decide
theorem sg1_4_9 : SS.bdot w1_4 z9 = true := by decide
theorem sg1_4_10 : SS.bdot w1_4 z10 = false := by decide
theorem sg1_4_11 : SS.bdot w1_4 z11 = true := by decide
theorem sg1_5_4 : SS.bdot w1_5 z4 = false := by decide
theorem sg1_5_5 : SS.bdot w1_5 z5 = true := by decide
theorem sg1_5_8 : SS.bdot w1_5 z8 = true := by decide
theorem sg1_5_9 : SS.bdot w1_5 z9 = true := by decide
theorem sg1_5_10 : SS.bdot w1_5 z10 = true := by decide
theorem sg1_5_11 : SS.bdot w1_5 z11 = false := by decide

theorem ex1_0 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef1 w1_0 = star (c y0) * d z4 + star (c y1) * d z5 + star (c y6) * d z8 + star (c y7) * d z9 + star (c y8) * d z10 + star (c y9) * d z11 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_4, fl1_5, fl1_8, fl1_9, fl1_10, fl1_11]
  simp only [sg1_0_4, sg1_0_5, sg1_0_8, sg1_0_9, sg1_0_10, sg1_0_11, SixQubit.signMul_false]
  try ring

theorem ex1_1 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef1 w1_1 = star (c y0) * d z4 + star (c y1) * d z5 - star (c y6) * d z8 - star (c y7) * d z9 - star (c y8) * d z10 - star (c y9) * d z11 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_4, fl1_5, fl1_8, fl1_9, fl1_10, fl1_11]
  simp only [sg1_1_4, sg1_1_5, sg1_1_8, sg1_1_9, sg1_1_10, sg1_1_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex1_2 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef1 w1_2 = star (c y0) * d z4 - star (c y1) * d z5 + star (c y6) * d z8 - star (c y7) * d z9 - star (c y8) * d z10 - star (c y9) * d z11 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_4, fl1_5, fl1_8, fl1_9, fl1_10, fl1_11]
  simp only [sg1_2_4, sg1_2_5, sg1_2_8, sg1_2_9, sg1_2_10, sg1_2_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex1_3 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef1 w1_3 = star (c y0) * d z4 - star (c y1) * d z5 - star (c y6) * d z8 + star (c y7) * d z9 - star (c y8) * d z10 - star (c y9) * d z11 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_4, fl1_5, fl1_8, fl1_9, fl1_10, fl1_11]
  simp only [sg1_3_4, sg1_3_5, sg1_3_8, sg1_3_9, sg1_3_10, sg1_3_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex1_4 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef1 w1_4 = star (c y0) * d z4 - star (c y1) * d z5 - star (c y6) * d z8 - star (c y7) * d z9 + star (c y8) * d z10 - star (c y9) * d z11 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_4, fl1_5, fl1_8, fl1_9, fl1_10, fl1_11]
  simp only [sg1_4_4, sg1_4_5, sg1_4_8, sg1_4_9, sg1_4_10, sg1_4_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex1_5 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef1 w1_5 = star (c y0) * d z4 - star (c y1) * d z5 - star (c y6) * d z8 - star (c y7) * d z9 - star (c y8) * d z10 + star (c y9) * d z11 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_4, fl1_5, fl1_8, fl1_9, fl1_10, fl1_11]
  simp only [sg1_5_4, sg1_5_5, sg1_5_8, sg1_5_9, sg1_5_10, sg1_5_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

/-- System 1 forces this product to vanish. -/
theorem tz1 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef1 w1_0 = 0)
    (h1 : offSum c d ef1 w1_1 = 0)
    (h2 : offSum c d ef1 w1_2 = 0)
    (h3 : offSum c d ef1 w1_3 = 0)
    (h4 : offSum c d ef1 w1_4 = 0)
    (h5 : offSum c d ef1 w1_5 = 0)
    : star (c y0) * d z4 = 0 := by
  rw [ex1_0 c d ] at h0
  rw [ex1_1 c d ] at h1
  rw [ex1_2 c d ] at h2
  rw [ex1_3 c d ] at h3
  rw [ex1_4 c d ] at h4
  rw [ex1_5 c d ] at h5
  linear_combination ((3 / 8) : ℂ) * h0 + ((1 / 8) : ℂ) * h1 + ((1 / 8) : ℂ) * h2 + ((1 / 8) : ℂ) * h3 + ((1 / 8) : ℂ) * h4 + ((1 / 8) : ℂ) * h5

/-- System 2: flip 001000. -/
def ef2 : SS.BitString 6 := bs false false true  false false false
def w2_0 : SS.BitString 6 := bs false false false false false false  -- dressing 000000
def w2_1 : SS.BitString 6 := bs true  false false false false false  -- dressing 100000
def w2_2 : SS.BitString 6 := bs false true  false false false false  -- dressing 010000
def w2_3 : SS.BitString 6 := bs false false false true  false false  -- dressing 000100
def w2_4 : SS.BitString 6 := bs false false false false true  false  -- dressing 000010
def w2_5 : SS.BitString 6 := bs false false false false false true   -- dressing 000001

theorem incidence2 :
    S1.filter (fun y => SS.bxor y ef2 ∈ S0) = {z3, z5, z7, z9, z10, z11} := by decide
theorem fl2_3 : SS.bxor z3 ef2 = y0 := by decide
theorem fl2_5 : SS.bxor z5 ef2 = y2 := by decide
theorem fl2_7 : SS.bxor z7 ef2 = y6 := by decide
theorem fl2_9 : SS.bxor z9 ef2 = y10 := by decide
theorem fl2_10 : SS.bxor z10 ef2 = y11 := by decide
theorem fl2_11 : SS.bxor z11 ef2 = y12 := by decide
theorem sg2_0_3 : SS.bdot w2_0 z3 = false := by decide
theorem sg2_0_5 : SS.bdot w2_0 z5 = false := by decide
theorem sg2_0_7 : SS.bdot w2_0 z7 = false := by decide
theorem sg2_0_9 : SS.bdot w2_0 z9 = false := by decide
theorem sg2_0_10 : SS.bdot w2_0 z10 = false := by decide
theorem sg2_0_11 : SS.bdot w2_0 z11 = false := by decide
theorem sg2_1_3 : SS.bdot w2_1 z3 = false := by decide
theorem sg2_1_5 : SS.bdot w2_1 z5 = false := by decide
theorem sg2_1_7 : SS.bdot w2_1 z7 = true := by decide
theorem sg2_1_9 : SS.bdot w2_1 z9 = true := by decide
theorem sg2_1_10 : SS.bdot w2_1 z10 = true := by decide
theorem sg2_1_11 : SS.bdot w2_1 z11 = true := by decide
theorem sg2_2_3 : SS.bdot w2_2 z3 = false := by decide
theorem sg2_2_5 : SS.bdot w2_2 z5 = true := by decide
theorem sg2_2_7 : SS.bdot w2_2 z7 = false := by decide
theorem sg2_2_9 : SS.bdot w2_2 z9 = true := by decide
theorem sg2_2_10 : SS.bdot w2_2 z10 = true := by decide
theorem sg2_2_11 : SS.bdot w2_2 z11 = true := by decide
theorem sg2_3_3 : SS.bdot w2_3 z3 = false := by decide
theorem sg2_3_5 : SS.bdot w2_3 z5 = true := by decide
theorem sg2_3_7 : SS.bdot w2_3 z7 = true := by decide
theorem sg2_3_9 : SS.bdot w2_3 z9 = false := by decide
theorem sg2_3_10 : SS.bdot w2_3 z10 = true := by decide
theorem sg2_3_11 : SS.bdot w2_3 z11 = true := by decide
theorem sg2_4_3 : SS.bdot w2_4 z3 = false := by decide
theorem sg2_4_5 : SS.bdot w2_4 z5 = true := by decide
theorem sg2_4_7 : SS.bdot w2_4 z7 = true := by decide
theorem sg2_4_9 : SS.bdot w2_4 z9 = true := by decide
theorem sg2_4_10 : SS.bdot w2_4 z10 = false := by decide
theorem sg2_4_11 : SS.bdot w2_4 z11 = true := by decide
theorem sg2_5_3 : SS.bdot w2_5 z3 = false := by decide
theorem sg2_5_5 : SS.bdot w2_5 z5 = true := by decide
theorem sg2_5_7 : SS.bdot w2_5 z7 = true := by decide
theorem sg2_5_9 : SS.bdot w2_5 z9 = true := by decide
theorem sg2_5_10 : SS.bdot w2_5 z10 = true := by decide
theorem sg2_5_11 : SS.bdot w2_5 z11 = false := by decide

theorem ex2_0 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef2 w2_0 = star (c y0) * d z3 + star (c y2) * d z5 + star (c y6) * d z7 + star (c y10) * d z9 + star (c y11) * d z10 + star (c y12) * d z11 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_3, fl2_5, fl2_7, fl2_9, fl2_10, fl2_11]
  simp only [sg2_0_3, sg2_0_5, sg2_0_7, sg2_0_9, sg2_0_10, sg2_0_11, SixQubit.signMul_false]
  try ring

theorem ex2_1 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef2 w2_1 = star (c y0) * d z3 + star (c y2) * d z5 - star (c y6) * d z7 - star (c y10) * d z9 - star (c y11) * d z10 - star (c y12) * d z11 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_3, fl2_5, fl2_7, fl2_9, fl2_10, fl2_11]
  simp only [sg2_1_3, sg2_1_5, sg2_1_7, sg2_1_9, sg2_1_10, sg2_1_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex2_2 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef2 w2_2 = star (c y0) * d z3 - star (c y2) * d z5 + star (c y6) * d z7 - star (c y10) * d z9 - star (c y11) * d z10 - star (c y12) * d z11 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_3, fl2_5, fl2_7, fl2_9, fl2_10, fl2_11]
  simp only [sg2_2_3, sg2_2_5, sg2_2_7, sg2_2_9, sg2_2_10, sg2_2_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex2_3 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef2 w2_3 = star (c y0) * d z3 - star (c y2) * d z5 - star (c y6) * d z7 + star (c y10) * d z9 - star (c y11) * d z10 - star (c y12) * d z11 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_3, fl2_5, fl2_7, fl2_9, fl2_10, fl2_11]
  simp only [sg2_3_3, sg2_3_5, sg2_3_7, sg2_3_9, sg2_3_10, sg2_3_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex2_4 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef2 w2_4 = star (c y0) * d z3 - star (c y2) * d z5 - star (c y6) * d z7 - star (c y10) * d z9 + star (c y11) * d z10 - star (c y12) * d z11 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_3, fl2_5, fl2_7, fl2_9, fl2_10, fl2_11]
  simp only [sg2_4_3, sg2_4_5, sg2_4_7, sg2_4_9, sg2_4_10, sg2_4_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex2_5 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef2 w2_5 = star (c y0) * d z3 - star (c y2) * d z5 - star (c y6) * d z7 - star (c y10) * d z9 - star (c y11) * d z10 + star (c y12) * d z11 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_3, fl2_5, fl2_7, fl2_9, fl2_10, fl2_11]
  simp only [sg2_5_3, sg2_5_5, sg2_5_7, sg2_5_9, sg2_5_10, sg2_5_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

/-- System 2 forces this product to vanish. -/
theorem tz2 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef2 w2_0 = 0)
    (h1 : offSum c d ef2 w2_1 = 0)
    (h2 : offSum c d ef2 w2_2 = 0)
    (h3 : offSum c d ef2 w2_3 = 0)
    (h4 : offSum c d ef2 w2_4 = 0)
    (h5 : offSum c d ef2 w2_5 = 0)
    : star (c y0) * d z3 = 0 := by
  rw [ex2_0 c d ] at h0
  rw [ex2_1 c d ] at h1
  rw [ex2_2 c d ] at h2
  rw [ex2_3 c d ] at h3
  rw [ex2_4 c d ] at h4
  rw [ex2_5 c d ] at h5
  linear_combination ((3 / 8) : ℂ) * h0 + ((1 / 8) : ℂ) * h1 + ((1 / 8) : ℂ) * h2 + ((1 / 8) : ℂ) * h3 + ((1 / 8) : ℂ) * h4 + ((1 / 8) : ℂ) * h5

/-- System 3: flip 000100. -/
def ef3 : SS.BitString 6 := bs false false false true  false false
def w3_0 : SS.BitString 6 := bs false false false false false false  -- dressing 000000
def w3_1 : SS.BitString 6 := bs true  false false false false false  -- dressing 100000
def w3_2 : SS.BitString 6 := bs false true  false false false false  -- dressing 010000
def w3_3 : SS.BitString 6 := bs false false true  false false false  -- dressing 001000
def w3_4 : SS.BitString 6 := bs false false false false true  false  -- dressing 000010
def w3_5 : SS.BitString 6 := bs false false false false false true   -- dressing 000001

theorem incidence3 :
    S1.filter (fun y => SS.bxor y ef3 ∈ S0) = {z2, z5, z7, z8, z10, z11} := by decide
theorem fl3_2 : SS.bxor z2 ef3 = y0 := by decide
theorem fl3_5 : SS.bxor z5 ef3 = y3 := by decide
theorem fl3_7 : SS.bxor z7 ef3 = y7 := by decide
theorem fl3_8 : SS.bxor z8 ef3 = y10 := by decide
theorem fl3_10 : SS.bxor z10 ef3 = y13 := by decide
theorem fl3_11 : SS.bxor z11 ef3 = y14 := by decide
theorem sg3_0_2 : SS.bdot w3_0 z2 = false := by decide
theorem sg3_0_5 : SS.bdot w3_0 z5 = false := by decide
theorem sg3_0_7 : SS.bdot w3_0 z7 = false := by decide
theorem sg3_0_8 : SS.bdot w3_0 z8 = false := by decide
theorem sg3_0_10 : SS.bdot w3_0 z10 = false := by decide
theorem sg3_0_11 : SS.bdot w3_0 z11 = false := by decide
theorem sg3_1_2 : SS.bdot w3_1 z2 = false := by decide
theorem sg3_1_5 : SS.bdot w3_1 z5 = false := by decide
theorem sg3_1_7 : SS.bdot w3_1 z7 = true := by decide
theorem sg3_1_8 : SS.bdot w3_1 z8 = true := by decide
theorem sg3_1_10 : SS.bdot w3_1 z10 = true := by decide
theorem sg3_1_11 : SS.bdot w3_1 z11 = true := by decide
theorem sg3_2_2 : SS.bdot w3_2 z2 = false := by decide
theorem sg3_2_5 : SS.bdot w3_2 z5 = true := by decide
theorem sg3_2_7 : SS.bdot w3_2 z7 = false := by decide
theorem sg3_2_8 : SS.bdot w3_2 z8 = true := by decide
theorem sg3_2_10 : SS.bdot w3_2 z10 = true := by decide
theorem sg3_2_11 : SS.bdot w3_2 z11 = true := by decide
theorem sg3_3_2 : SS.bdot w3_3 z2 = false := by decide
theorem sg3_3_5 : SS.bdot w3_3 z5 = true := by decide
theorem sg3_3_7 : SS.bdot w3_3 z7 = true := by decide
theorem sg3_3_8 : SS.bdot w3_3 z8 = false := by decide
theorem sg3_3_10 : SS.bdot w3_3 z10 = true := by decide
theorem sg3_3_11 : SS.bdot w3_3 z11 = true := by decide
theorem sg3_4_2 : SS.bdot w3_4 z2 = false := by decide
theorem sg3_4_5 : SS.bdot w3_4 z5 = true := by decide
theorem sg3_4_7 : SS.bdot w3_4 z7 = true := by decide
theorem sg3_4_8 : SS.bdot w3_4 z8 = true := by decide
theorem sg3_4_10 : SS.bdot w3_4 z10 = false := by decide
theorem sg3_4_11 : SS.bdot w3_4 z11 = true := by decide
theorem sg3_5_2 : SS.bdot w3_5 z2 = false := by decide
theorem sg3_5_5 : SS.bdot w3_5 z5 = true := by decide
theorem sg3_5_7 : SS.bdot w3_5 z7 = true := by decide
theorem sg3_5_8 : SS.bdot w3_5 z8 = true := by decide
theorem sg3_5_10 : SS.bdot w3_5 z10 = true := by decide
theorem sg3_5_11 : SS.bdot w3_5 z11 = false := by decide

theorem ex3_0 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef3 w3_0 = star (c y0) * d z2 + star (c y3) * d z5 + star (c y7) * d z7 + star (c y10) * d z8 + star (c y13) * d z10 + star (c y14) * d z11 := by
  unfold offSum
  rw [incidence3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl3_2, fl3_5, fl3_7, fl3_8, fl3_10, fl3_11]
  simp only [sg3_0_2, sg3_0_5, sg3_0_7, sg3_0_8, sg3_0_10, sg3_0_11, SixQubit.signMul_false]
  try ring

theorem ex3_1 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef3 w3_1 = star (c y0) * d z2 + star (c y3) * d z5 - star (c y7) * d z7 - star (c y10) * d z8 - star (c y13) * d z10 - star (c y14) * d z11 := by
  unfold offSum
  rw [incidence3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl3_2, fl3_5, fl3_7, fl3_8, fl3_10, fl3_11]
  simp only [sg3_1_2, sg3_1_5, sg3_1_7, sg3_1_8, sg3_1_10, sg3_1_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex3_2 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef3 w3_2 = star (c y0) * d z2 - star (c y3) * d z5 + star (c y7) * d z7 - star (c y10) * d z8 - star (c y13) * d z10 - star (c y14) * d z11 := by
  unfold offSum
  rw [incidence3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl3_2, fl3_5, fl3_7, fl3_8, fl3_10, fl3_11]
  simp only [sg3_2_2, sg3_2_5, sg3_2_7, sg3_2_8, sg3_2_10, sg3_2_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex3_3 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef3 w3_3 = star (c y0) * d z2 - star (c y3) * d z5 - star (c y7) * d z7 + star (c y10) * d z8 - star (c y13) * d z10 - star (c y14) * d z11 := by
  unfold offSum
  rw [incidence3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl3_2, fl3_5, fl3_7, fl3_8, fl3_10, fl3_11]
  simp only [sg3_3_2, sg3_3_5, sg3_3_7, sg3_3_8, sg3_3_10, sg3_3_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex3_4 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef3 w3_4 = star (c y0) * d z2 - star (c y3) * d z5 - star (c y7) * d z7 - star (c y10) * d z8 + star (c y13) * d z10 - star (c y14) * d z11 := by
  unfold offSum
  rw [incidence3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl3_2, fl3_5, fl3_7, fl3_8, fl3_10, fl3_11]
  simp only [sg3_4_2, sg3_4_5, sg3_4_7, sg3_4_8, sg3_4_10, sg3_4_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex3_5 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef3 w3_5 = star (c y0) * d z2 - star (c y3) * d z5 - star (c y7) * d z7 - star (c y10) * d z8 - star (c y13) * d z10 + star (c y14) * d z11 := by
  unfold offSum
  rw [incidence3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl3_2, fl3_5, fl3_7, fl3_8, fl3_10, fl3_11]
  simp only [sg3_5_2, sg3_5_5, sg3_5_7, sg3_5_8, sg3_5_10, sg3_5_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

/-- System 3 forces this product to vanish. -/
theorem tz3 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef3 w3_0 = 0)
    (h1 : offSum c d ef3 w3_1 = 0)
    (h2 : offSum c d ef3 w3_2 = 0)
    (h3 : offSum c d ef3 w3_3 = 0)
    (h4 : offSum c d ef3 w3_4 = 0)
    (h5 : offSum c d ef3 w3_5 = 0)
    : star (c y0) * d z2 = 0 := by
  rw [ex3_0 c d ] at h0
  rw [ex3_1 c d ] at h1
  rw [ex3_2 c d ] at h2
  rw [ex3_3 c d ] at h3
  rw [ex3_4 c d ] at h4
  rw [ex3_5 c d ] at h5
  linear_combination ((3 / 8) : ℂ) * h0 + ((1 / 8) : ℂ) * h1 + ((1 / 8) : ℂ) * h2 + ((1 / 8) : ℂ) * h3 + ((1 / 8) : ℂ) * h4 + ((1 / 8) : ℂ) * h5

/-- System 4: flip 000010. -/
def ef4 : SS.BitString 6 := bs false false false false true  false
def w4_0 : SS.BitString 6 := bs false false false false false false  -- dressing 000000
def w4_1 : SS.BitString 6 := bs true  false false false false false  -- dressing 100000
def w4_2 : SS.BitString 6 := bs false true  false false false false  -- dressing 010000
def w4_3 : SS.BitString 6 := bs false false true  false false false  -- dressing 001000
def w4_4 : SS.BitString 6 := bs false false false true  false false  -- dressing 000100
def w4_5 : SS.BitString 6 := bs false false false false false true   -- dressing 000001

theorem incidence4 :
    S1.filter (fun y => SS.bxor y ef4 ∈ S0) = {z1, z5, z7, z8, z9, z11} := by decide
theorem fl4_1 : SS.bxor z1 ef4 = y0 := by decide
theorem fl4_5 : SS.bxor z5 ef4 = y4 := by decide
theorem fl4_7 : SS.bxor z7 ef4 = y8 := by decide
theorem fl4_8 : SS.bxor z8 ef4 = y11 := by decide
theorem fl4_9 : SS.bxor z9 ef4 = y13 := by decide
theorem fl4_11 : SS.bxor z11 ef4 = y15 := by decide
theorem sg4_0_1 : SS.bdot w4_0 z1 = false := by decide
theorem sg4_0_5 : SS.bdot w4_0 z5 = false := by decide
theorem sg4_0_7 : SS.bdot w4_0 z7 = false := by decide
theorem sg4_0_8 : SS.bdot w4_0 z8 = false := by decide
theorem sg4_0_9 : SS.bdot w4_0 z9 = false := by decide
theorem sg4_0_11 : SS.bdot w4_0 z11 = false := by decide
theorem sg4_1_1 : SS.bdot w4_1 z1 = false := by decide
theorem sg4_1_5 : SS.bdot w4_1 z5 = false := by decide
theorem sg4_1_7 : SS.bdot w4_1 z7 = true := by decide
theorem sg4_1_8 : SS.bdot w4_1 z8 = true := by decide
theorem sg4_1_9 : SS.bdot w4_1 z9 = true := by decide
theorem sg4_1_11 : SS.bdot w4_1 z11 = true := by decide
theorem sg4_2_1 : SS.bdot w4_2 z1 = false := by decide
theorem sg4_2_5 : SS.bdot w4_2 z5 = true := by decide
theorem sg4_2_7 : SS.bdot w4_2 z7 = false := by decide
theorem sg4_2_8 : SS.bdot w4_2 z8 = true := by decide
theorem sg4_2_9 : SS.bdot w4_2 z9 = true := by decide
theorem sg4_2_11 : SS.bdot w4_2 z11 = true := by decide
theorem sg4_3_1 : SS.bdot w4_3 z1 = false := by decide
theorem sg4_3_5 : SS.bdot w4_3 z5 = true := by decide
theorem sg4_3_7 : SS.bdot w4_3 z7 = true := by decide
theorem sg4_3_8 : SS.bdot w4_3 z8 = false := by decide
theorem sg4_3_9 : SS.bdot w4_3 z9 = true := by decide
theorem sg4_3_11 : SS.bdot w4_3 z11 = true := by decide
theorem sg4_4_1 : SS.bdot w4_4 z1 = false := by decide
theorem sg4_4_5 : SS.bdot w4_4 z5 = true := by decide
theorem sg4_4_7 : SS.bdot w4_4 z7 = true := by decide
theorem sg4_4_8 : SS.bdot w4_4 z8 = true := by decide
theorem sg4_4_9 : SS.bdot w4_4 z9 = false := by decide
theorem sg4_4_11 : SS.bdot w4_4 z11 = true := by decide
theorem sg4_5_1 : SS.bdot w4_5 z1 = false := by decide
theorem sg4_5_5 : SS.bdot w4_5 z5 = true := by decide
theorem sg4_5_7 : SS.bdot w4_5 z7 = true := by decide
theorem sg4_5_8 : SS.bdot w4_5 z8 = true := by decide
theorem sg4_5_9 : SS.bdot w4_5 z9 = true := by decide
theorem sg4_5_11 : SS.bdot w4_5 z11 = false := by decide

theorem ex4_0 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef4 w4_0 = star (c y0) * d z1 + star (c y4) * d z5 + star (c y8) * d z7 + star (c y11) * d z8 + star (c y13) * d z9 + star (c y15) * d z11 := by
  unfold offSum
  rw [incidence4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl4_1, fl4_5, fl4_7, fl4_8, fl4_9, fl4_11]
  simp only [sg4_0_1, sg4_0_5, sg4_0_7, sg4_0_8, sg4_0_9, sg4_0_11, SixQubit.signMul_false]
  try ring

theorem ex4_1 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef4 w4_1 = star (c y0) * d z1 + star (c y4) * d z5 - star (c y8) * d z7 - star (c y11) * d z8 - star (c y13) * d z9 - star (c y15) * d z11 := by
  unfold offSum
  rw [incidence4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl4_1, fl4_5, fl4_7, fl4_8, fl4_9, fl4_11]
  simp only [sg4_1_1, sg4_1_5, sg4_1_7, sg4_1_8, sg4_1_9, sg4_1_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex4_2 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef4 w4_2 = star (c y0) * d z1 - star (c y4) * d z5 + star (c y8) * d z7 - star (c y11) * d z8 - star (c y13) * d z9 - star (c y15) * d z11 := by
  unfold offSum
  rw [incidence4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl4_1, fl4_5, fl4_7, fl4_8, fl4_9, fl4_11]
  simp only [sg4_2_1, sg4_2_5, sg4_2_7, sg4_2_8, sg4_2_9, sg4_2_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex4_3 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef4 w4_3 = star (c y0) * d z1 - star (c y4) * d z5 - star (c y8) * d z7 + star (c y11) * d z8 - star (c y13) * d z9 - star (c y15) * d z11 := by
  unfold offSum
  rw [incidence4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl4_1, fl4_5, fl4_7, fl4_8, fl4_9, fl4_11]
  simp only [sg4_3_1, sg4_3_5, sg4_3_7, sg4_3_8, sg4_3_9, sg4_3_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex4_4 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef4 w4_4 = star (c y0) * d z1 - star (c y4) * d z5 - star (c y8) * d z7 - star (c y11) * d z8 + star (c y13) * d z9 - star (c y15) * d z11 := by
  unfold offSum
  rw [incidence4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl4_1, fl4_5, fl4_7, fl4_8, fl4_9, fl4_11]
  simp only [sg4_4_1, sg4_4_5, sg4_4_7, sg4_4_8, sg4_4_9, sg4_4_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex4_5 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef4 w4_5 = star (c y0) * d z1 - star (c y4) * d z5 - star (c y8) * d z7 - star (c y11) * d z8 - star (c y13) * d z9 + star (c y15) * d z11 := by
  unfold offSum
  rw [incidence4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl4_1, fl4_5, fl4_7, fl4_8, fl4_9, fl4_11]
  simp only [sg4_5_1, sg4_5_5, sg4_5_7, sg4_5_8, sg4_5_9, sg4_5_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

/-- System 4 forces this product to vanish. -/
theorem tz4 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef4 w4_0 = 0)
    (h1 : offSum c d ef4 w4_1 = 0)
    (h2 : offSum c d ef4 w4_2 = 0)
    (h3 : offSum c d ef4 w4_3 = 0)
    (h4 : offSum c d ef4 w4_4 = 0)
    (h5 : offSum c d ef4 w4_5 = 0)
    : star (c y0) * d z1 = 0 := by
  rw [ex4_0 c d ] at h0
  rw [ex4_1 c d ] at h1
  rw [ex4_2 c d ] at h2
  rw [ex4_3 c d ] at h3
  rw [ex4_4 c d ] at h4
  rw [ex4_5 c d ] at h5
  linear_combination ((3 / 8) : ℂ) * h0 + ((1 / 8) : ℂ) * h1 + ((1 / 8) : ℂ) * h2 + ((1 / 8) : ℂ) * h3 + ((1 / 8) : ℂ) * h4 + ((1 / 8) : ℂ) * h5

/-- System 5: flip 000001. -/
def ef5 : SS.BitString 6 := bs false false false false false true 
def w5_0 : SS.BitString 6 := bs false false false false false false  -- dressing 000000
def w5_1 : SS.BitString 6 := bs true  false false false false false  -- dressing 100000
def w5_2 : SS.BitString 6 := bs false true  false false false false  -- dressing 010000
def w5_3 : SS.BitString 6 := bs false false true  false false false  -- dressing 001000
def w5_4 : SS.BitString 6 := bs false false false true  false false  -- dressing 000100
def w5_5 : SS.BitString 6 := bs false false false false true  false  -- dressing 000010

theorem incidence5 :
    S1.filter (fun y => SS.bxor y ef5 ∈ S0) = {z0, z5, z7, z8, z9, z10} := by decide
theorem fl5_0 : SS.bxor z0 ef5 = y0 := by decide
theorem fl5_5 : SS.bxor z5 ef5 = y5 := by decide
theorem fl5_7 : SS.bxor z7 ef5 = y9 := by decide
theorem fl5_8 : SS.bxor z8 ef5 = y12 := by decide
theorem fl5_9 : SS.bxor z9 ef5 = y14 := by decide
theorem fl5_10 : SS.bxor z10 ef5 = y15 := by decide
theorem sg5_0_0 : SS.bdot w5_0 z0 = false := by decide
theorem sg5_0_5 : SS.bdot w5_0 z5 = false := by decide
theorem sg5_0_7 : SS.bdot w5_0 z7 = false := by decide
theorem sg5_0_8 : SS.bdot w5_0 z8 = false := by decide
theorem sg5_0_9 : SS.bdot w5_0 z9 = false := by decide
theorem sg5_0_10 : SS.bdot w5_0 z10 = false := by decide
theorem sg5_1_0 : SS.bdot w5_1 z0 = false := by decide
theorem sg5_1_5 : SS.bdot w5_1 z5 = false := by decide
theorem sg5_1_7 : SS.bdot w5_1 z7 = true := by decide
theorem sg5_1_8 : SS.bdot w5_1 z8 = true := by decide
theorem sg5_1_9 : SS.bdot w5_1 z9 = true := by decide
theorem sg5_1_10 : SS.bdot w5_1 z10 = true := by decide
theorem sg5_2_0 : SS.bdot w5_2 z0 = false := by decide
theorem sg5_2_5 : SS.bdot w5_2 z5 = true := by decide
theorem sg5_2_7 : SS.bdot w5_2 z7 = false := by decide
theorem sg5_2_8 : SS.bdot w5_2 z8 = true := by decide
theorem sg5_2_9 : SS.bdot w5_2 z9 = true := by decide
theorem sg5_2_10 : SS.bdot w5_2 z10 = true := by decide
theorem sg5_3_0 : SS.bdot w5_3 z0 = false := by decide
theorem sg5_3_5 : SS.bdot w5_3 z5 = true := by decide
theorem sg5_3_7 : SS.bdot w5_3 z7 = true := by decide
theorem sg5_3_8 : SS.bdot w5_3 z8 = false := by decide
theorem sg5_3_9 : SS.bdot w5_3 z9 = true := by decide
theorem sg5_3_10 : SS.bdot w5_3 z10 = true := by decide
theorem sg5_4_0 : SS.bdot w5_4 z0 = false := by decide
theorem sg5_4_5 : SS.bdot w5_4 z5 = true := by decide
theorem sg5_4_7 : SS.bdot w5_4 z7 = true := by decide
theorem sg5_4_8 : SS.bdot w5_4 z8 = true := by decide
theorem sg5_4_9 : SS.bdot w5_4 z9 = false := by decide
theorem sg5_4_10 : SS.bdot w5_4 z10 = true := by decide
theorem sg5_5_0 : SS.bdot w5_5 z0 = false := by decide
theorem sg5_5_5 : SS.bdot w5_5 z5 = true := by decide
theorem sg5_5_7 : SS.bdot w5_5 z7 = true := by decide
theorem sg5_5_8 : SS.bdot w5_5 z8 = true := by decide
theorem sg5_5_9 : SS.bdot w5_5 z9 = true := by decide
theorem sg5_5_10 : SS.bdot w5_5 z10 = false := by decide

theorem ex5_0 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef5 w5_0 = star (c y0) * d z0 + star (c y5) * d z5 + star (c y9) * d z7 + star (c y12) * d z8 + star (c y14) * d z9 + star (c y15) * d z10 := by
  unfold offSum
  rw [incidence5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl5_0, fl5_5, fl5_7, fl5_8, fl5_9, fl5_10]
  simp only [sg5_0_0, sg5_0_5, sg5_0_7, sg5_0_8, sg5_0_9, sg5_0_10, SixQubit.signMul_false]
  try ring

theorem ex5_1 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef5 w5_1 = star (c y0) * d z0 + star (c y5) * d z5 - star (c y9) * d z7 - star (c y12) * d z8 - star (c y14) * d z9 - star (c y15) * d z10 := by
  unfold offSum
  rw [incidence5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl5_0, fl5_5, fl5_7, fl5_8, fl5_9, fl5_10]
  simp only [sg5_1_0, sg5_1_5, sg5_1_7, sg5_1_8, sg5_1_9, sg5_1_10, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex5_2 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef5 w5_2 = star (c y0) * d z0 - star (c y5) * d z5 + star (c y9) * d z7 - star (c y12) * d z8 - star (c y14) * d z9 - star (c y15) * d z10 := by
  unfold offSum
  rw [incidence5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl5_0, fl5_5, fl5_7, fl5_8, fl5_9, fl5_10]
  simp only [sg5_2_0, sg5_2_5, sg5_2_7, sg5_2_8, sg5_2_9, sg5_2_10, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex5_3 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef5 w5_3 = star (c y0) * d z0 - star (c y5) * d z5 - star (c y9) * d z7 + star (c y12) * d z8 - star (c y14) * d z9 - star (c y15) * d z10 := by
  unfold offSum
  rw [incidence5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl5_0, fl5_5, fl5_7, fl5_8, fl5_9, fl5_10]
  simp only [sg5_3_0, sg5_3_5, sg5_3_7, sg5_3_8, sg5_3_9, sg5_3_10, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex5_4 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef5 w5_4 = star (c y0) * d z0 - star (c y5) * d z5 - star (c y9) * d z7 - star (c y12) * d z8 + star (c y14) * d z9 - star (c y15) * d z10 := by
  unfold offSum
  rw [incidence5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl5_0, fl5_5, fl5_7, fl5_8, fl5_9, fl5_10]
  simp only [sg5_4_0, sg5_4_5, sg5_4_7, sg5_4_8, sg5_4_9, sg5_4_10, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex5_5 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef5 w5_5 = star (c y0) * d z0 - star (c y5) * d z5 - star (c y9) * d z7 - star (c y12) * d z8 - star (c y14) * d z9 + star (c y15) * d z10 := by
  unfold offSum
  rw [incidence5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl5_0, fl5_5, fl5_7, fl5_8, fl5_9, fl5_10]
  simp only [sg5_5_0, sg5_5_5, sg5_5_7, sg5_5_8, sg5_5_9, sg5_5_10, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

/-- System 5 forces this product to vanish. -/
theorem tz5 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef5 w5_0 = 0)
    (h1 : offSum c d ef5 w5_1 = 0)
    (h2 : offSum c d ef5 w5_2 = 0)
    (h3 : offSum c d ef5 w5_3 = 0)
    (h4 : offSum c d ef5 w5_4 = 0)
    (h5 : offSum c d ef5 w5_5 = 0)
    : star (c y0) * d z0 = 0 := by
  rw [ex5_0 c d ] at h0
  rw [ex5_1 c d ] at h1
  rw [ex5_2 c d ] at h2
  rw [ex5_3 c d ] at h3
  rw [ex5_4 c d ] at h4
  rw [ex5_5 c d ] at h5
  linear_combination ((3 / 8) : ℂ) * h0 + ((1 / 8) : ℂ) * h1 + ((1 / 8) : ℂ) * h2 + ((1 / 8) : ℂ) * h3 + ((1 / 8) : ℂ) * h4 + ((1 / 8) : ℂ) * h5

/-- **Orbit 27 is impossible.** -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11)) (Complex.normSq (c y12)) (Complex.normSq (c y13)) (Complex.normSq (c y14)) (Complex.normSq (c y15))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)))
    (e0_0 : offSum c d ef0 w0_0 = 0)
    (e0_1 : offSum c d ef0 w0_1 = 0)
    (e0_2 : offSum c d ef0 w0_2 = 0)
    (e0_3 : offSum c d ef0 w0_3 = 0)
    (e0_4 : offSum c d ef0 w0_4 = 0)
    (e0_5 : offSum c d ef0 w0_5 = 0)
    (e1_0 : offSum c d ef1 w1_0 = 0)
    (e1_1 : offSum c d ef1 w1_1 = 0)
    (e1_2 : offSum c d ef1 w1_2 = 0)
    (e1_3 : offSum c d ef1 w1_3 = 0)
    (e1_4 : offSum c d ef1 w1_4 = 0)
    (e1_5 : offSum c d ef1 w1_5 = 0)
    (e2_0 : offSum c d ef2 w2_0 = 0)
    (e2_1 : offSum c d ef2 w2_1 = 0)
    (e2_2 : offSum c d ef2 w2_2 = 0)
    (e2_3 : offSum c d ef2 w2_3 = 0)
    (e2_4 : offSum c d ef2 w2_4 = 0)
    (e2_5 : offSum c d ef2 w2_5 = 0)
    (e3_0 : offSum c d ef3 w3_0 = 0)
    (e3_1 : offSum c d ef3 w3_1 = 0)
    (e3_2 : offSum c d ef3 w3_2 = 0)
    (e3_3 : offSum c d ef3 w3_3 = 0)
    (e3_4 : offSum c d ef3 w3_4 = 0)
    (e3_5 : offSum c d ef3 w3_5 = 0)
    (e4_0 : offSum c d ef4 w4_0 = 0)
    (e4_1 : offSum c d ef4 w4_1 = 0)
    (e4_2 : offSum c d ef4 w4_2 = 0)
    (e4_3 : offSum c d ef4 w4_3 = 0)
    (e4_4 : offSum c d ef4 w4_4 = 0)
    (e4_5 : offSum c d ef4 w4_5 = 0)
    (e5_0 : offSum c d ef5 w5_0 = 0)
    (e5_1 : offSum c d ef5 w5_1 = 0)
    (e5_2 : offSum c d ef5 w5_2 = 0)
    (e5_3 : offSum c d ef5 w5_3 = 0)
    (e5_4 : offSum c d ef5 w5_4 = 0)
    (e5_5 : offSum c d ef5 w5_5 = 0)
    : False := by
  have a0 := hm.anchors
  have na0 : c y0 ≠ 0 := fun hz => by rw [hz] at a0; simp at a0
  have p0 := tz0 c d  e0_0 e0_1 e0_2 e0_3 e0_4 e0_5
  have v22 : d z6 = 0 := by
    rcases mul_eq_zero.mp p0 with hh | hh
    · exact absurd (by simpa using congrArg star hh) na0
    · exact hh
  have p1 := tz1 c d  e1_0 e1_1 e1_2 e1_3 e1_4 e1_5
  have v20 : d z4 = 0 := by
    rcases mul_eq_zero.mp p1 with hh | hh
    · exact absurd (by simpa using congrArg star hh) na0
    · exact hh
  have p2 := tz2 c d  e2_0 e2_1 e2_2 e2_3 e2_4 e2_5
  have v19 : d z3 = 0 := by
    rcases mul_eq_zero.mp p2 with hh | hh
    · exact absurd (by simpa using congrArg star hh) na0
    · exact hh
  have p3 := tz3 c d  e3_0 e3_1 e3_2 e3_3 e3_4 e3_5
  have v18 : d z2 = 0 := by
    rcases mul_eq_zero.mp p3 with hh | hh
    · exact absurd (by simpa using congrArg star hh) na0
    · exact hh
  have p4 := tz4 c d  e4_0 e4_1 e4_2 e4_3 e4_4 e4_5
  have v17 : d z1 = 0 := by
    rcases mul_eq_zero.mp p4 with hh | hh
    · exact absurd (by simpa using congrArg star hh) na0
    · exact hh
  have p5 := tz5 c d  e5_0 e5_1 e5_2 e5_3 e5_4 e5_5
  have v16 : d z0 = 0 := by
    rcases mul_eq_zero.mp p5 with hh | hh
    · exact absurd (by simpa using congrArg star hh) na0
    · exact hh
  exact hm.infeasible
    (by rw [v16]; simp)
    (by rw [v17]; simp)
    (by rw [v18]; simp)
    (by rw [v19]; simp)
    (by rw [v20]; simp)
    (by rw [v22]; simp)

end

end SixQubit.Orbit27
