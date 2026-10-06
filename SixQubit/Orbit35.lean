import Mathlib

import SS.FullKL
import SixQubit.Common

/-!
# Six-qubit no-go for moment orbit 35

Orbit 35 of `six_qubit_sslp_v7.tex`: q = 5, angle vector
a = (1, 1, 1, 2, 2, 3), residues 0 and 1, closed in Section 17.

No single Walsh system kills this orbit.  The certificate is a chain:

* the moment polytope alone forces 3 probabilities to vanish;
* with those eliminated, 3 Walsh systems each force one product to
  vanish, and each pairs with an anchor probability that the polytope
  forces strictly positive, turning it into a vanishing amplitude;
* the moment polytope carrying all 6 zeros is infeasible.

Everything computational is decided by the Lean kernel; `native_decide` is
not used.
-/

namespace SixQubit.Orbit35

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]

def y0 : SS.BitString 6 := bs false false false false false false  -- 000000
def y1 : SS.BitString 6 := bs false false false false true  true   -- 000011
def y2 : SS.BitString 6 := bs false false false true  false true   -- 000101
def y3 : SS.BitString 6 := bs false false true  true  true  false  -- 001110
def y4 : SS.BitString 6 := bs false true  false true  true  false  -- 010110
def y5 : SS.BitString 6 := bs false true  true  false false true   -- 011001
def y6 : SS.BitString 6 := bs true  false false true  true  false  -- 100110
def y7 : SS.BitString 6 := bs true  false true  false false true   -- 101001
def y8 : SS.BitString 6 := bs true  true  false false false true   -- 110001
def y9 : SS.BitString 6 := bs true  true  true  false true  false  -- 111010
def y10 : SS.BitString 6 := bs true  true  true  true  false false  -- 111100
def y11 : SS.BitString 6 := bs true  true  true  true  true  true   -- 111111

def z0 : SS.BitString 6 := bs false false true  false false false  -- 001000
def z1 : SS.BitString 6 := bs false false true  false true  true   -- 001011
def z2 : SS.BitString 6 := bs false false true  true  false true   -- 001101
def z3 : SS.BitString 6 := bs false true  false false false false  -- 010000
def z4 : SS.BitString 6 := bs false true  false false true  true   -- 010011
def z5 : SS.BitString 6 := bs false true  false true  false true   -- 010101
def z6 : SS.BitString 6 := bs false true  true  true  true  false  -- 011110
def z7 : SS.BitString 6 := bs true  false false false false false  -- 100000
def z8 : SS.BitString 6 := bs true  false false false true  true   -- 100011
def z9 : SS.BitString 6 := bs true  false false true  false true   -- 100101
def z10 : SS.BitString 6 := bs true  false true  true  true  false  -- 101110
def z11 : SS.BitString 6 := bs true  true  false true  true  false  -- 110110
def z12 : SS.BitString 6 := bs true  true  true  false false true   -- 111001

def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11}
def S1 : Finset (SS.BitString 6) := {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12}

def av : Fin 6 -> ZMod 5 := ![1, 1, 1, 2, 2, 3]

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
structure MomentSystem (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : Real) : Prop where
  n0 : q0 + q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 + q9 + q10 + q11 = 1
  n1 : r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 = 1
  m1 : q6 + q7 + q8 + q9 + q10 + q11 = r7 + r8 + r9 + r10 + r11 + r12
  m2 : q4 + q5 + q8 + q9 + q10 + q11 = r3 + r4 + r5 + r6 + r11 + r12
  m3 : q3 + q5 + q7 + q9 + q10 + q11 = r0 + r1 + r2 + r6 + r10 + r12
  m4 : q2 + q3 + q4 + q6 + q10 + q11 = r2 + r5 + r6 + r9 + r10 + r11
  m5 : q1 + q3 + q4 + q6 + q9 + q11 = r1 + r4 + r6 + r8 + r10 + r11
  m6 : q1 + q2 + q5 + q7 + q8 + q11 = r1 + r2 + r4 + r5 + r8 + r9 + r12
  c12 : q8 + q9 + q10 + q11 = r11 + r12
  c13 : q7 + q9 + q10 + q11 = r10 + r12
  c14 : q6 + q10 + q11 = r9 + r10 + r11
  c15 : q6 + q9 + q11 = r8 + r10 + r11
  c16 : q7 + q8 + q11 = r8 + r9 + r12
  c23 : q5 + q9 + q10 + q11 = r6 + r12
  c24 : q4 + q10 + q11 = r5 + r6 + r11
  c25 : q4 + q9 + q11 = r4 + r6 + r11
  c26 : q5 + q8 + q11 = r4 + r5 + r12
  c34 : q3 + q10 + q11 = r2 + r6 + r10
  c35 : q3 + q9 + q11 = r1 + r6 + r10
  c36 : q5 + q7 + q11 = r1 + r2 + r12
  c45 : q3 + q4 + q6 + q11 = r6 + r10 + r11
  c46 : q2 + q11 = r2 + r5 + r9
  c56 : q1 + q11 = r1 + r4 + r8

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
  nr12 : 0 ≤ r12

/-- Stage 0: the polytope alone forces these to vanish. -/
theorem MomentSystem.stage0 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : Real}
    (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) :
    q0 = 0 ∧ q1 = 0 ∧ q2 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- The anchor probabilities the chain uses are strictly positive. -/
theorem MomentSystem.anchors {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : Real}
    (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) :
    0 < r12 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12⟩ := h
  linarith

/-- Stage 2: the polytope carrying every derived zero is infeasible. -/
theorem MomentSystem.infeasible {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : Real}
    (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12)
    (v0 : q0 = 0)
    (v1 : q1 = 0)
    (v2 : q2 = 0)
    (v5 : q5 = 0)
    (v7 : q7 = 0)
    (v8 : q8 = 0)
    : False := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12⟩ := h
  linarith

/-! ## The Walsh systems -/

def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),
      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

theorem signMul_zero (b : Bool) : SixQubit.signMul b (0 : ℂ) = 0 := by
  cases b <;> simp [SixQubit.signMul]

/-- System 0: flip 100000. -/
def ef0 : SS.BitString 6 := bs true  false false false false false
def w0_0 : SS.BitString 6 := bs false true  false false false false  -- dressing 010000
def w0_1 : SS.BitString 6 := bs false false true  false false false  -- dressing 001000

theorem incidence0 :
    S1.filter (fun y => SS.bxor y ef0 ∈ S0) = {z7, z8, z9, z10, z11, z12} := by decide
theorem fl0_7 : SS.bxor z7 ef0 = y0 := by decide
theorem fl0_8 : SS.bxor z8 ef0 = y1 := by decide
theorem fl0_9 : SS.bxor z9 ef0 = y2 := by decide
theorem fl0_10 : SS.bxor z10 ef0 = y3 := by decide
theorem fl0_11 : SS.bxor z11 ef0 = y4 := by decide
theorem fl0_12 : SS.bxor z12 ef0 = y5 := by decide
theorem sg0_0_7 : SS.bdot w0_0 z7 = false := by decide
theorem sg0_0_8 : SS.bdot w0_0 z8 = false := by decide
theorem sg0_0_9 : SS.bdot w0_0 z9 = false := by decide
theorem sg0_0_10 : SS.bdot w0_0 z10 = false := by decide
theorem sg0_0_11 : SS.bdot w0_0 z11 = true := by decide
theorem sg0_0_12 : SS.bdot w0_0 z12 = true := by decide
theorem sg0_1_7 : SS.bdot w0_1 z7 = false := by decide
theorem sg0_1_8 : SS.bdot w0_1 z8 = false := by decide
theorem sg0_1_9 : SS.bdot w0_1 z9 = false := by decide
theorem sg0_1_10 : SS.bdot w0_1 z10 = true := by decide
theorem sg0_1_11 : SS.bdot w0_1 z11 = false := by decide
theorem sg0_1_12 : SS.bdot w0_1 z12 = true := by decide

theorem ex0_0 (c d : SS.BitString 6 -> ℂ)
    (k0 : c y0 = 0)
    (k1 : c y1 = 0)
    (k2 : c y2 = 0)
    : offSum c d ef0 w0_0 = star (c y3) * d z10 - star (c y4) * d z11 - star (c y5) * d z12 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_7, fl0_8, fl0_9, fl0_10, fl0_11, fl0_12]
  rw [k0, k1, k2]
  simp only [sg0_0_10, sg0_0_11, sg0_0_12, SixQubit.signMul_true, SixQubit.signMul_false, signMul_zero, star_zero, zero_mul]
  try ring

theorem ex0_1 (c d : SS.BitString 6 -> ℂ)
    (k0 : c y0 = 0)
    (k1 : c y1 = 0)
    (k2 : c y2 = 0)
    : offSum c d ef0 w0_1 = - star (c y3) * d z10 + star (c y4) * d z11 - star (c y5) * d z12 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_7, fl0_8, fl0_9, fl0_10, fl0_11, fl0_12]
  rw [k0, k1, k2]
  simp only [sg0_1_10, sg0_1_11, sg0_1_12, SixQubit.signMul_true, SixQubit.signMul_false, signMul_zero, star_zero, zero_mul]
  try ring

/-- System 0 forces this product to vanish. -/
theorem tz0 (c d : SS.BitString 6 -> ℂ)
    (k0 : c y0 = 0)
    (k1 : c y1 = 0)
    (k2 : c y2 = 0)
    (h0 : offSum c d ef0 w0_0 = 0)
    (h1 : offSum c d ef0 w0_1 = 0)
    : star (c y5) * d z12 = 0 := by
  rw [ex0_0 c d k0 k1 k2] at h0
  rw [ex0_1 c d k0 k1 k2] at h1
  linear_combination ((-1 / 2) : ℂ) * h0 + ((-1 / 2) : ℂ) * h1

/-- System 1: flip 010000. -/
def ef1 : SS.BitString 6 := bs false true  false false false false
def w1_0 : SS.BitString 6 := bs true  false false false false false  -- dressing 100000
def w1_1 : SS.BitString 6 := bs false false true  false false false  -- dressing 001000

theorem incidence1 :
    S1.filter (fun y => SS.bxor y ef1 ∈ S0) = {z3, z4, z5, z6, z11, z12} := by decide
theorem fl1_3 : SS.bxor z3 ef1 = y0 := by decide
theorem fl1_4 : SS.bxor z4 ef1 = y1 := by decide
theorem fl1_5 : SS.bxor z5 ef1 = y2 := by decide
theorem fl1_6 : SS.bxor z6 ef1 = y3 := by decide
theorem fl1_11 : SS.bxor z11 ef1 = y6 := by decide
theorem fl1_12 : SS.bxor z12 ef1 = y7 := by decide
theorem sg1_0_3 : SS.bdot w1_0 z3 = false := by decide
theorem sg1_0_4 : SS.bdot w1_0 z4 = false := by decide
theorem sg1_0_5 : SS.bdot w1_0 z5 = false := by decide
theorem sg1_0_6 : SS.bdot w1_0 z6 = false := by decide
theorem sg1_0_11 : SS.bdot w1_0 z11 = true := by decide
theorem sg1_0_12 : SS.bdot w1_0 z12 = true := by decide
theorem sg1_1_3 : SS.bdot w1_1 z3 = false := by decide
theorem sg1_1_4 : SS.bdot w1_1 z4 = false := by decide
theorem sg1_1_5 : SS.bdot w1_1 z5 = false := by decide
theorem sg1_1_6 : SS.bdot w1_1 z6 = true := by decide
theorem sg1_1_11 : SS.bdot w1_1 z11 = false := by decide
theorem sg1_1_12 : SS.bdot w1_1 z12 = true := by decide

theorem ex1_0 (c d : SS.BitString 6 -> ℂ)
    (k0 : c y0 = 0)
    (k1 : c y1 = 0)
    (k2 : c y2 = 0)
    : offSum c d ef1 w1_0 = star (c y3) * d z6 - star (c y6) * d z11 - star (c y7) * d z12 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_3, fl1_4, fl1_5, fl1_6, fl1_11, fl1_12]
  rw [k0, k1, k2]
  simp only [sg1_0_6, sg1_0_11, sg1_0_12, SixQubit.signMul_true, SixQubit.signMul_false, signMul_zero, star_zero, zero_mul]
  try ring

theorem ex1_1 (c d : SS.BitString 6 -> ℂ)
    (k0 : c y0 = 0)
    (k1 : c y1 = 0)
    (k2 : c y2 = 0)
    : offSum c d ef1 w1_1 = - star (c y3) * d z6 + star (c y6) * d z11 - star (c y7) * d z12 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_3, fl1_4, fl1_5, fl1_6, fl1_11, fl1_12]
  rw [k0, k1, k2]
  simp only [sg1_1_6, sg1_1_11, sg1_1_12, SixQubit.signMul_true, SixQubit.signMul_false, signMul_zero, star_zero, zero_mul]
  try ring

/-- System 1 forces this product to vanish. -/
theorem tz1 (c d : SS.BitString 6 -> ℂ)
    (k0 : c y0 = 0)
    (k1 : c y1 = 0)
    (k2 : c y2 = 0)
    (h0 : offSum c d ef1 w1_0 = 0)
    (h1 : offSum c d ef1 w1_1 = 0)
    : star (c y7) * d z12 = 0 := by
  rw [ex1_0 c d k0 k1 k2] at h0
  rw [ex1_1 c d k0 k1 k2] at h1
  linear_combination ((-1 / 2) : ℂ) * h0 + ((-1 / 2) : ℂ) * h1

/-- System 2: flip 001000. -/
def ef2 : SS.BitString 6 := bs false false true  false false false
def w2_0 : SS.BitString 6 := bs true  false false false false false  -- dressing 100000
def w2_1 : SS.BitString 6 := bs false true  false false false false  -- dressing 010000

theorem incidence2 :
    S1.filter (fun y => SS.bxor y ef2 ∈ S0) = {z0, z1, z2, z6, z10, z12} := by decide
theorem fl2_0 : SS.bxor z0 ef2 = y0 := by decide
theorem fl2_1 : SS.bxor z1 ef2 = y1 := by decide
theorem fl2_2 : SS.bxor z2 ef2 = y2 := by decide
theorem fl2_6 : SS.bxor z6 ef2 = y4 := by decide
theorem fl2_10 : SS.bxor z10 ef2 = y6 := by decide
theorem fl2_12 : SS.bxor z12 ef2 = y8 := by decide
theorem sg2_0_0 : SS.bdot w2_0 z0 = false := by decide
theorem sg2_0_1 : SS.bdot w2_0 z1 = false := by decide
theorem sg2_0_2 : SS.bdot w2_0 z2 = false := by decide
theorem sg2_0_6 : SS.bdot w2_0 z6 = false := by decide
theorem sg2_0_10 : SS.bdot w2_0 z10 = true := by decide
theorem sg2_0_12 : SS.bdot w2_0 z12 = true := by decide
theorem sg2_1_0 : SS.bdot w2_1 z0 = false := by decide
theorem sg2_1_1 : SS.bdot w2_1 z1 = false := by decide
theorem sg2_1_2 : SS.bdot w2_1 z2 = false := by decide
theorem sg2_1_6 : SS.bdot w2_1 z6 = true := by decide
theorem sg2_1_10 : SS.bdot w2_1 z10 = false := by decide
theorem sg2_1_12 : SS.bdot w2_1 z12 = true := by decide

theorem ex2_0 (c d : SS.BitString 6 -> ℂ)
    (k0 : c y0 = 0)
    (k1 : c y1 = 0)
    (k2 : c y2 = 0)
    : offSum c d ef2 w2_0 = star (c y4) * d z6 - star (c y6) * d z10 - star (c y8) * d z12 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_0, fl2_1, fl2_2, fl2_6, fl2_10, fl2_12]
  rw [k0, k1, k2]
  simp only [sg2_0_6, sg2_0_10, sg2_0_12, SixQubit.signMul_true, SixQubit.signMul_false, signMul_zero, star_zero, zero_mul]
  try ring

theorem ex2_1 (c d : SS.BitString 6 -> ℂ)
    (k0 : c y0 = 0)
    (k1 : c y1 = 0)
    (k2 : c y2 = 0)
    : offSum c d ef2 w2_1 = - star (c y4) * d z6 + star (c y6) * d z10 - star (c y8) * d z12 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_0, fl2_1, fl2_2, fl2_6, fl2_10, fl2_12]
  rw [k0, k1, k2]
  simp only [sg2_1_6, sg2_1_10, sg2_1_12, SixQubit.signMul_true, SixQubit.signMul_false, signMul_zero, star_zero, zero_mul]
  try ring

/-- System 2 forces this product to vanish. -/
theorem tz2 (c d : SS.BitString 6 -> ℂ)
    (k0 : c y0 = 0)
    (k1 : c y1 = 0)
    (k2 : c y2 = 0)
    (h0 : offSum c d ef2 w2_0 = 0)
    (h1 : offSum c d ef2 w2_1 = 0)
    : star (c y8) * d z12 = 0 := by
  rw [ex2_0 c d k0 k1 k2] at h0
  rw [ex2_1 c d k0 k1 k2] at h1
  linear_combination ((-1 / 2) : ℂ) * h0 + ((-1 / 2) : ℂ) * h1

/-- **Orbit 35 is impossible.** -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)) (Complex.normSq (d z12)))
    (e0_0 : offSum c d ef0 w0_0 = 0)
    (e0_1 : offSum c d ef0 w0_1 = 0)
    (e1_0 : offSum c d ef1 w1_0 = 0)
    (e1_1 : offSum c d ef1 w1_1 = 0)
    (e2_0 : offSum c d ef2 w2_0 = 0)
    (e2_1 : offSum c d ef2 w2_1 = 0)
    : False := by
  obtain ⟨s0, s1, s2⟩ := hm.stage0
  have k0 : c y0 = 0 := Complex.normSq_eq_zero.mp s0
  have k1 : c y1 = 0 := Complex.normSq_eq_zero.mp s1
  have k2 : c y2 = 0 := Complex.normSq_eq_zero.mp s2
  have a24 := hm.anchors
  have na24 : d z12 ≠ 0 := fun hz => by rw [hz] at a24; simp at a24
  have p0 := tz0 c d k0 k1 k2 e0_0 e0_1
  have v5 : c y5 = 0 := by
    rcases mul_eq_zero.mp p0 with hh | hh
    · simpa using congrArg star hh
    · exact absurd hh na24
  have p1 := tz1 c d k0 k1 k2 e1_0 e1_1
  have v7 : c y7 = 0 := by
    rcases mul_eq_zero.mp p1 with hh | hh
    · simpa using congrArg star hh
    · exact absurd hh na24
  have p2 := tz2 c d k0 k1 k2 e2_0 e2_1
  have v8 : c y8 = 0 := by
    rcases mul_eq_zero.mp p2 with hh | hh
    · simpa using congrArg star hh
    · exact absurd hh na24
  exact hm.infeasible
    s0
    s1
    s2
    (by rw [v5]; simp)
    (by rw [v7]; simp)
    (by rw [v8]; simp)

end

end SixQubit.Orbit35
