import Mathlib

import SS.FullKL
import SixQubit.Common
import SixQubit.Triangle

/-!
# Six-qubit no-go for moment orbit 50

Orbit 50 of `six_qubit_sslp.tex`: q = 6, angle vector
a = (1, 1, 1, 3, 4, 4), residues 0 and 2.  The two fibers are complementary.

Indices 0 and 10 have probability forced positive, and the moment system
gives the shell mass 1/3 on {1, 2, 5}, so at least one of those is active too.
Each of the three pairs carries a reciprocal flip relation, and
`SixQubit.Triangle.contradiction_of_normSq` closes the resulting odd
triangle without any division.

Everything computational is decided by the Lean kernel; `native_decide`
is not used.
-/

namespace SixQubit.Orbit50

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

/-! ## The two fibers -/

def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]

def y0 : SS.BitString 6 := bs false false false false false false  -- 000000
def y1 : SS.BitString 6 := bs false false true  true  true  true   -- 001111
def y2 : SS.BitString 6 := bs false true  false true  true  true   -- 010111
def y3 : SS.BitString 6 := bs false true  true  false false true   -- 011001
def y4 : SS.BitString 6 := bs false true  true  false true  false  -- 011010
def y5 : SS.BitString 6 := bs true  false false true  true  true   -- 100111
def y6 : SS.BitString 6 := bs true  false true  false false true   -- 101001
def y7 : SS.BitString 6 := bs true  false true  false true  false  -- 101010
def y8 : SS.BitString 6 := bs true  true  false false false true   -- 110001
def y9 : SS.BitString 6 := bs true  true  false false true  false  -- 110010
def y10 : SS.BitString 6 := bs true  true  true  true  false false  -- 111100

def z0 : SS.BitString 6 := bs false false false false true  true   -- 000011
def z1 : SS.BitString 6 := bs false false true  true  false true   -- 001101
def z2 : SS.BitString 6 := bs false false true  true  true  false  -- 001110
def z3 : SS.BitString 6 := bs false true  false true  false true   -- 010101
def z4 : SS.BitString 6 := bs false true  false true  true  false  -- 010110
def z5 : SS.BitString 6 := bs false true  true  false false false  -- 011000
def z6 : SS.BitString 6 := bs true  false false true  false true   -- 100101
def z7 : SS.BitString 6 := bs true  false false true  true  false  -- 100110
def z8 : SS.BitString 6 := bs true  false true  false false false  -- 101000
def z9 : SS.BitString 6 := bs true  true  false false false false  -- 110000
def z10 : SS.BitString 6 := bs true  true  true  true  true  true   -- 111111

def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10}
def S1 : Finset (SS.BitString 6) := {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10}

def av : Fin 6 -> ZMod 6 := ![1, 1, 1, 3, 4, 4]

theorem S0_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 0) = S0 := by
  decide

theorem S1_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 2) = S1 := by
  decide

/-! ## Flip masks, incidences and signs -/

def ef0 : SS.BitString 6 := bs false false false false true  true   -- 000011
def ef1 : SS.BitString 6 := bs false false true  true  false false  -- 001100
def ef2 : SS.BitString 6 := bs false true  false true  false false  -- 010100
def ef3 : SS.BitString 6 := bs false true  true  false false false  -- 011000
def ef4 : SS.BitString 6 := bs true  false false true  false false  -- 100100
def ef5 : SS.BitString 6 := bs true  false true  false false false  -- 101000
def ef6 : SS.BitString 6 := bs true  true  false false false false  -- 110000
def w0 : SS.BitString 6 := bs false false false false false false  -- 000000
def w1 : SS.BitString 6 := bs false false false true  false false  -- 000100

theorem incidence_ef0 :
    S1.filter (fun y => SS.bxor y ef0 ∈ S0) = {z0, z10} := by decide
theorem flip_ef0_0 : SS.bxor z0 ef0 = y0 := by decide
theorem flip_ef0_10 : SS.bxor z10 ef0 = y10 := by decide
theorem sg_ef0_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg_ef0_w0_10 : SS.bdot w0 z10 = false := by decide

theorem incidence_ef1 :
    S1.filter (fun y => SS.bxor y ef1 ∈ S0) = {z0, z3, z4, z6, z7, z9} := by decide
theorem flip_ef1_0 : SS.bxor z0 ef1 = y1 := by decide
theorem flip_ef1_3 : SS.bxor z3 ef1 = y3 := by decide
theorem flip_ef1_4 : SS.bxor z4 ef1 = y4 := by decide
theorem flip_ef1_6 : SS.bxor z6 ef1 = y6 := by decide
theorem flip_ef1_7 : SS.bxor z7 ef1 = y7 := by decide
theorem flip_ef1_9 : SS.bxor z9 ef1 = y10 := by decide
theorem sg_ef1_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg_ef1_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg_ef1_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg_ef1_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg_ef1_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg_ef1_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg_ef1_w1_0 : SS.bdot w1 z0 = false := by decide
theorem sg_ef1_w1_3 : SS.bdot w1 z3 = true := by decide
theorem sg_ef1_w1_4 : SS.bdot w1 z4 = true := by decide
theorem sg_ef1_w1_6 : SS.bdot w1 z6 = true := by decide
theorem sg_ef1_w1_7 : SS.bdot w1 z7 = true := by decide
theorem sg_ef1_w1_9 : SS.bdot w1 z9 = false := by decide

theorem incidence_ef2 :
    S1.filter (fun y => SS.bxor y ef2 ∈ S0) = {z0, z1, z2, z6, z7, z8} := by decide
theorem flip_ef2_0 : SS.bxor z0 ef2 = y2 := by decide
theorem flip_ef2_1 : SS.bxor z1 ef2 = y3 := by decide
theorem flip_ef2_2 : SS.bxor z2 ef2 = y4 := by decide
theorem flip_ef2_6 : SS.bxor z6 ef2 = y8 := by decide
theorem flip_ef2_7 : SS.bxor z7 ef2 = y9 := by decide
theorem flip_ef2_8 : SS.bxor z8 ef2 = y10 := by decide
theorem sg_ef2_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg_ef2_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg_ef2_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg_ef2_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg_ef2_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg_ef2_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_ef2_w1_0 : SS.bdot w1 z0 = false := by decide
theorem sg_ef2_w1_1 : SS.bdot w1 z1 = true := by decide
theorem sg_ef2_w1_2 : SS.bdot w1 z2 = true := by decide
theorem sg_ef2_w1_6 : SS.bdot w1 z6 = true := by decide
theorem sg_ef2_w1_7 : SS.bdot w1 z7 = true := by decide
theorem sg_ef2_w1_8 : SS.bdot w1 z8 = false := by decide

theorem incidence_ef3 :
    S1.filter (fun y => SS.bxor y ef3 ∈ S0) = {z5, z10} := by decide
theorem flip_ef3_5 : SS.bxor z5 ef3 = y0 := by decide
theorem flip_ef3_10 : SS.bxor z10 ef3 = y5 := by decide
theorem sg_ef3_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg_ef3_w0_10 : SS.bdot w0 z10 = false := by decide

theorem incidence_ef4 :
    S1.filter (fun y => SS.bxor y ef4 ∈ S0) = {z0, z1, z2, z3, z4, z5} := by decide
theorem flip_ef4_0 : SS.bxor z0 ef4 = y5 := by decide
theorem flip_ef4_1 : SS.bxor z1 ef4 = y6 := by decide
theorem flip_ef4_2 : SS.bxor z2 ef4 = y7 := by decide
theorem flip_ef4_3 : SS.bxor z3 ef4 = y8 := by decide
theorem flip_ef4_4 : SS.bxor z4 ef4 = y9 := by decide
theorem flip_ef4_5 : SS.bxor z5 ef4 = y10 := by decide
theorem sg_ef4_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg_ef4_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg_ef4_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg_ef4_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg_ef4_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg_ef4_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg_ef4_w1_0 : SS.bdot w1 z0 = false := by decide
theorem sg_ef4_w1_1 : SS.bdot w1 z1 = true := by decide
theorem sg_ef4_w1_2 : SS.bdot w1 z2 = true := by decide
theorem sg_ef4_w1_3 : SS.bdot w1 z3 = true := by decide
theorem sg_ef4_w1_4 : SS.bdot w1 z4 = true := by decide
theorem sg_ef4_w1_5 : SS.bdot w1 z5 = false := by decide

theorem incidence_ef5 :
    S1.filter (fun y => SS.bxor y ef5 ∈ S0) = {z8, z10} := by decide
theorem flip_ef5_8 : SS.bxor z8 ef5 = y0 := by decide
theorem flip_ef5_10 : SS.bxor z10 ef5 = y2 := by decide
theorem sg_ef5_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_ef5_w0_10 : SS.bdot w0 z10 = false := by decide

theorem incidence_ef6 :
    S1.filter (fun y => SS.bxor y ef6 ∈ S0) = {z9, z10} := by decide
theorem flip_ef6_9 : SS.bxor z9 ef6 = y0 := by decide
theorem flip_ef6_10 : SS.bxor z10 ef6 = y1 := by decide
theorem sg_ef6_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg_ef6_w0_10 : SS.bdot w0 z10 = false := by decide

/-! ## The moment system -/

structure MomentSystem (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 : Real) : Prop where
  n0 : q0 + q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 + q9 + q10 = 1
  n1 : r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 = 1
  m1 : q5 + q6 + q7 + q8 + q9 + q10 = r6 + r7 + r8 + r9 + r10
  m2 : q2 + q3 + q4 + q8 + q9 + q10 = r3 + r4 + r5 + r9 + r10
  m3 : q1 + q3 + q4 + q6 + q7 + q10 = r1 + r2 + r5 + r8 + r10
  m4 : q1 + q2 + q5 + q10 = r1 + r2 + r3 + r4 + r6 + r7 + r10
  m5 : q1 + q2 + q4 + q5 + q7 + q9 = r0 + r2 + r4 + r7 + r10
  m6 : q1 + q2 + q3 + q5 + q6 + q8 = r0 + r1 + r3 + r6 + r10
  m12 : q8 + q9 + q10 = r9 + r10
  m13 : q6 + q7 + q10 = r8 + r10
  m14 : q5 + q10 = r6 + r7 + r10
  m15 : q5 + q7 + q9 = r7 + r10
  m16 : q5 + q6 + q8 = r6 + r10
  m23 : q3 + q4 + q10 = r5 + r10
  m24 : q2 + q10 = r3 + r4 + r10
  m25 : q2 + q4 + q9 = r4 + r10
  m26 : q2 + q3 + q8 = r3 + r10
  m34 : q1 + q10 = r1 + r2 + r10
  m35 : q1 + q4 + q7 = r2 + r10
  m36 : q1 + q3 + q6 = r1 + r10
  m45 : q1 + q2 + q5 = r2 + r4 + r7 + r10
  m46 : q1 + q2 + q5 = r1 + r3 + r6 + r10
  m56 : q1 + q2 + q5 = r0 + r10

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

/-- The anchors are pinned, the top matches the bottom, and the shell mass
on the disjunction set is positive. -/
theorem MomentSystem.facts {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) :
    q0 = 1/6 ∧ q10 = 1/6 ∧ q0 = r10 ∧ q1 = r9 ∧ q2 = r8 ∧ q5 = r5 ∧ q10 = r0 ∧ q1 + q2 + q5 = 1/3 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, m12, m13, m14, m15, m16, m23, m24, m25, m26, m34, m35, m36, m45, m46, m56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-! ## The reciprocal relations -/

def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),
      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

theorem ex_ef6_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w0 = star (c y0) * d z9 + star (c y1) * d z10 := by
  unfold offSum
  rw [incidence_ef6]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef6_9, flip_ef6_10]
  simp only [sg_ef6_w0_9, sg_ef6_w0_10, SixQubit.signMul_false]
  try ring

theorem ex_ef5_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef5 w0 = star (c y0) * d z8 + star (c y2) * d z10 := by
  unfold offSum
  rw [incidence_ef5]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef5_8, flip_ef5_10]
  simp only [sg_ef5_w0_8, sg_ef5_w0_10, SixQubit.signMul_false]
  try ring

theorem ex_ef3_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w0 = star (c y0) * d z5 + star (c y5) * d z10 := by
  unfold offSum
  rw [incidence_ef3]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef3_5, flip_ef3_10]
  simp only [sg_ef3_w0_5, sg_ef3_w0_10, SixQubit.signMul_false]
  try ring

theorem ex_ef0_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w0 = star (c y0) * d z0 + star (c y10) * d z10 := by
  unfold offSum
  rw [incidence_ef0]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef0_0, flip_ef0_10]
  simp only [sg_ef0_w0_0, sg_ef0_w0_10, SixQubit.signMul_false]
  try ring

theorem ex_ef1_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w0 = star (c y1) * d z0 + star (c y3) * d z3 + star (c y4) * d z4 + star (c y6) * d z6 + star (c y7) * d z7 + star (c y10) * d z9 := by
  unfold offSum
  rw [incidence_ef1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef1_0, flip_ef1_3, flip_ef1_4, flip_ef1_6, flip_ef1_7, flip_ef1_9]
  simp only [sg_ef1_w0_0, sg_ef1_w0_3, sg_ef1_w0_4, sg_ef1_w0_6, sg_ef1_w0_7, sg_ef1_w0_9, SixQubit.signMul_false]
  try ring

theorem ex_ef1_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w1 = star (c y1) * d z0 - star (c y3) * d z3 - star (c y4) * d z4 - star (c y6) * d z6 - star (c y7) * d z7 + star (c y10) * d z9 := by
  unfold offSum
  rw [incidence_ef1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef1_0, flip_ef1_3, flip_ef1_4, flip_ef1_6, flip_ef1_7, flip_ef1_9]
  simp only [sg_ef1_w1_0, sg_ef1_w1_3, sg_ef1_w1_4, sg_ef1_w1_6, sg_ef1_w1_7, sg_ef1_w1_9, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef2_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w0 = star (c y2) * d z0 + star (c y3) * d z1 + star (c y4) * d z2 + star (c y8) * d z6 + star (c y9) * d z7 + star (c y10) * d z8 := by
  unfold offSum
  rw [incidence_ef2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef2_0, flip_ef2_1, flip_ef2_2, flip_ef2_6, flip_ef2_7, flip_ef2_8]
  simp only [sg_ef2_w0_0, sg_ef2_w0_1, sg_ef2_w0_2, sg_ef2_w0_6, sg_ef2_w0_7, sg_ef2_w0_8, SixQubit.signMul_false]
  try ring

theorem ex_ef2_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w1 = star (c y2) * d z0 - star (c y3) * d z1 - star (c y4) * d z2 - star (c y8) * d z6 - star (c y9) * d z7 + star (c y10) * d z8 := by
  unfold offSum
  rw [incidence_ef2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef2_0, flip_ef2_1, flip_ef2_2, flip_ef2_6, flip_ef2_7, flip_ef2_8]
  simp only [sg_ef2_w1_0, sg_ef2_w1_1, sg_ef2_w1_2, sg_ef2_w1_6, sg_ef2_w1_7, sg_ef2_w1_8, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef4_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w0 = star (c y5) * d z0 + star (c y6) * d z1 + star (c y7) * d z2 + star (c y8) * d z3 + star (c y9) * d z4 + star (c y10) * d z5 := by
  unfold offSum
  rw [incidence_ef4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef4_0, flip_ef4_1, flip_ef4_2, flip_ef4_3, flip_ef4_4, flip_ef4_5]
  simp only [sg_ef4_w0_0, sg_ef4_w0_1, sg_ef4_w0_2, sg_ef4_w0_3, sg_ef4_w0_4, sg_ef4_w0_5, SixQubit.signMul_false]
  try ring

theorem ex_ef4_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w1 = star (c y5) * d z0 - star (c y6) * d z1 - star (c y7) * d z2 - star (c y8) * d z3 - star (c y9) * d z4 + star (c y10) * d z5 := by
  unfold offSum
  rw [incidence_ef4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef4_0, flip_ef4_1, flip_ef4_2, flip_ef4_3, flip_ef4_4, flip_ef4_5]
  simp only [sg_ef4_w1_0, sg_ef4_w1_1, sg_ef4_w1_2, sg_ef4_w1_3, sg_ef4_w1_4, sg_ef4_w1_5, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

/-! ## The no-go -/

/-- **Orbit 50 is impossible.** -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)))
    (h0 : offSum c d ef0 w0 = 0)
    (h1 : offSum c d ef1 w0 = 0)
    (h2 : offSum c d ef1 w1 = 0)
    (h3 : offSum c d ef2 w0 = 0)
    (h4 : offSum c d ef2 w1 = 0)
    (h5 : offSum c d ef3 w0 = 0)
    (h6 : offSum c d ef4 w0 = 0)
    (h7 : offSum c d ef4 w1 = 0)
    (h8 : offSum c d ef5 w0 = 0)
    (h9 : offSum c d ef6 w0 = 0)
    : False := by
  rw [ex_ef0_w0] at h0
  rw [ex_ef1_w0] at h1
  rw [ex_ef1_w1] at h2
  rw [ex_ef2_w0] at h3
  rw [ex_ef2_w1] at h4
  rw [ex_ef3_w0] at h5
  rw [ex_ef4_w0] at h6
  rw [ex_ef4_w1] at h7
  rw [ex_ef5_w0] at h8
  rw [ex_ef6_w0] at h9
  have relo_0_10 : star (c y0) * d z0 + star (c y10) * d z10 = 0 := by
    linear_combination (1 : ℂ) * h0
  have relo_0_1 : star (c y0) * d z9 + star (c y1) * d z10 = 0 := by
    linear_combination (1 : ℂ) * h9
  have relo_0_2 : star (c y0) * d z8 + star (c y2) * d z10 = 0 := by
    linear_combination (1 : ℂ) * h8
  have relo_0_5 : star (c y0) * d z5 + star (c y5) * d z10 = 0 := by
    linear_combination (1 : ℂ) * h5
  have relo_10_1 : star (c y10) * d z9 + star (c y1) * d z0 = 0 := by
    linear_combination (1/2 : ℂ) * h1 + (1/2 : ℂ) * h2
  have relo_10_2 : star (c y10) * d z8 + star (c y2) * d z0 = 0 := by
    linear_combination (1/2 : ℂ) * h3 + (1/2 : ℂ) * h4
  have relo_10_5 : star (c y10) * d z5 + star (c y5) * d z0 = 0 := by
    linear_combination (1/2 : ℂ) * h6 + (1/2 : ℂ) * h7
  obtain ⟨fA, fB, mt0, mt1, mt2, mt5, mt10, fs⟩ := hm.facts
  have pos0 : 0 < Complex.normSq (c y0) := by rw [fA]; norm_num
  have post0 : 0 < Complex.normSq (d z10) := by rw [← mt0]; exact pos0
  have pos10 : 0 < Complex.normSq (c y10) := by rw [fB]; norm_num
  have post10 : 0 < Complex.normSq (d z0) := by rw [← mt10]; exact pos10
  have alt : 0 < Complex.normSq (c y1) ∨ 0 < Complex.normSq (c y2) ∨ 0 < Complex.normSq (c y5) := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨a0, a1, a2⟩ := hcon
    have nn1 := Complex.normSq_nonneg (c y1)
    have nn2 := Complex.normSq_nonneg (c y2)
    have nn5 := Complex.normSq_nonneg (c y5)
    linarith
  rcases alt with hk1 | hk2 | hk5
  · have postk : 0 < Complex.normSq (d z9) := by rw [← mt1]; exact hk1
    exact SixQubit.Triangle.contradiction_of_normSq relo_0_10 relo_0_1 relo_10_1 hk1 post0 post10
  · have postk : 0 < Complex.normSq (d z8) := by rw [← mt2]; exact hk2
    exact SixQubit.Triangle.contradiction_of_normSq relo_0_10 relo_0_2 relo_10_2 hk2 post0 post10
  · have postk : 0 < Complex.normSq (d z5) := by rw [← mt5]; exact hk5
    exact SixQubit.Triangle.contradiction_of_normSq relo_0_10 relo_0_5 relo_10_5 hk5 post0 post10

end

end SixQubit.Orbit50
