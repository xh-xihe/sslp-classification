import Mathlib

import SS.FullKL
import SixQubit.Common

/-!
# Six-qubit no-go for moment orbit 52

Orbit 52 of `six_qubit_sslp.tex`: q = 6, angle vector
a = (1, 2, 3, 3, 4, 4), residues 0 and 2.

The flip mask 000001 has 4 incidences, and the admissible dressings
isolate 4 of them individually.  For each isolated incidence the
moment system ties the two endpoint probabilities by a positive ratio,
so either branch of `mul_eq_zero` kills both.  The resulting vanishing
set is inconsistent with the moment system.

Everything computational is decided by the Lean kernel; `native_decide`
is not used.
-/

namespace SixQubit.Orbit52

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

/-! ## The two fibers -/

def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]

def y0 : SS.BitString 6 := bs false false false false false false  -- 000000
def y1 : SS.BitString 6 := bs false false true  true  false false  -- 001100
def y2 : SS.BitString 6 := bs false true  false false false true   -- 010001
def y3 : SS.BitString 6 := bs false true  false false true  false  -- 010010
def y4 : SS.BitString 6 := bs false true  true  true  false true   -- 011101
def y5 : SS.BitString 6 := bs false true  true  true  true  false  -- 011110
def y6 : SS.BitString 6 := bs true  false false true  true  true   -- 100111
def y7 : SS.BitString 6 := bs true  false true  false true  true   -- 101011
def y8 : SS.BitString 6 := bs true  true  false true  false false  -- 110100
def y9 : SS.BitString 6 := bs true  true  true  false false false  -- 111000

def z0 : SS.BitString 6 := bs false false false false true  true   -- 000011
def z1 : SS.BitString 6 := bs false false true  true  true  true   -- 001111
def z2 : SS.BitString 6 := bs false true  false false false false  -- 010000
def z3 : SS.BitString 6 := bs false true  true  true  false false  -- 011100
def z4 : SS.BitString 6 := bs true  false false true  false true   -- 100101
def z5 : SS.BitString 6 := bs true  false false true  true  false  -- 100110
def z6 : SS.BitString 6 := bs true  false true  false false true   -- 101001
def z7 : SS.BitString 6 := bs true  false true  false true  false  -- 101010
def z8 : SS.BitString 6 := bs true  true  false true  true  true   -- 110111
def z9 : SS.BitString 6 := bs true  true  true  false true  true   -- 111011

def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9}
def S1 : Finset (SS.BitString 6) := {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9}

def av : Fin 6 -> ZMod 6 := ![1, 2, 3, 3, 4, 4]

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
    S1.filter (fun y => SS.bxor y ef ∈ S0) = {z2, z3, z5, z7} := by decide

theorem flip_z2 : SS.bxor z2 ef = y2 := by decide
theorem flip_z3 : SS.bxor z3 ef = y4 := by decide
theorem flip_z5 : SS.bxor z5 ef = y6 := by decide
theorem flip_z7 : SS.bxor z7 ef = y7 := by decide

def w0 : SS.BitString 6 := bs false false false false false false  -- 000000
def w1 : SS.BitString 6 := bs false false false false true  false  -- 000010
def w2 : SS.BitString 6 := bs false false false true  false false  -- 000100
def w3 : SS.BitString 6 := bs false false true  false false false  -- 001000
theorem sg_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg_w1_2 : SS.bdot w1 z2 = false := by decide
theorem sg_w1_3 : SS.bdot w1 z3 = false := by decide
theorem sg_w1_5 : SS.bdot w1 z5 = true := by decide
theorem sg_w1_7 : SS.bdot w1 z7 = true := by decide
theorem sg_w2_2 : SS.bdot w2 z2 = false := by decide
theorem sg_w2_3 : SS.bdot w2 z3 = true := by decide
theorem sg_w2_5 : SS.bdot w2 z5 = true := by decide
theorem sg_w2_7 : SS.bdot w2 z7 = false := by decide
theorem sg_w3_2 : SS.bdot w3 z2 = false := by decide
theorem sg_w3_3 : SS.bdot w3 z3 = true := by decide
theorem sg_w3_5 : SS.bdot w3 z5 = false := by decide
theorem sg_w3_7 : SS.bdot w3 z7 = true := by decide

/-! ## The moment system -/

structure MomentSystem (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Real) : Prop where
  n0 : q0 + q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 + q9 = 1
  n1 : r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 = 1
  m1 : q6 + q7 + q8 + q9 = r4 + r5 + r6 + r7 + r8 + r9
  m2 : q2 + q3 + q4 + q5 + q8 + q9 = r2 + r3 + r8 + r9
  m3 : q1 + q4 + q5 + q7 + q9 = r1 + r3 + r6 + r7 + r9
  m4 : q1 + q4 + q5 + q6 + q8 = r1 + r3 + r4 + r5 + r8
  m5 : q3 + q5 + q6 + q7 = r0 + r1 + r5 + r7 + r8 + r9
  m6 : q2 + q4 + q6 + q7 = r0 + r1 + r4 + r6 + r8 + r9
  m12 : q8 + q9 = r8 + r9
  m13 : q7 + q9 = r6 + r7 + r9
  m14 : q6 + q8 = r4 + r5 + r8
  m15 : q6 + q7 = r5 + r7 + r8 + r9
  m16 : q6 + q7 = r4 + r6 + r8 + r9
  m23 : q4 + q5 + q9 = r3 + r9
  m24 : q4 + q5 + q8 = r3 + r8
  m25 : q3 + q5 = r8 + r9
  m26 : q2 + q4 = r8 + r9
  m34 : q1 + q4 + q5 = r1 + r3
  m35 : q5 + q7 = r1 + r7 + r9
  m36 : q4 + q7 = r1 + r6 + r9
  m45 : q5 + q6 = r1 + r5 + r8
  m46 : q4 + q6 = r1 + r4 + r8
  m56 : q6 + q7 = r0 + r1 + r8 + r9

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
    q2 = (1/2) * r2 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, m12, m13, m14, m15, m16, m23, m24, m25, m26, m34, m35, m36, m45, m46, m56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9⟩ := h
  linarith

/-- Endpoint ratio at incidence 1. -/
theorem MomentSystem.ratio1 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) :
    q4 = (1/2) * r3 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, m12, m13, m14, m15, m16, m23, m24, m25, m26, m34, m35, m36, m45, m46, m56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9⟩ := h
  linarith

/-- Endpoint ratio at incidence 2. -/
theorem MomentSystem.ratio2 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) :
    q6 = (2) * r5 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, m12, m13, m14, m15, m16, m23, m24, m25, m26, m34, m35, m36, m45, m46, m56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9⟩ := h
  linarith

/-- Endpoint ratio at incidence 3. -/
theorem MomentSystem.ratio3 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) :
    q7 = (2) * r7 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, m12, m13, m14, m15, m16, m23, m24, m25, m26, m34, m35, m36, m45, m46, m56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9⟩ := h
  linarith

/-- Every isolated bottom probability vanishing is impossible. -/
theorem MomentSystem.absurd_zero {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9)
    (v0 : q2 = 0)
    (v1 : q4 = 0)
    (v2 : q6 = 0)
    (v3 : q7 = 0)
    : False := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, m12, m13, m14, m15, m16, m23, m24, m25, m26, m34, m35, m36, m45, m46, m56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9⟩ := h
  linarith

/-! ## The Walsh expansions -/

def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),
      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

theorem ex_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef w0 = star (c y2) * d z2 + star (c y4) * d z3 + star (c y6) * d z5 + star (c y7) * d z7 := by
  unfold offSum
  rw [incidence]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_z2, flip_z3, flip_z5, flip_z7]
  simp only [sg_w0_2, sg_w0_3, sg_w0_5, sg_w0_7, SixQubit.signMul_false]
  try ring

theorem ex_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef w1 = star (c y2) * d z2 + star (c y4) * d z3 - star (c y6) * d z5 - star (c y7) * d z7 := by
  unfold offSum
  rw [incidence]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_z2, flip_z3, flip_z5, flip_z7]
  simp only [sg_w1_2, sg_w1_3, sg_w1_5, sg_w1_7, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef w2 = star (c y2) * d z2 - star (c y4) * d z3 - star (c y6) * d z5 + star (c y7) * d z7 := by
  unfold offSum
  rw [incidence]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_z2, flip_z3, flip_z5, flip_z7]
  simp only [sg_w2_2, sg_w2_3, sg_w2_5, sg_w2_7, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef w3 = star (c y2) * d z2 - star (c y4) * d z3 + star (c y6) * d z5 - star (c y7) * d z7 := by
  unfold offSum
  rw [incidence]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_z2, flip_z3, flip_z5, flip_z7]
  simp only [sg_w3_2, sg_w3_3, sg_w3_5, sg_w3_7, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

/-! ## The no-go -/

/-- **Orbit 52 is impossible.** -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)))
    (h0 : offSum c d ef w0 = 0)
    (h1 : offSum c d ef w1 = 0)
    (h2 : offSum c d ef w2 = 0)
    (h3 : offSum c d ef w3 = 0)
    : False := by
  rw [ex_w0] at h0
  rw [ex_w1] at h1
  rw [ex_w2] at h2
  rw [ex_w3] at h3
  have key0 : star (c y2) * d z2 = 0 := by
    linear_combination (1/4 : ℂ) * h0 + (1/4 : ℂ) * h1 + (1/4 : ℂ) * h2 + (1/4 : ℂ) * h3
  have rat0 := hm.ratio0
  have van0 : Complex.normSq (c y2) = 0 := by
    rcases mul_eq_zero.mp key0 with hh | hh
    · have : c y2 = 0 := by simpa using congrArg star hh
      simp [this]
    · have hz : Complex.normSq (d z2) = 0 := by simp [hh]
      rw [rat0, hz]; ring
  have key1 : star (c y4) * d z3 = 0 := by
    linear_combination (1/4 : ℂ) * h0 + (1/4 : ℂ) * h1 + (-1/4 : ℂ) * h2 + (-1/4 : ℂ) * h3
  have rat1 := hm.ratio1
  have van1 : Complex.normSq (c y4) = 0 := by
    rcases mul_eq_zero.mp key1 with hh | hh
    · have : c y4 = 0 := by simpa using congrArg star hh
      simp [this]
    · have hz : Complex.normSq (d z3) = 0 := by simp [hh]
      rw [rat1, hz]; ring
  have key2 : star (c y6) * d z5 = 0 := by
    linear_combination (1/4 : ℂ) * h0 + (-1/4 : ℂ) * h1 + (-1/4 : ℂ) * h2 + (1/4 : ℂ) * h3
  have rat2 := hm.ratio2
  have van2 : Complex.normSq (c y6) = 0 := by
    rcases mul_eq_zero.mp key2 with hh | hh
    · have : c y6 = 0 := by simpa using congrArg star hh
      simp [this]
    · have hz : Complex.normSq (d z5) = 0 := by simp [hh]
      rw [rat2, hz]; ring
  have key3 : star (c y7) * d z7 = 0 := by
    linear_combination (1/4 : ℂ) * h0 + (-1/4 : ℂ) * h1 + (1/4 : ℂ) * h2 + (-1/4 : ℂ) * h3
  have rat3 := hm.ratio3
  have van3 : Complex.normSq (c y7) = 0 := by
    rcases mul_eq_zero.mp key3 with hh | hh
    · have : c y7 = 0 := by simpa using congrArg star hh
      simp [this]
    · have hz : Complex.normSq (d z7) = 0 := by simp [hh]
      rw [rat3, hz]; ring
  exact hm.absurd_zero van0 van1 van2 van3

end

end SixQubit.Orbit52
