import Mathlib

import SS.FullKL
import SixQubit.Common

/-!
# Six-qubit no-go for moment orbit 53

Orbit 53 of `six_qubit_sslp.tex`: q = 6, angle vector
a = (1, 1, 1, 3, 3, 4).  The projective order is m = 6, so the residue that has to
be excluded is delta = q/m = 1: `S0` is the residue-0 fiber, `S1` the
residue-1 fiber, and the two are complementary.

Write `u i = star (c y i)` and `v j = d z (top j)`, where `top j` indexes
the complement of `y j`.  The three weight-one flips 100000, 010000 and
001000 each have four incidences and a rank-three system of admissible
dressings; row reduction gives one equality row and two reciprocal rows
per flip.  Squared moduli of the reciprocal rows are the three quadratic
moment relations

    q0 q3 = q1 q2 ,    q0 q5 = q1 q4 ,    q0 q7 = q1 q6 ,

whose quadratic parts cancel identically against the linear moment
identities.  They pin the whole moment point: `q0 = q1 = 1/6` and every
other probability is `1/12`, so no amplitude vanishes (`pinned`).

The flips 000011 and 000101 give `u0 v9 + u9 v0 = 0` and
`u1 v9 + u9 v1 = 0`; eliminating `v9` and cancelling the nonzero `u9`
gives `u1 v0 = u0 v1`.  Substituted into the two remaining reciprocal
rows this yields `u1 u4 + u0 u5 = 0` and `u1 u6 + u0 u7 = 0`, and the
four-incidence flip 100001 then collapses to `u0 u5 u7 v0 = 0`, which
contradicts the pinned point.  Nothing is ever divided: each cancellation
is a `mul_eq_zero` split against a pinned positive probability.

Everything computational is decided by the Lean kernel; `native_decide`
is not used.
-/

namespace SixQubit.Orbit53

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

/-! ## The two fibers -/

def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]

def y0 : SS.BitString 6 := bs false false false false false false  -- 000000
def y1 : SS.BitString 6 := bs false false false true  true  false  -- 000110
def y2 : SS.BitString 6 := bs false true  true  false false true   -- 011001
def y3 : SS.BitString 6 := bs false true  true  true  true  true   -- 011111
def y4 : SS.BitString 6 := bs true  false true  false false true   -- 101001
def y5 : SS.BitString 6 := bs true  false true  true  true  true   -- 101111
def y6 : SS.BitString 6 := bs true  true  false false false true   -- 110001
def y7 : SS.BitString 6 := bs true  true  false true  true  true   -- 110111
def y8 : SS.BitString 6 := bs true  true  true  false true  false  -- 111010
def y9 : SS.BitString 6 := bs true  true  true  true  false false  -- 111100

def z0 : SS.BitString 6 := bs false false false false true  true   -- 000011
def z1 : SS.BitString 6 := bs false false false true  false true   -- 000101
def z2 : SS.BitString 6 := bs false false true  false false false  -- 001000
def z3 : SS.BitString 6 := bs false false true  true  true  false  -- 001110
def z4 : SS.BitString 6 := bs false true  false false false false  -- 010000
def z5 : SS.BitString 6 := bs false true  false true  true  false  -- 010110
def z6 : SS.BitString 6 := bs true  false false false false false  -- 100000
def z7 : SS.BitString 6 := bs true  false false true  true  false  -- 100110
def z8 : SS.BitString 6 := bs true  true  true  false false true   -- 111001
def z9 : SS.BitString 6 := bs true  true  true  true  true  true   -- 111111

def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9}
def S1 : Finset (SS.BitString 6) := {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9}

def av : Fin 6 -> ZMod 6 := ![1, 1, 1, 3, 3, 4]

theorem S0_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 0) = S0 := by
  decide

theorem S1_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 1) = S1 := by
  decide

/-! ## Flip masks, incidences and signs -/

def ef0 : SS.BitString 6 := bs false false false false true  true   -- 000011
def ef1 : SS.BitString 6 := bs false false false true  false true   -- 000101
def ef2 : SS.BitString 6 := bs false false true  false false false  -- 001000
def ef3 : SS.BitString 6 := bs false true  false false false false  -- 010000
def ef4 : SS.BitString 6 := bs true  false false false false false  -- 100000
def ef5 : SS.BitString 6 := bs true  false false false false true   -- 100001
def w0 : SS.BitString 6 := bs false false false false false false  -- 000000
def w1 : SS.BitString 6 := bs false false false false false true   -- 000001
def w2 : SS.BitString 6 := bs false false false false true  false  -- 000010
def w3 : SS.BitString 6 := bs false false false true  false false  -- 000100

theorem incidence_ef0 :
    S1.filter (fun y => SS.bxor y ef0 ∈ S0) = {z0, z1, z8, z9} := by decide
theorem flip_ef0_0 : SS.bxor z0 ef0 = y0 := by decide
theorem flip_ef0_1 : SS.bxor z1 ef0 = y1 := by decide
theorem flip_ef0_8 : SS.bxor z8 ef0 = y8 := by decide
theorem flip_ef0_9 : SS.bxor z9 ef0 = y9 := by decide
theorem sg_ef0_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg_ef0_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg_ef0_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_ef0_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg_ef0_w2_0 : SS.bdot w2 z0 = true := by decide
theorem sg_ef0_w2_1 : SS.bdot w2 z1 = false := by decide
theorem sg_ef0_w2_8 : SS.bdot w2 z8 = false := by decide
theorem sg_ef0_w2_9 : SS.bdot w2 z9 = true := by decide

theorem incidence_ef1 :
    S1.filter (fun y => SS.bxor y ef1 ∈ S0) = {z0, z1, z8, z9} := by decide
theorem flip_ef1_0 : SS.bxor z0 ef1 = y1 := by decide
theorem flip_ef1_1 : SS.bxor z1 ef1 = y0 := by decide
theorem flip_ef1_8 : SS.bxor z8 ef1 = y9 := by decide
theorem flip_ef1_9 : SS.bxor z9 ef1 = y8 := by decide
theorem sg_ef1_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg_ef1_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg_ef1_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_ef1_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg_ef1_w3_0 : SS.bdot w3 z0 = false := by decide
theorem sg_ef1_w3_1 : SS.bdot w3 z1 = true := by decide
theorem sg_ef1_w3_8 : SS.bdot w3 z8 = false := by decide
theorem sg_ef1_w3_9 : SS.bdot w3 z9 = true := by decide

theorem incidence_ef2 :
    S1.filter (fun y => SS.bxor y ef2 ∈ S0) = {z2, z3, z8, z9} := by decide
theorem flip_ef2_2 : SS.bxor z2 ef2 = y0 := by decide
theorem flip_ef2_3 : SS.bxor z3 ef2 = y1 := by decide
theorem flip_ef2_8 : SS.bxor z8 ef2 = y6 := by decide
theorem flip_ef2_9 : SS.bxor z9 ef2 = y7 := by decide
theorem sg_ef2_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg_ef2_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg_ef2_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_ef2_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg_ef2_w1_2 : SS.bdot w1 z2 = false := by decide
theorem sg_ef2_w1_3 : SS.bdot w1 z3 = false := by decide
theorem sg_ef2_w1_8 : SS.bdot w1 z8 = true := by decide
theorem sg_ef2_w1_9 : SS.bdot w1 z9 = true := by decide
theorem sg_ef2_w2_2 : SS.bdot w2 z2 = false := by decide
theorem sg_ef2_w2_3 : SS.bdot w2 z3 = true := by decide
theorem sg_ef2_w2_8 : SS.bdot w2 z8 = false := by decide
theorem sg_ef2_w2_9 : SS.bdot w2 z9 = true := by decide

theorem incidence_ef3 :
    S1.filter (fun y => SS.bxor y ef3 ∈ S0) = {z4, z5, z8, z9} := by decide
theorem flip_ef3_4 : SS.bxor z4 ef3 = y0 := by decide
theorem flip_ef3_5 : SS.bxor z5 ef3 = y1 := by decide
theorem flip_ef3_8 : SS.bxor z8 ef3 = y4 := by decide
theorem flip_ef3_9 : SS.bxor z9 ef3 = y5 := by decide
theorem sg_ef3_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg_ef3_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg_ef3_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_ef3_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg_ef3_w1_4 : SS.bdot w1 z4 = false := by decide
theorem sg_ef3_w1_5 : SS.bdot w1 z5 = false := by decide
theorem sg_ef3_w1_8 : SS.bdot w1 z8 = true := by decide
theorem sg_ef3_w1_9 : SS.bdot w1 z9 = true := by decide
theorem sg_ef3_w2_4 : SS.bdot w2 z4 = false := by decide
theorem sg_ef3_w2_5 : SS.bdot w2 z5 = true := by decide
theorem sg_ef3_w2_8 : SS.bdot w2 z8 = false := by decide
theorem sg_ef3_w2_9 : SS.bdot w2 z9 = true := by decide

theorem incidence_ef4 :
    S1.filter (fun y => SS.bxor y ef4 ∈ S0) = {z6, z7, z8, z9} := by decide
theorem flip_ef4_6 : SS.bxor z6 ef4 = y0 := by decide
theorem flip_ef4_7 : SS.bxor z7 ef4 = y1 := by decide
theorem flip_ef4_8 : SS.bxor z8 ef4 = y2 := by decide
theorem flip_ef4_9 : SS.bxor z9 ef4 = y3 := by decide
theorem sg_ef4_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg_ef4_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg_ef4_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_ef4_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg_ef4_w2_6 : SS.bdot w2 z6 = false := by decide
theorem sg_ef4_w2_7 : SS.bdot w2 z7 = true := by decide
theorem sg_ef4_w2_8 : SS.bdot w2 z8 = false := by decide
theorem sg_ef4_w2_9 : SS.bdot w2 z9 = true := by decide

theorem incidence_ef5 :
    S1.filter (fun y => SS.bxor y ef5 ∈ S0) = {z2, z3, z4, z5} := by decide
theorem flip_ef5_2 : SS.bxor z2 ef5 = y4 := by decide
theorem flip_ef5_3 : SS.bxor z3 ef5 = y5 := by decide
theorem flip_ef5_4 : SS.bxor z4 ef5 = y6 := by decide
theorem flip_ef5_5 : SS.bxor z5 ef5 = y7 := by decide
theorem sg_ef5_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg_ef5_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg_ef5_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg_ef5_w0_5 : SS.bdot w0 z5 = false := by decide

/-! ## The moment system -/

/-- The two normalizations, the twenty-one moment equalities, and the
nonnegativity of every probability. -/
structure MomentSystem (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Real) : Prop where
  n0 : q0 + q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 + q9 = 1
  n1 : r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 = 1
  m1 : q4 + q5 + q6 + q7 + q8 + q9 = r6 + r7 + r8 + r9
  m2 : q2 + q3 + q6 + q7 + q8 + q9 = r4 + r5 + r8 + r9
  m3 : q2 + q3 + q4 + q5 + q8 + q9 = r2 + r3 + r8 + r9
  m4 : q1 + q3 + q5 + q7 + q9 = r1 + r3 + r5 + r7 + r9
  m5 : q1 + q3 + q5 + q7 + q8 = r0 + r3 + r5 + r7 + r9
  m6 : q2 + q3 + q4 + q5 + q6 + q7 = r0 + r1 + r8 + r9
  m12 : q6 + q7 + q8 + q9 = r8 + r9
  m13 : q4 + q5 + q8 + q9 = r8 + r9
  m14 : q5 + q7 + q9 = r7 + r9
  m15 : q5 + q7 + q8 = r7 + r9
  m16 : q4 + q5 + q6 + q7 = r8 + r9
  m23 : q2 + q3 + q8 + q9 = r8 + r9
  m24 : q3 + q7 + q9 = r5 + r9
  m25 : q3 + q7 + q8 = r5 + r9
  m26 : q2 + q3 + q6 + q7 = r8 + r9
  m34 : q3 + q5 + q9 = r3 + r9
  m35 : q3 + q5 + q8 = r3 + r9
  m36 : q2 + q3 + q4 + q5 = r8 + r9
  m45 : q1 + q3 + q5 + q7 = r3 + r5 + r7 + r9
  m46 : q3 + q5 + q7 = r1 + r9
  m56 : q3 + q5 + q7 = r0 + r9

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

/-- The linear consequences of the moment system that the pinning uses,
and the four identifications of a top probability with the bottom
probability at the complementary string. -/
theorem MomentSystem.facts {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) :
    q4 + q5 = 1/6 ∧ q6 + q7 = 1/6 ∧ q0 + q1 = 1/3 ∧ q3 + 1/4 = q4 + q6 + q0 ∧ q2 + q4 + q6 + q0 = 5/12 ∧ q9 = 1/12 ∧ r7 = q2 ∧ r5 = q4 ∧ r3 = q6 ∧ r9 = q0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, m12, m13, m14, m15, m16, m23, m24, m25, m26, m34, m35, m36, m45, m46, m56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- The four identifications of a top probability with the bottom
probability at the complementary string, used to turn the reciprocal rows
into relations among bottom probabilities alone. -/
theorem MomentSystem.endpoints {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) :
    r7 = q2 ∧ r5 = q4 ∧ r3 = q6 ∧ r9 = q0 := by
  obtain ⟨_, _, _, _, _, _, a1, a2, a3, a4⟩ := h.facts
  exact ⟨a1, a2, a3, a4⟩

/-- The one probability the moment polytope pins on its own. -/
theorem MomentSystem.endpoints_pos {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) :
    0 < q9 := by
  obtain ⟨_, _, _, _, _, a, _, _, _, _⟩ := h.facts
  linarith

/-! ## Pinning the moment point -/

/-- The three quadratic relations have identically cancelling quadratic
parts, so together with the linear moment identities they force the
unique interior point. -/
theorem pinned {q0 q1 q2 q3 q4 q5 q6 q7 : Real}
    (f1 : q4 + q5 = 1/6) (f2 : q6 + q7 = 1/6) (f3 : q0 + q1 = 1/3)
    (f4 : q3 + 1/4 = q4 + q6 + q0) (f5 : q2 + q4 + q6 + q0 = 5/12)
    (M1 : q0 * q3 = q1 * q2) (M2 : q0 * q5 = q1 * q4)
    (M3 : q0 * q7 = q1 * q6) :
    q0 = 1/6 ∧ q5 = 1/12 ∧ q7 = 1/12 := by
  have e1 : q1 = 1/3 - q0 := by linarith
  have e5 : q5 = 1/6 - q4 := by linarith
  have e7 : q7 = 1/6 - q6 := by linarith
  rw [e5, e1] at M2
  rw [e7, e1] at M3
  have h4 : q4 = q0 / 2 := by linear_combination (-3 : Real) * M2
  have h6 : q6 = q0 / 2 := by linear_combination (-3 : Real) * M3
  have e3 : q3 = 2 * q0 - 1/4 := by linarith
  have e2 : q2 = 5/12 - 2 * q0 := by linarith
  rw [e3, e2, e1] at M1
  have h0 : q0 = 1/6 := by linear_combination (6/5 : Real) * M1
  refine ⟨h0, ?_, ?_⟩
  · rw [e5, h4, h0]; norm_num
  · rw [e7, h6, h0]; norm_num

/-! ## The Walsh expansions -/

def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),
      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

theorem ex_ef0_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w0 = star (c y0) * d z0 + star (c y1) * d z1 + star (c y8) * d z8 + star (c y9) * d z9 := by
  unfold offSum
  rw [incidence_ef0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef0_0, flip_ef0_1, flip_ef0_8, flip_ef0_9]
  simp only [sg_ef0_w0_0, sg_ef0_w0_1, sg_ef0_w0_8, sg_ef0_w0_9, SixQubit.signMul_false]
  try ring

theorem ex_ef0_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w2 = - star (c y0) * d z0 + star (c y1) * d z1 + star (c y8) * d z8 - star (c y9) * d z9 := by
  unfold offSum
  rw [incidence_ef0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef0_0, flip_ef0_1, flip_ef0_8, flip_ef0_9]
  simp only [sg_ef0_w2_0, sg_ef0_w2_1, sg_ef0_w2_8, sg_ef0_w2_9, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef1_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w0 = star (c y1) * d z0 + star (c y0) * d z1 + star (c y9) * d z8 + star (c y8) * d z9 := by
  unfold offSum
  rw [incidence_ef1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef1_0, flip_ef1_1, flip_ef1_8, flip_ef1_9]
  simp only [sg_ef1_w0_0, sg_ef1_w0_1, sg_ef1_w0_8, sg_ef1_w0_9, SixQubit.signMul_false]
  try ring

theorem ex_ef1_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w3 = star (c y1) * d z0 - star (c y0) * d z1 + star (c y9) * d z8 - star (c y8) * d z9 := by
  unfold offSum
  rw [incidence_ef1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef1_0, flip_ef1_1, flip_ef1_8, flip_ef1_9]
  simp only [sg_ef1_w3_0, sg_ef1_w3_1, sg_ef1_w3_8, sg_ef1_w3_9, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef2_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w0 = star (c y0) * d z2 + star (c y1) * d z3 + star (c y6) * d z8 + star (c y7) * d z9 := by
  unfold offSum
  rw [incidence_ef2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef2_2, flip_ef2_3, flip_ef2_8, flip_ef2_9]
  simp only [sg_ef2_w0_2, sg_ef2_w0_3, sg_ef2_w0_8, sg_ef2_w0_9, SixQubit.signMul_false]
  try ring

theorem ex_ef2_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w1 = star (c y0) * d z2 + star (c y1) * d z3 - star (c y6) * d z8 - star (c y7) * d z9 := by
  unfold offSum
  rw [incidence_ef2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef2_2, flip_ef2_3, flip_ef2_8, flip_ef2_9]
  simp only [sg_ef2_w1_2, sg_ef2_w1_3, sg_ef2_w1_8, sg_ef2_w1_9, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef2_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w2 = star (c y0) * d z2 - star (c y1) * d z3 + star (c y6) * d z8 - star (c y7) * d z9 := by
  unfold offSum
  rw [incidence_ef2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef2_2, flip_ef2_3, flip_ef2_8, flip_ef2_9]
  simp only [sg_ef2_w2_2, sg_ef2_w2_3, sg_ef2_w2_8, sg_ef2_w2_9, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef3_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w0 = star (c y0) * d z4 + star (c y1) * d z5 + star (c y4) * d z8 + star (c y5) * d z9 := by
  unfold offSum
  rw [incidence_ef3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef3_4, flip_ef3_5, flip_ef3_8, flip_ef3_9]
  simp only [sg_ef3_w0_4, sg_ef3_w0_5, sg_ef3_w0_8, sg_ef3_w0_9, SixQubit.signMul_false]
  try ring

theorem ex_ef3_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w1 = star (c y0) * d z4 + star (c y1) * d z5 - star (c y4) * d z8 - star (c y5) * d z9 := by
  unfold offSum
  rw [incidence_ef3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef3_4, flip_ef3_5, flip_ef3_8, flip_ef3_9]
  simp only [sg_ef3_w1_4, sg_ef3_w1_5, sg_ef3_w1_8, sg_ef3_w1_9, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef3_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w2 = star (c y0) * d z4 - star (c y1) * d z5 + star (c y4) * d z8 - star (c y5) * d z9 := by
  unfold offSum
  rw [incidence_ef3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef3_4, flip_ef3_5, flip_ef3_8, flip_ef3_9]
  simp only [sg_ef3_w2_4, sg_ef3_w2_5, sg_ef3_w2_8, sg_ef3_w2_9, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef4_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w0 = star (c y0) * d z6 + star (c y1) * d z7 + star (c y2) * d z8 + star (c y3) * d z9 := by
  unfold offSum
  rw [incidence_ef4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef4_6, flip_ef4_7, flip_ef4_8, flip_ef4_9]
  simp only [sg_ef4_w0_6, sg_ef4_w0_7, sg_ef4_w0_8, sg_ef4_w0_9, SixQubit.signMul_false]
  try ring

theorem ex_ef4_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w2 = star (c y0) * d z6 - star (c y1) * d z7 + star (c y2) * d z8 - star (c y3) * d z9 := by
  unfold offSum
  rw [incidence_ef4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef4_6, flip_ef4_7, flip_ef4_8, flip_ef4_9]
  simp only [sg_ef4_w2_6, sg_ef4_w2_7, sg_ef4_w2_8, sg_ef4_w2_9, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef5_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef5 w0 = star (c y4) * d z2 + star (c y5) * d z3 + star (c y6) * d z4 + star (c y7) * d z5 := by
  unfold offSum
  rw [incidence_ef5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef5_2, flip_ef5_3, flip_ef5_4, flip_ef5_5]
  simp only [sg_ef5_w0_2, sg_ef5_w0_3, sg_ef5_w0_4, sg_ef5_w0_5, SixQubit.signMul_false]
  try ring

/-! ## The reduced Walsh rows -/

/-- Row reduction of the admissible dressings of the six flip masks. -/
theorem rows (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef0 w0 = 0)
    (h1 : offSum c d ef0 w2 = 0)
    (h2 : offSum c d ef1 w0 = 0)
    (h3 : offSum c d ef1 w3 = 0)
    (h4 : offSum c d ef2 w0 = 0)
    (h5 : offSum c d ef2 w1 = 0)
    (h6 : offSum c d ef2 w2 = 0)
    (h7 : offSum c d ef3 w0 = 0)
    (h8 : offSum c d ef3 w1 = 0)
    (h9 : offSum c d ef3 w2 = 0)
    (h10 : offSum c d ef4 w0 = 0)
    (h11 : offSum c d ef4 w2 = 0)
    (h12 : offSum c d ef5 w0 = 0) :
    star (c y1) * d z7 + star (c y3) * d z9 = 0
      ∧ star (c y0) * d z4 - star (c y5) * d z9 = 0
      ∧ star (c y1) * d z5 + star (c y5) * d z9 = 0
      ∧ star (c y4) * d z8 + star (c y5) * d z9 = 0
      ∧ star (c y0) * d z2 - star (c y7) * d z9 = 0
      ∧ star (c y1) * d z3 + star (c y7) * d z9 = 0
      ∧ star (c y6) * d z8 + star (c y7) * d z9 = 0
      ∧ star (c y0) * d z0 + star (c y9) * d z9 = 0
      ∧ star (c y1) * d z0 + star (c y9) * d z8 = 0
      ∧ star (c y4) * d z2 + star (c y5) * d z3 + star (c y6) * d z4 + star (c y7) * d z5 = 0 := by
  rw [ex_ef0_w0] at h0
  rw [ex_ef0_w2] at h1
  rw [ex_ef1_w0] at h2
  rw [ex_ef1_w3] at h3
  rw [ex_ef2_w0] at h4
  rw [ex_ef2_w1] at h5
  rw [ex_ef2_w2] at h6
  rw [ex_ef3_w0] at h7
  rw [ex_ef3_w1] at h8
  rw [ex_ef3_w2] at h9
  rw [ex_ef4_w0] at h10
  rw [ex_ef4_w2] at h11
  rw [ex_ef5_w0] at h12
  have K1 : star (c y1) * d z7 + star (c y3) * d z9 = 0 := by
    linear_combination (1/2 : ℂ) * h10 + (-1/2 : ℂ) * h11
  have E4 : star (c y0) * d z4 - star (c y5) * d z9 = 0 := by
    linear_combination (1/2 : ℂ) * h8 + (1/2 : ℂ) * h9
  have E5 : star (c y1) * d z5 + star (c y5) * d z9 = 0 := by
    linear_combination (1/2 : ℂ) * h7 + (-1/2 : ℂ) * h9
  have E6 : star (c y4) * d z8 + star (c y5) * d z9 = 0 := by
    linear_combination (1/2 : ℂ) * h7 + (-1/2 : ℂ) * h8
  have E7 : star (c y0) * d z2 - star (c y7) * d z9 = 0 := by
    linear_combination (1/2 : ℂ) * h5 + (1/2 : ℂ) * h6
  have E8 : star (c y1) * d z3 + star (c y7) * d z9 = 0 := by
    linear_combination (1/2 : ℂ) * h4 + (-1/2 : ℂ) * h6
  have E9 : star (c y6) * d z8 + star (c y7) * d z9 = 0 := by
    linear_combination (1/2 : ℂ) * h4 + (-1/2 : ℂ) * h5
  have EA : star (c y0) * d z0 + star (c y9) * d z9 = 0 := by
    linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1
  have EB : star (c y1) * d z0 + star (c y9) * d z8 = 0 := by
    linear_combination (1/2 : ℂ) * h2 + (1/2 : ℂ) * h3
  have GG : star (c y4) * d z2 + star (c y5) * d z3 + star (c y6) * d z4 + star (c y7) * d z5 = 0 := by
    linear_combination (1 : ℂ) * h12
  exact ⟨K1, E4, E5, E6, E7, E8, E9, EA, EB, GG⟩

/-! ## The target product -/

/-- Phase synchronisation collapses the four-incidence flip 100001 to a
single product; the only input beyond the Walsh rows is that the amplitude
at `y9` does not vanish. -/
theorem target_zero (c d : SS.BitString 6 -> ℂ) (nu9 : star (c y9) ≠ 0)
    (h0 : offSum c d ef0 w0 = 0)
    (h1 : offSum c d ef0 w2 = 0)
    (h2 : offSum c d ef1 w0 = 0)
    (h3 : offSum c d ef1 w3 = 0)
    (h4 : offSum c d ef2 w0 = 0)
    (h5 : offSum c d ef2 w1 = 0)
    (h6 : offSum c d ef2 w2 = 0)
    (h7 : offSum c d ef3 w0 = 0)
    (h8 : offSum c d ef3 w1 = 0)
    (h9 : offSum c d ef3 w2 = 0)
    (h10 : offSum c d ef4 w0 = 0)
    (h11 : offSum c d ef4 w2 = 0)
    (h12 : offSum c d ef5 w0 = 0) :
    star (c y0) * star (c y5) * star (c y7) * d z9 = 0 := by
  obtain ⟨_, E4, E5, E6, E7, E8, E9, EA, EB, GG⟩ := rows c d h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  have hP0 : star (c y9) * (star (c y1) * d z9 - star (c y0) * d z8) = 0 := by
    linear_combination (star (c y1) : ℂ) * EA - (star (c y0) : ℂ) * EB
  have hP : star (c y1) * d z9 - star (c y0) * d z8 = 0 := by
    rcases mul_eq_zero.mp hP0 with hx | hx
    · exact absurd hx nu9
    · exact hx
  have hQ2a : d z9 * (star (c y1) * star (c y4) + star (c y0) * star (c y5)) = 0 := by
    linear_combination (star (c y0) : ℂ) * E6 + (star (c y4) : ℂ) * hP
  have hQ3a : d z9 * (star (c y1) * star (c y6) + star (c y0) * star (c y7)) = 0 := by
    linear_combination (star (c y0) : ℂ) * E9 + (star (c y6) : ℂ) * hP
  linear_combination (-(star (c y0) * star (c y1)) / 4 : ℂ) * GG
    + ((star (c y1) * star (c y4)) / 4 : ℂ) * E7 + ((star (c y0) * star (c y5)) / 4 : ℂ) * E8
    + ((star (c y1) * star (c y6)) / 4 : ℂ) * E4 + ((star (c y0) * star (c y7)) / 4 : ℂ) * E5
    + (star (c y7) / 4 : ℂ) * hQ2a + (star (c y5) / 4 : ℂ) * hQ3a

/-! ## The no-go -/

/-- **Orbit 53 is impossible.** -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)))
    (h0 : offSum c d ef0 w0 = 0)
    (h1 : offSum c d ef0 w2 = 0)
    (h2 : offSum c d ef1 w0 = 0)
    (h3 : offSum c d ef1 w3 = 0)
    (h4 : offSum c d ef2 w0 = 0)
    (h5 : offSum c d ef2 w1 = 0)
    (h6 : offSum c d ef2 w2 = 0)
    (h7 : offSum c d ef3 w0 = 0)
    (h8 : offSum c d ef3 w1 = 0)
    (h9 : offSum c d ef3 w2 = 0)
    (h10 : offSum c d ef4 w0 = 0)
    (h11 : offSum c d ef4 w2 = 0)
    (h12 : offSum c d ef5 w0 = 0)
    : False := by
  obtain ⟨K1, _, E5, _, _, E8, _, _, _, _⟩ := rows c d h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩ := hm.facts
  have M1 : Complex.normSq (c y0) * Complex.normSq (c y3) = Complex.normSq (c y1) * Complex.normSq (c y2) := by
    have hx : star (c y1) * d z7 = -(star (c y3) * d z9) := by linear_combination K1
    have hy : Complex.normSq (c y1) * Complex.normSq (d z7)
        = Complex.normSq (c y3) * Complex.normSq (d z9) := by
      simpa [Complex.normSq_mul] using congrArg Complex.normSq hx
    rw [f7, f10] at hy
    linear_combination (-1 : Real) * hy
  have M2 : Complex.normSq (c y0) * Complex.normSq (c y5) = Complex.normSq (c y1) * Complex.normSq (c y4) := by
    have hx : star (c y1) * d z5 = -(star (c y5) * d z9) := by linear_combination E5
    have hy : Complex.normSq (c y1) * Complex.normSq (d z5)
        = Complex.normSq (c y5) * Complex.normSq (d z9) := by
      simpa [Complex.normSq_mul] using congrArg Complex.normSq hx
    rw [f8, f10] at hy
    linear_combination (-1 : Real) * hy
  have M3 : Complex.normSq (c y0) * Complex.normSq (c y7) = Complex.normSq (c y1) * Complex.normSq (c y6) := by
    have hx : star (c y1) * d z3 = -(star (c y7) * d z9) := by linear_combination E8
    have hy : Complex.normSq (c y1) * Complex.normSq (d z3)
        = Complex.normSq (c y7) * Complex.normSq (d z9) := by
      simpa [Complex.normSq_mul] using congrArg Complex.normSq hx
    rw [f9, f10] at hy
    linear_combination (-1 : Real) * hy
  obtain ⟨p0, p5, p7⟩ := pinned f1 f2 f3 f4 f5 M1 M2 M3
  have nu0 : star (c y0) ≠ 0 := by
    intro hzero
    have hk : c y0 = 0 := by simpa using congrArg star hzero
    rw [hk, Complex.normSq_zero] at p0
    norm_num at p0
  have nu5 : star (c y5) ≠ 0 := by
    intro hzero
    have hk : c y5 = 0 := by simpa using congrArg star hzero
    rw [hk, Complex.normSq_zero] at p5
    norm_num at p5
  have nu7 : star (c y7) ≠ 0 := by
    intro hzero
    have hk : c y7 = 0 := by simpa using congrArg star hzero
    rw [hk, Complex.normSq_zero] at p7
    norm_num at p7
  have nu9 : star (c y9) ≠ 0 := by
    intro hzero
    have hk : c y9 = 0 := by simpa using congrArg star hzero
    rw [hk, Complex.normSq_zero] at f6
    norm_num at f6
  have nv0 : d z9 ≠ 0 := by
    intro hzero
    rw [hzero, Complex.normSq_zero, p0] at f10
    norm_num at f10
  have hfin := target_zero c d nu9 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero nu0 nu5) nu7) nv0) hfin

end

end SixQubit.Orbit53
