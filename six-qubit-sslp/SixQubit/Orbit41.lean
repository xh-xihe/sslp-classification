import Mathlib

import SS.FullKL
import SixQubit.Common

/-!
# Six-qubit no-go for moment orbit 41

Orbit 41 of `six_qubit_sslp.tex`: q = 6, angle vector
a = (1, 1, 1, 1, 2, 3), residues 0 and 3.

The flip mask 000001 has 10 incidences on the two fibers.  A rational
combination of 4 admissible dressings isolates the single monomial
at (000000, 000001), while the moment polytope pins its two endpoint
probabilities to 1/4 and 1/4.  Both are positive, so the isolated
monomial cannot vanish.

Everything computational is decided by the Lean kernel; `native_decide`
is not used.
-/

namespace SixQubit.Orbit41

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

/-! ## The two fibers -/

def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]

def y0 : SS.BitString 6 := bs false false false false false false  -- 000000
def y1 : SS.BitString 6 := bs false false false true  true  true   -- 000111
def y2 : SS.BitString 6 := bs false false true  false true  true   -- 001011
def y3 : SS.BitString 6 := bs false true  false false true  true   -- 010011
def y4 : SS.BitString 6 := bs false true  true  true  false true   -- 011101
def y5 : SS.BitString 6 := bs true  false false false true  true   -- 100011
def y6 : SS.BitString 6 := bs true  false true  true  false true   -- 101101
def y7 : SS.BitString 6 := bs true  true  false true  false true   -- 110101
def y8 : SS.BitString 6 := bs true  true  true  false false true   -- 111001
def y9 : SS.BitString 6 := bs true  true  true  true  true  false  -- 111110

def z0 : SS.BitString 6 := bs false false false false false true   -- 000001
def z1 : SS.BitString 6 := bs false false false true  true  false  -- 000110
def z2 : SS.BitString 6 := bs false false true  false true  false  -- 001010
def z3 : SS.BitString 6 := bs false true  false false true  false  -- 010010
def z4 : SS.BitString 6 := bs false true  true  true  false false  -- 011100
def z5 : SS.BitString 6 := bs true  false false false true  false  -- 100010
def z6 : SS.BitString 6 := bs true  false true  true  false false  -- 101100
def z7 : SS.BitString 6 := bs true  true  false true  false false  -- 110100
def z8 : SS.BitString 6 := bs true  true  true  false false false  -- 111000
def z9 : SS.BitString 6 := bs true  true  true  true  true  true   -- 111111

def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9}
def S1 : Finset (SS.BitString 6) := {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9}

def av : Fin 6 -> ZMod 6 := ![1, 1, 1, 1, 2, 3]

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
theorem sg_w1_2 : SS.bdot w1 z2 = false := by decide
theorem sg_w1_3 : SS.bdot w1 z3 = false := by decide
theorem sg_w1_4 : SS.bdot w1 z4 = false := by decide
theorem sg_w1_5 : SS.bdot w1 z5 = false := by decide
theorem sg_w1_6 : SS.bdot w1 z6 = false := by decide
theorem sg_w1_7 : SS.bdot w1 z7 = false := by decide
theorem sg_w1_8 : SS.bdot w1 z8 = false := by decide
theorem sg_w1_9 : SS.bdot w1 z9 = true := by decide
theorem sg_w2_0 : SS.bdot w2 z0 = false := by decide
theorem sg_w2_1 : SS.bdot w2 z1 = true := by decide
theorem sg_w2_2 : SS.bdot w2 z2 = true := by decide
theorem sg_w2_3 : SS.bdot w2 z3 = true := by decide
theorem sg_w2_4 : SS.bdot w2 z4 = false := by decide
theorem sg_w2_5 : SS.bdot w2 z5 = true := by decide
theorem sg_w2_6 : SS.bdot w2 z6 = false := by decide
theorem sg_w2_7 : SS.bdot w2 z7 = false := by decide
theorem sg_w2_8 : SS.bdot w2 z8 = false := by decide
theorem sg_w2_9 : SS.bdot w2 z9 = true := by decide
theorem sg_w3_0 : SS.bdot w3 z0 = true := by decide
theorem sg_w3_1 : SS.bdot w3 z1 = true := by decide
theorem sg_w3_2 : SS.bdot w3 z2 = true := by decide
theorem sg_w3_3 : SS.bdot w3 z3 = true := by decide
theorem sg_w3_4 : SS.bdot w3 z4 = false := by decide
theorem sg_w3_5 : SS.bdot w3 z5 = true := by decide
theorem sg_w3_6 : SS.bdot w3 z6 = false := by decide
theorem sg_w3_7 : SS.bdot w3 z7 = false := by decide
theorem sg_w3_8 : SS.bdot w3 z8 = false := by decide
theorem sg_w3_9 : SS.bdot w3 z9 = false := by decide

/-! ## The moment system -/

/-- The two normalizations, the twenty-one moment equalities, and the
nonnegativity of every probability. -/
structure MomentSystem (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Real) : Prop where
  n0 : q0 + q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 + q9 = 1
  n1 : r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 = 1
  m1 : q5 + q6 + q7 + q8 + q9 = r5 + r6 + r7 + r8 + r9
  m2 : q3 + q4 + q7 + q8 + q9 = r3 + r4 + r7 + r8 + r9
  m3 : q2 + q4 + q6 + q8 + q9 = r2 + r4 + r6 + r8 + r9
  m4 : q1 + q4 + q6 + q7 + q9 = r1 + r4 + r6 + r7 + r9
  m5 : q1 + q2 + q3 + q5 + q9 = r1 + r2 + r3 + r5 + r9
  m6 : q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 = r0 + r9
  m12 : q7 + q8 + q9 = r7 + r8 + r9
  m13 : q6 + q8 + q9 = r6 + r8 + r9
  m14 : q6 + q7 + q9 = r6 + r7 + r9
  m15 : q5 + q9 = r5 + r9
  m16 : q5 + q6 + q7 + q8 = r9
  m23 : q4 + q8 + q9 = r4 + r8 + r9
  m24 : q4 + q7 + q9 = r4 + r7 + r9
  m25 : q3 + q9 = r3 + r9
  m26 : q3 + q4 + q7 + q8 = r9
  m34 : q4 + q6 + q9 = r4 + r6 + r9
  m35 : q2 + q9 = r2 + r9
  m36 : q2 + q4 + q6 + q8 = r9
  m45 : q1 + q9 = r1 + r9
  m46 : q1 + q4 + q6 + q7 = r9
  m56 : q1 + q2 + q3 + q5 = r9

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

/-- The two endpoint probabilities of the isolated incidence are forced. -/
theorem MomentSystem.endpoints {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Real}
    (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) :
    q0 = 1/4 ∧ r0 = 1/4 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, m12, m13, m14, m15, m16, m23, m24, m25, m26, m34, m35, m36, m45, m46, m56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9⟩ := h
  refine ⟨?_, ?_⟩ <;> linarith

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
    offSum c d ef w1 = - star (c y0) * d z0 + star (c y1) * d z1 + star (c y2) * d z2 + star (c y3) * d z3 + star (c y4) * d z4 + star (c y5) * d z5 + star (c y6) * d z6 + star (c y7) * d z7 + star (c y8) * d z8 - star (c y9) * d z9 := by
  unfold offSum
  rw [incidence]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_z0, flip_z1, flip_z2, flip_z3, flip_z4, flip_z5, flip_z6, flip_z7, flip_z8, flip_z9]
  simp only [sg_w1_0, sg_w1_1, sg_w1_2, sg_w1_3, sg_w1_4, sg_w1_5, sg_w1_6, sg_w1_7, sg_w1_8, sg_w1_9, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef w2 = star (c y0) * d z0 - star (c y1) * d z1 - star (c y2) * d z2 - star (c y3) * d z3 + star (c y4) * d z4 - star (c y5) * d z5 + star (c y6) * d z6 + star (c y7) * d z7 + star (c y8) * d z8 - star (c y9) * d z9 := by
  unfold offSum
  rw [incidence]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_z0, flip_z1, flip_z2, flip_z3, flip_z4, flip_z5, flip_z6, flip_z7, flip_z8, flip_z9]
  simp only [sg_w2_0, sg_w2_1, sg_w2_2, sg_w2_3, sg_w2_4, sg_w2_5, sg_w2_6, sg_w2_7, sg_w2_8, sg_w2_9, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef w3 = - star (c y0) * d z0 - star (c y1) * d z1 - star (c y2) * d z2 - star (c y3) * d z3 + star (c y4) * d z4 - star (c y5) * d z5 + star (c y6) * d z6 + star (c y7) * d z7 + star (c y8) * d z8 + star (c y9) * d z9 := by
  unfold offSum
  rw [incidence]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_z0, flip_z1, flip_z2, flip_z3, flip_z4, flip_z5, flip_z6, flip_z7, flip_z8, flip_z9]
  simp only [sg_w3_0, sg_w3_1, sg_w3_2, sg_w3_3, sg_w3_4, sg_w3_5, sg_w3_6, sg_w3_7, sg_w3_8, sg_w3_9, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

/-! ## The no-go -/

/-- **Orbit 41 is impossible.** -/
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
  have key : star (c y0) * d z0 = 0 := by
    linear_combination (1/4 : ℂ) * h0 + (-1/4 : ℂ) * h1 + (1/4 : ℂ) * h2 + (-1/4 : ℂ) * h3
  obtain ⟨hp, hq⟩ := hm.endpoints
  rcases mul_eq_zero.mp key with hh | hh
  · rw [show c y0 = 0 from by simpa using congrArg star hh] at hp
    simp at hp
  · rw [hh] at hq
    simp at hq

end

end SixQubit.Orbit41
