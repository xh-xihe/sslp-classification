import Mathlib

import SS.FullKL
import SixQubit.Common

/-!
# Six-qubit no-go for moment orbit 48

Orbit 48 of `six_qubit_sslp.tex`: q = 6, angle vector
a = (1, 1, 1, 2, 2, 2), residues 0 and 2.

The flip mask 000001 has 4 incidences on the two fibers.  A rational
combination of 2 admissible dressings isolates the single monomial
at (000000, 000001), while the moment polytope pins its two endpoint
probabilities to 1/3 and 1/6.  Both are positive, so the isolated
monomial cannot vanish.

Everything computational is decided by the Lean kernel; `native_decide`
is not used.
-/

namespace SixQubit.Orbit48

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

/-! ## The two fibers -/

def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]

def y0 : SS.BitString 6 := bs false false false false false false  -- 000000
def y1 : SS.BitString 6 := bs false false false true  true  true   -- 000111
def y2 : SS.BitString 6 := bs false true  true  false true  true   -- 011011
def y3 : SS.BitString 6 := bs false true  true  true  false true   -- 011101
def y4 : SS.BitString 6 := bs false true  true  true  true  false  -- 011110
def y5 : SS.BitString 6 := bs true  false true  false true  true   -- 101011
def y6 : SS.BitString 6 := bs true  false true  true  false true   -- 101101
def y7 : SS.BitString 6 := bs true  false true  true  true  false  -- 101110
def y8 : SS.BitString 6 := bs true  true  false false true  true   -- 110011
def y9 : SS.BitString 6 := bs true  true  false true  false true   -- 110101
def y10 : SS.BitString 6 := bs true  true  false true  true  false  -- 110110

def z0 : SS.BitString 6 := bs false false false false false true   -- 000001
def z1 : SS.BitString 6 := bs false false false false true  false  -- 000010
def z2 : SS.BitString 6 := bs false false false true  false false  -- 000100
def z3 : SS.BitString 6 := bs false true  true  false false false  -- 011000
def z4 : SS.BitString 6 := bs false true  true  true  true  true   -- 011111
def z5 : SS.BitString 6 := bs true  false true  false false false  -- 101000
def z6 : SS.BitString 6 := bs true  false true  true  true  true   -- 101111
def z7 : SS.BitString 6 := bs true  true  false false false false  -- 110000
def z8 : SS.BitString 6 := bs true  true  false true  true  true   -- 110111

def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10}
def S1 : Finset (SS.BitString 6) := {z0, z1, z2, z3, z4, z5, z6, z7, z8}

def av : Fin 6 -> ZMod 6 := ![1, 1, 1, 2, 2, 2]

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
    S1.filter (fun y => SS.bxor y ef ∈ S0) = {z0, z4, z6, z8} := by decide

theorem flip_z0 : SS.bxor z0 ef = y0 := by decide
theorem flip_z4 : SS.bxor z4 ef = y4 := by decide
theorem flip_z6 : SS.bxor z6 ef = y7 := by decide
theorem flip_z8 : SS.bxor z8 ef = y10 := by decide

def w0 : SS.BitString 6 := bs false false false false false false  -- 000000
def w1 : SS.BitString 6 := bs false false false false true  false  -- 000010
theorem sg_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_w1_0 : SS.bdot w1 z0 = false := by decide
theorem sg_w1_4 : SS.bdot w1 z4 = true := by decide
theorem sg_w1_6 : SS.bdot w1 z6 = true := by decide
theorem sg_w1_8 : SS.bdot w1 z8 = true := by decide

/-! ## The moment system -/

/-- The two normalizations, the twenty-one moment equalities, and the
nonnegativity of every probability. -/
structure MomentSystem (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 : Real) : Prop where
  n0 : q0 + q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 + q9 + q10 = 1
  n1 : r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 = 1
  m1 : q5 + q6 + q7 + q8 + q9 + q10 = r5 + r6 + r7 + r8
  m2 : q2 + q3 + q4 + q8 + q9 + q10 = r3 + r4 + r7 + r8
  m3 : q2 + q3 + q4 + q5 + q6 + q7 = r3 + r4 + r5 + r6
  m4 : q1 + q3 + q4 + q6 + q7 + q9 + q10 = r2 + r4 + r6 + r8
  m5 : q1 + q2 + q4 + q5 + q7 + q8 + q10 = r1 + r4 + r6 + r8
  m6 : q1 + q2 + q3 + q5 + q6 + q8 + q9 = r0 + r4 + r6 + r8
  m12 : q8 + q9 + q10 = r7 + r8
  m13 : q5 + q6 + q7 = r5 + r6
  m14 : q6 + q7 + q9 + q10 = r6 + r8
  m15 : q5 + q7 + q8 + q10 = r6 + r8
  m16 : q5 + q6 + q8 + q9 = r6 + r8
  m23 : q2 + q3 + q4 = r3 + r4
  m24 : q3 + q4 + q9 + q10 = r4 + r8
  m25 : q2 + q4 + q8 + q10 = r4 + r8
  m26 : q2 + q3 + q8 + q9 = r4 + r8
  m34 : q3 + q4 + q6 + q7 = r4 + r6
  m35 : q2 + q4 + q5 + q7 = r4 + r6
  m36 : q2 + q3 + q5 + q6 = r4 + r6
  m45 : q1 + q4 + q7 + q10 = r4 + r6 + r8
  m46 : q1 + q3 + q6 + q9 = r4 + r6 + r8
  m56 : q1 + q2 + q5 + q8 = r4 + r6 + r8

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

/-- The two endpoint probabilities of the isolated incidence are forced. -/
theorem MomentSystem.endpoints {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 : Real}
    (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8) :
    q0 = 1/3 ∧ r0 = 1/6 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, m12, m13, m14, m15, m16, m23, m24, m25, m26, m34, m35, m36, m45, m46, m56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8⟩ := h
  refine ⟨?_, ?_⟩ <;> linarith

/-! ## The Walsh expansions -/

def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),
      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

theorem ex_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef w0 = star (c y0) * d z0 + star (c y4) * d z4 + star (c y7) * d z6 + star (c y10) * d z8 := by
  unfold offSum
  rw [incidence]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_z0, flip_z4, flip_z6, flip_z8]
  simp only [sg_w0_0, sg_w0_4, sg_w0_6, sg_w0_8, SixQubit.signMul_false]
  try ring

theorem ex_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef w1 = star (c y0) * d z0 - star (c y4) * d z4 - star (c y7) * d z6 - star (c y10) * d z8 := by
  unfold offSum
  rw [incidence]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_z0, flip_z4, flip_z6, flip_z8]
  simp only [sg_w1_0, sg_w1_4, sg_w1_6, sg_w1_8, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

/-! ## The no-go -/

/-- **Orbit 48 is impossible.** -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)))
    (h0 : offSum c d ef w0 = 0)
    (h1 : offSum c d ef w1 = 0)
    : False := by
  rw [ex_w0] at h0
  rw [ex_w1] at h1
  have key : star (c y0) * d z0 = 0 := by
    linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1
  obtain ⟨hp, hq⟩ := hm.endpoints
  rcases mul_eq_zero.mp key with hh | hh
  · rw [show c y0 = 0 from by simpa using congrArg star hh] at hp
    simp at hp
  · rw [hh] at hq
    simp at hq

end

end SixQubit.Orbit48
