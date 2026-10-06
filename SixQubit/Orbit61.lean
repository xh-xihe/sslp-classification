import Mathlib

import SS.FullKL
import SixQubit.Common

/-!
# Six-qubit no-go for moment orbit 61

Orbit 61 of `six_qubit_sslp_v7.tex`: q = 7, angle vector
a = (1, 2, 2, 3, 3, 4), residues 0 and 1, closed in Section 13.

The obstruction here is an *odd cancellation cycle* rather than a Walsh
system on a single flip.  Three Paulis of weight at most two each leave only
two surviving terms, giving `A_r + B_r = 0`.  Oriented as below, the product
`A_0 A_1 A_2` and the product `B_0 B_1 B_2` are the same monomial but carry
opposite signs, so that monomial is twice zero.  Each of its six factors has
strictly positive probability, which is the contradiction.

Everything computational is decided by the Lean kernel; `native_decide` is
not used.
-/

namespace SixQubit.Orbit61

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]

def y0 : SS.BitString 6 := bs false false false false false false  -- 000000
def y1 : SS.BitString 6 := bs false false false false true  true   -- 000011
def y2 : SS.BitString 6 := bs false false false true  false true   -- 000101
def y3 : SS.BitString 6 := bs false true  true  false true  false  -- 011010
def y4 : SS.BitString 6 := bs false true  true  true  false false  -- 011100
def y5 : SS.BitString 6 := bs false true  true  true  true  true   -- 011111
def y6 : SS.BitString 6 := bs true  false false true  true  false  -- 100110
def y7 : SS.BitString 6 := bs true  false true  false false true   -- 101001
def y8 : SS.BitString 6 := bs true  true  false false false true   -- 110001

def z0 : SS.BitString 6 := bs false false true  true  true  false  -- 001110
def z1 : SS.BitString 6 := bs false true  false true  true  false  -- 010110
def z2 : SS.BitString 6 := bs false true  true  false false true   -- 011001
def z3 : SS.BitString 6 := bs true  false false false false false  -- 100000
def z4 : SS.BitString 6 := bs true  false false false true  true   -- 100011
def z5 : SS.BitString 6 := bs true  false false true  false true   -- 100101
def z6 : SS.BitString 6 := bs true  true  true  false true  false  -- 111010
def z7 : SS.BitString 6 := bs true  true  true  true  false false  -- 111100
def z8 : SS.BitString 6 := bs true  true  true  true  true  true   -- 111111

def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6, y7, y8}
def S1 : Finset (SS.BitString 6) := {z0, z1, z2, z3, z4, z5, z6, z7, z8}

def av : Fin 6 -> ZMod 7 := ![1, 2, 2, 3, 3, 4]

/-- Each support is exactly its residue fiber, decided over all 64 strings. -/
theorem S0_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 0) = S0 := by
  decide

theorem S1_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 1) = S1 := by
  decide

/-! ## The three Paulis -/

/-- Relation 0: flip 110000, dressing 000000. -/
def ef0 : SS.BitString 6 := bs true  true  false false false false
def w0 : SS.BitString 6 := bs false false false false false false
/-- Relation 1: flip 001100, dressing 000000. -/
def ef1 : SS.BitString 6 := bs false false true  true  false false
def w1 : SS.BitString 6 := bs false false false false false false
/-- Relation 2: flip 000011, dressing 000000. -/
def ef2 : SS.BitString 6 := bs false false false false true  true 
def w2 : SS.BitString 6 := bs false false false false false false

theorem incidence0 :
    S1.filter (fun y => SS.bxor y ef0 ∈ S0) = {z1, z2} := by decide
theorem ne0 : (z1 : SS.BitString 6) ≠ z2 := by decide
theorem flipA0 : SS.bxor z1 ef0 = y6 := by decide
theorem flipB0 : SS.bxor z2 ef0 = y7 := by decide
theorem sgA0 : SS.bdot w0 z1 = false := by decide
theorem sgB0 : SS.bdot w0 z2 = false := by decide
theorem incidence1 :
    S1.filter (fun y => SS.bxor y ef1 ∈ S0) = {z5, z1} := by decide
theorem ne1 : (z5 : SS.BitString 6) ≠ z1 := by decide
theorem flipA1 : SS.bxor z5 ef1 = y7 := by decide
theorem flipB1 : SS.bxor z1 ef1 = y3 := by decide
theorem sgA1 : SS.bdot w1 z5 = false := by decide
theorem sgB1 : SS.bdot w1 z1 = false := by decide
theorem incidence2 :
    S1.filter (fun y => SS.bxor y ef2 ∈ S0) = {z2, z5} := by decide
theorem ne2 : (z2 : SS.BitString 6) ≠ z5 := by decide
theorem flipA2 : SS.bxor z2 ef2 = y3 := by decide
theorem flipB2 : SS.bxor z5 ef2 = y6 := by decide
theorem sgA2 : SS.bdot w2 z2 = false := by decide
theorem sgB2 : SS.bdot w2 z5 = false := by decide

/-! ## The moment system -/

/-- The two normalizations, the twenty-one moment equalities, and the
nonnegativity of every probability. -/
structure MomentSystem (q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8 : Real) : Prop where
  n0 : q0 + q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 = 1
  n1 : r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 = 1
  m1 : q6 + q7 + q8 = r3 + r4 + r5 + r6 + r7 + r8
  m2 : q3 + q4 + q5 + q8 = r1 + r2 + r6 + r7 + r8
  m3 : q3 + q4 + q5 + q7 = r0 + r2 + r6 + r7 + r8
  m4 : q2 + q4 + q5 + q6 = r0 + r1 + r5 + r7 + r8
  m5 : q1 + q3 + q5 + q6 = r0 + r1 + r4 + r6 + r8
  m6 : q1 + q2 + q5 + q7 + q8 = r2 + r4 + r5 + r8
  c12 : q8 = r6 + r7 + r8
  c13 : q7 = r6 + r7 + r8
  c14 : q6 = r5 + r7 + r8
  c15 : q6 = r4 + r6 + r8
  c16 : q7 + q8 = r4 + r5 + r8
  c23 : q3 + q4 + q5 = r2 + r6 + r7 + r8
  c24 : q4 + q5 = r1 + r7 + r8
  c25 : q3 + q5 = r1 + r6 + r8
  c26 : q5 + q8 = r2 + r8
  c34 : q4 + q5 = r0 + r7 + r8
  c35 : q3 + q5 = r0 + r6 + r8
  c36 : q5 + q7 = r2 + r8
  c45 : q5 + q6 = r0 + r1 + r8
  c46 : q2 + q5 = r5 + r8
  c56 : q1 + q5 = r4 + r8

  nq0 : 0 ≤ q0
  nq1 : 0 ≤ q1
  nq2 : 0 ≤ q2
  nq3 : 0 ≤ q3
  nq4 : 0 ≤ q4
  nq5 : 0 ≤ q5
  nq6 : 0 ≤ q6
  nq7 : 0 ≤ q7
  nq8 : 0 ≤ q8
  nr0 : 0 ≤ r0
  nr1 : 0 ≤ r1
  nr2 : 0 ≤ r2
  nr3 : 0 ≤ r3
  nr4 : 0 ≤ r4
  nr5 : 0 ≤ r5
  nr6 : 0 ≤ r6
  nr7 : 0 ≤ r7
  nr8 : 0 ≤ r8

/-- The 6 probabilities entering the cycle are forced. -/
theorem MomentSystem.pos {q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8 : Real}
    (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8) :
    0 < q3 ∧ 0 < q6 ∧ 0 < q7 ∧ 0 < r1 ∧ 0 < r2 ∧ 0 < r5 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-! ## The cycle -/

def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),
      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

theorem expand0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w0 = star (c y6) * d z1 + star (c y7) * d z2 := by
  unfold offSum
  rw [incidence0, Finset.sum_pair ne0, flipA0, flipB0, sgA0, sgB0]
  simp only [SixQubit.signMul_false]
  try ring

theorem expand1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w1 = star (c y7) * d z5 + star (c y3) * d z1 := by
  unfold offSum
  rw [incidence1, Finset.sum_pair ne1, flipA1, flipB1, sgA1, sgB1]
  simp only [SixQubit.signMul_false]
  try ring

theorem expand2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w2 = star (c y3) * d z2 + star (c y6) * d z5 := by
  unfold offSum
  rw [incidence2, Finset.sum_pair ne2, flipA2, flipB2, sgA2, sgB2]
  simp only [SixQubit.signMul_false]
  try ring

/-- **Orbit 61 is impossible.** -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)))
    (h0 : offSum c d ef0 w0 = 0)
    (h1 : offSum c d ef1 w1 = 0)
    (h2 : offSum c d ef2 w2 = 0)
    : False := by
  obtain ⟨p3, p6, p7, t1, t2, t5⟩ := hm.pos
  rw [expand0] at h0
  rw [expand1] at h1
  rw [expand2] at h2
  have nu3 : c y3 ≠ 0 := fun hz => by rw [hz] at p3; simp at p3
  have nu6 : c y6 ≠ 0 := fun hz => by rw [hz] at p6; simp at p6
  have nu7 : c y7 ≠ 0 := fun hz => by rw [hz] at p7; simp at p7
  have nv1 : d z1 ≠ 0 := fun hz => by rw [hz] at t1; simp at t1
  have nv2 : d z2 ≠ 0 := fun hz => by rw [hz] at t2; simp at t2
  have nv5 : d z5 ≠ 0 := fun hz => by rw [hz] at t5; simp at t5
  have key : (2 : ℂ) * ((star (c y6) * d z1) * (star (c y7) * d z5) * (star (c y3) * d z2)) = 0 := by
    linear_combination ((star (c y7) * d z5) * (star (c y3) * d z2)) * h0 - ((star (c y7) * d z2) * (star (c y3) * d z2)) * h1 + ((star (c y7) * d z2) * (star (c y3) * d z1)) * h2
  have hz : ((star (c y6) * d z1) * (star (c y7) * d z5) * (star (c y3) * d z2)) = 0 := by linear_combination key / 2
  simp [nu3, nu6, nu7, nv1, nv2, nv5] at hz

end

end SixQubit.Orbit61
