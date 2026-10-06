import Mathlib

import SS.FullKL
import SixQubit.Common

/-!
# Six-qubit no-go for moment orbit 62

Orbit 62 of `six_qubit_sslp_v7.tex`: q = 8, angle vector
a = (1, 1, 1, 5, 5, 5), residues 0 and 2, closed in Section 15.

The obstruction here is an *odd cancellation cycle* rather than a Walsh
system on a single flip.  Three Paulis of weight at most two each leave only
two surviving terms, giving `A_r + B_r = 0`.  Oriented as below, the product
`A_0 A_1 A_2` and the product `B_0 B_1 B_2` are the same monomial but carry
opposite signs, so that monomial is twice zero.  Each of its six factors has
strictly positive probability, which is the contradiction.

Everything computational is decided by the Lean kernel; `native_decide` is
not used.
-/

namespace SixQubit.Orbit62

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]

def y0 : SS.BitString 6 := bs false false false false false false  -- 000000
def y1 : SS.BitString 6 := bs false false true  true  true  true   -- 001111
def y2 : SS.BitString 6 := bs false true  false true  true  true   -- 010111
def y3 : SS.BitString 6 := bs true  false false true  true  true   -- 100111
def y4 : SS.BitString 6 := bs true  true  true  false false true   -- 111001
def y5 : SS.BitString 6 := bs true  true  true  false true  false  -- 111010
def y6 : SS.BitString 6 := bs true  true  true  true  false false  -- 111100

def z0 : SS.BitString 6 := bs false false false false true  true   -- 000011
def z1 : SS.BitString 6 := bs false false false true  false true   -- 000101
def z2 : SS.BitString 6 := bs false false false true  true  false  -- 000110
def z3 : SS.BitString 6 := bs false true  true  false false false  -- 011000
def z4 : SS.BitString 6 := bs true  false true  false false false  -- 101000
def z5 : SS.BitString 6 := bs true  true  false false false false  -- 110000
def z6 : SS.BitString 6 := bs true  true  true  true  true  true   -- 111111

def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6}
def S1 : Finset (SS.BitString 6) := {z0, z1, z2, z3, z4, z5, z6}

def av : Fin 6 -> ZMod 8 := ![1, 1, 1, 5, 5, 5]

/-- Each support is exactly its residue fiber, decided over all 64 strings. -/
theorem S0_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 0) = S0 := by
  decide

theorem S1_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 2) = S1 := by
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
    S1.filter (fun y => SS.bxor y ef0 ∈ S0) = {z5, z6} := by decide
theorem ne0 : (z5 : SS.BitString 6) ≠ z6 := by decide
theorem flipA0 : SS.bxor z5 ef0 = y0 := by decide
theorem flipB0 : SS.bxor z6 ef0 = y1 := by decide
theorem sgA0 : SS.bdot w0 z5 = false := by decide
theorem sgB0 : SS.bdot w0 z6 = false := by decide
theorem incidence1 :
    S1.filter (fun y => SS.bxor y ef1 ∈ S0) = {z0, z5} := by decide
theorem ne1 : (z0 : SS.BitString 6) ≠ z5 := by decide
theorem flipA1 : SS.bxor z0 ef1 = y1 := by decide
theorem flipB1 : SS.bxor z5 ef1 = y6 := by decide
theorem sgA1 : SS.bdot w1 z0 = false := by decide
theorem sgB1 : SS.bdot w1 z5 = false := by decide
theorem incidence2 :
    S1.filter (fun y => SS.bxor y ef2 ∈ S0) = {z6, z0} := by decide
theorem ne2 : (z6 : SS.BitString 6) ≠ z0 := by decide
theorem flipA2 : SS.bxor z6 ef2 = y6 := by decide
theorem flipB2 : SS.bxor z0 ef2 = y0 := by decide
theorem sgA2 : SS.bdot w2 z6 = false := by decide
theorem sgB2 : SS.bdot w2 z0 = false := by decide

/-! ## The moment system -/

/-- The two normalizations, the twenty-one moment equalities, and the
nonnegativity of every probability. -/
structure MomentSystem (q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6 : Real) : Prop where
  n0 : q0 + q1 + q2 + q3 + q4 + q5 + q6 = 1
  n1 : r0 + r1 + r2 + r3 + r4 + r5 + r6 = 1
  m1 : q3 + q4 + q5 + q6 = r4 + r5 + r6
  m2 : q2 + q4 + q5 + q6 = r3 + r5 + r6
  m3 : q1 + q4 + q5 + q6 = r3 + r4 + r6
  m4 : q1 + q2 + q3 + q6 = r1 + r2 + r6
  m5 : q1 + q2 + q3 + q5 = r0 + r2 + r6
  m6 : q1 + q2 + q3 + q4 = r0 + r1 + r6
  c12 : q4 + q5 + q6 = r5 + r6
  c13 : q4 + q5 + q6 = r4 + r6
  c14 : q3 + q6 = r6
  c15 : q3 + q5 = r6
  c16 : q3 + q4 = r6
  c23 : q4 + q5 + q6 = r3 + r6
  c24 : q2 + q6 = r6
  c25 : q2 + q5 = r6
  c26 : q2 + q4 = r6
  c34 : q1 + q6 = r6
  c35 : q1 + q5 = r6
  c36 : q1 + q4 = r6
  c45 : q1 + q2 + q3 = r2 + r6
  c46 : q1 + q2 + q3 = r1 + r6
  c56 : q1 + q2 + q3 = r0 + r6

  nq0 : 0 ≤ q0
  nq1 : 0 ≤ q1
  nq2 : 0 ≤ q2
  nq3 : 0 ≤ q3
  nq4 : 0 ≤ q4
  nq5 : 0 ≤ q5
  nq6 : 0 ≤ q6
  nr0 : 0 ≤ r0
  nr1 : 0 ≤ r1
  nr2 : 0 ≤ r2
  nr3 : 0 ≤ r3
  nr4 : 0 ≤ r4
  nr5 : 0 ≤ r5
  nr6 : 0 ≤ r6

/-- The 6 probabilities entering the cycle are forced. -/
theorem MomentSystem.pos {q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6 : Real}
    (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6) :
    0 < q0 ∧ 0 < q1 ∧ 0 < q6 ∧ 0 < r0 ∧ 0 < r5 ∧ 0 < r6 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nr0, nr1, nr2, nr3, nr4, nr5, nr6⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-! ## The cycle -/

def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),
      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

theorem expand0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w0 = star (c y0) * d z5 + star (c y1) * d z6 := by
  unfold offSum
  rw [incidence0, Finset.sum_pair ne0, flipA0, flipB0, sgA0, sgB0]
  simp only [SixQubit.signMul_false]
  try ring

theorem expand1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w1 = star (c y1) * d z0 + star (c y6) * d z5 := by
  unfold offSum
  rw [incidence1, Finset.sum_pair ne1, flipA1, flipB1, sgA1, sgB1]
  simp only [SixQubit.signMul_false]
  try ring

theorem expand2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w2 = star (c y6) * d z6 + star (c y0) * d z0 := by
  unfold offSum
  rw [incidence2, Finset.sum_pair ne2, flipA2, flipB2, sgA2, sgB2]
  simp only [SixQubit.signMul_false]
  try ring

/-- **Orbit 62 is impossible.** -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)))
    (h0 : offSum c d ef0 w0 = 0)
    (h1 : offSum c d ef1 w1 = 0)
    (h2 : offSum c d ef2 w2 = 0)
    : False := by
  obtain ⟨p0, p1, p6, t0, t5, t6⟩ := hm.pos
  rw [expand0] at h0
  rw [expand1] at h1
  rw [expand2] at h2
  have nu0 : c y0 ≠ 0 := fun hz => by rw [hz] at p0; simp at p0
  have nu1 : c y1 ≠ 0 := fun hz => by rw [hz] at p1; simp at p1
  have nu6 : c y6 ≠ 0 := fun hz => by rw [hz] at p6; simp at p6
  have nv0 : d z0 ≠ 0 := fun hz => by rw [hz] at t0; simp at t0
  have nv5 : d z5 ≠ 0 := fun hz => by rw [hz] at t5; simp at t5
  have nv6 : d z6 ≠ 0 := fun hz => by rw [hz] at t6; simp at t6
  have key : (2 : ℂ) * ((star (c y0) * d z5) * (star (c y1) * d z0) * (star (c y6) * d z6)) = 0 := by
    linear_combination ((star (c y1) * d z0) * (star (c y6) * d z6)) * h0 - ((star (c y1) * d z6) * (star (c y6) * d z6)) * h1 + ((star (c y1) * d z6) * (star (c y6) * d z5)) * h2
  have hz : ((star (c y0) * d z5) * (star (c y1) * d z0) * (star (c y6) * d z6)) = 0 := by linear_combination key / 2
  simp [nu0, nu1, nu6, nv0, nv5, nv6] at hz

end

end SixQubit.Orbit62
