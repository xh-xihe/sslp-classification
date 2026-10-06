import Mathlib

import SS.FullKL
import SixQubit.Common

/-!
# Six-qubit no-go for moment orbit 32

Orbit 32 of `six_qubit_sslp_v7.tex`: q = 4, angle vector
a = (1, 1, 2, 2, 2, 3), residues 0 and 1, closed in Section 15.

The polytope forces no probability to be positive here.  It forces a positive
*sum*: writing a string as `(o1,o2,u1,u2,u3,o3)` and letting `u` run over the
even-parity middle strings, the top probabilities satisfy `sum_u E_u = 1/4`,
so at least one `E_u` is positive.  Which one is never determined, and the
argument does not need to know: the four cases apply one and the same lemma.

For such a `u`, three weight-one flips dressed by the four Z-masks on the
middle block give an invertible 4x4 Walsh system each, decoupling into one
equation per `u`.  Their squared moduli, factored through the exact moment
reflection, force `E_u = F_u = G_u = A_u = C_u > 0`, and a triangle identity
then makes a product of three nonzero amplitudes vanish.

Everything computational is decided by the Lean kernel; `native_decide` is
not used.
-/

namespace SixQubit.Orbit32

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

/-! ## The local lemma -/

/-- The whole argument at one middle string `u`.  `Au`..`Gu` are the six
probabilities there, tied to the amplitudes by `hA`..`hG`; `rA`..`rC` are the
exact moment reflection; `h1`..`h3` are the three decoupled Walsh equations. -/
theorem local_nogo (au bu cu eu fu gu : ℂ) (Au Bu Cu Eu Fu Gu : ℝ)
    (hA : Au = Complex.normSq au) (hB : Bu = Complex.normSq bu)
    (hC : Cu = Complex.normSq cu) (hE : Eu = Complex.normSq eu)
    (hF : Fu = Complex.normSq fu) (hG : Gu = Complex.normSq gu)
    (rA : Au = (2 * Eu + 2 * Fu - Gu) / 3)
    (rC : Cu = (-Eu + 2 * Fu + 2 * Gu) / 3)
    (rB : Bu = (2 * Eu - Fu + 2 * Gu) / 3)
    (hpos : 0 < Eu)
    (h1 : star au * fu + star bu * gu = 0)
    (h2 : star au * eu + star cu * gu = 0)
    (h3 : star bu * eu + star cu * fu = 0) : False := by
  have nF : 0 ≤ Fu := by rw [hF]; exact Complex.normSq_nonneg fu
  have nG : 0 ≤ Gu := by rw [hG]; exact Complex.normSq_nonneg gu
  have hS : 0 < Eu + Fu + Gu := by linarith
  -- squared moduli of the two Walsh equations
  have m1 : Au * Fu = Bu * Gu := by
    have he : star au * fu = -(star bu * gu) := by linear_combination h1
    have hm := congrArg Complex.normSq he
    simp [Complex.normSq_mul] at hm
    rw [hA, hB, hF, hG]; linarith [hm]
  have m2 : Au * Eu = Cu * Gu := by
    have he : star au * eu = -(star cu * gu) := by linear_combination h2
    have hm := congrArg Complex.normSq he
    simp [Complex.normSq_mul] at hm
    rw [hA, hC, hE, hG]; linarith [hm]
  -- factor each through the moment reflection
  have f1 : (Fu - Gu) * (Eu + Fu + Gu) = 0 := by
    rw [rA, rB] at m1; linear_combination (3 / 2) * m1
  have f2 : (Eu - Gu) * (Eu + Fu + Gu) = 0 := by
    rw [rA, rC] at m2; linear_combination (3 / 2) * m2
  have hFG : Fu = Gu := by
    rcases mul_eq_zero.mp f1 with h | h
    · linarith
    · linarith
  have hEG : Eu = Gu := by
    rcases mul_eq_zero.mp f2 with h | h
    · linarith
    · linarith
  -- every probability the contradiction uses is now positive
  have pA : 0 < Au := by rw [rA]; linarith
  have pC : 0 < Cu := by rw [rC]; linarith
  have pF : 0 < Fu := by linarith
  have na : au ≠ 0 := by
    intro hz; rw [hz] at hA; simp at hA; rw [hA] at pA; exact lt_irrefl 0 pA
  have nc : cu ≠ 0 := by
    intro hz; rw [hz] at hC; simp at hC; rw [hC] at pC; exact lt_irrefl 0 pC
  have nf : fu ≠ 0 := by
    intro hz; rw [hz] at hF; simp at hF; rw [hF] at pF; exact lt_irrefl 0 pF
  -- the triangle identity
  have key : (2 : ℂ) * (star au * star cu * fu) = 0 := by
    linear_combination (star cu) * h1 - (star bu) * h2 + (star au) * h3
  have hz : star au * star cu * fu = 0 := by linear_combination key / 2
  simp [na, nc, nf] at hz

/-! ## The orbit -/

def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]

def y0 : SS.BitString 6 := bs false false false false false false  -- 000000
def y1 : SS.BitString 6 := bs false false false true  true  false  -- 000110
def y2 : SS.BitString 6 := bs false false true  false true  false  -- 001010
def y3 : SS.BitString 6 := bs false false true  true  false false  -- 001100
def y4 : SS.BitString 6 := bs false true  false false false true   -- 010001
def y5 : SS.BitString 6 := bs false true  false true  true  true   -- 010111
def y6 : SS.BitString 6 := bs false true  true  false true  true   -- 011011
def y7 : SS.BitString 6 := bs false true  true  true  false true   -- 011101
def y8 : SS.BitString 6 := bs true  false false false false true   -- 100001
def y9 : SS.BitString 6 := bs true  false false true  true  true   -- 100111
def y10 : SS.BitString 6 := bs true  false true  false true  true   -- 101011
def y11 : SS.BitString 6 := bs true  false true  true  false true   -- 101101
def y12 : SS.BitString 6 := bs true  true  false false true  false  -- 110010
def y13 : SS.BitString 6 := bs true  true  false true  false false  -- 110100
def y14 : SS.BitString 6 := bs true  true  true  false false false  -- 111000
def y15 : SS.BitString 6 := bs true  true  true  true  true  false  -- 111110

def z0 : SS.BitString 6 := bs false false false false true  true   -- 000011
def z1 : SS.BitString 6 := bs false false false true  false true   -- 000101
def z2 : SS.BitString 6 := bs false false true  false false true   -- 001001
def z3 : SS.BitString 6 := bs false false true  true  true  true   -- 001111
def z4 : SS.BitString 6 := bs false true  false false false false  -- 010000
def z5 : SS.BitString 6 := bs false true  false true  true  false  -- 010110
def z6 : SS.BitString 6 := bs false true  true  false true  false  -- 011010
def z7 : SS.BitString 6 := bs false true  true  true  false false  -- 011100
def z8 : SS.BitString 6 := bs true  false false false false false  -- 100000
def z9 : SS.BitString 6 := bs true  false false true  true  false  -- 100110
def z10 : SS.BitString 6 := bs true  false true  false true  false  -- 101010
def z11 : SS.BitString 6 := bs true  false true  true  false false  -- 101100
def z12 : SS.BitString 6 := bs true  true  false false false true   -- 110001
def z13 : SS.BitString 6 := bs true  true  false true  true  true   -- 110111
def z14 : SS.BitString 6 := bs true  true  true  false true  true   -- 111011
def z15 : SS.BitString 6 := bs true  true  true  true  false true   -- 111101

def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15}
def S1 : Finset (SS.BitString 6) := {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15}

def av : Fin 6 -> ZMod 4 := ![1, 1, 2, 2, 2, 3]

/-- Each support is exactly its residue fiber, decided over all 64 strings. -/
theorem S0_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 0) = S0 := by
  decide

theorem S1_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 1) = S1 := by
  decide

/-- Flip 0: mask 100000. -/
def ef0 : SS.BitString 6 := bs true  false false false false false
/-- Flip 1: mask 010000. -/
def ef1 : SS.BitString 6 := bs false true  false false false false
/-- Flip 2: mask 000001. -/
def ef2 : SS.BitString 6 := bs false false false false false true 
def w0 : SS.BitString 6 := bs false false false false false false  -- dressing 000000
def w1 : SS.BitString 6 := bs false false true  false false false  -- dressing 001000
def w2 : SS.BitString 6 := bs false false false true  false false  -- dressing 000100
def w3 : SS.BitString 6 := bs false false false false true  false  -- dressing 000010

theorem incidence0 :
    S1.filter (fun y => SS.bxor y ef0 ∈ S0) = {z8, z9, z10, z11, z12, z13, z14, z15} := by decide
theorem fl0_8 : SS.bxor z8 ef0 = y0 := by decide
theorem fl0_9 : SS.bxor z9 ef0 = y1 := by decide
theorem fl0_10 : SS.bxor z10 ef0 = y2 := by decide
theorem fl0_11 : SS.bxor z11 ef0 = y3 := by decide
theorem fl0_12 : SS.bxor z12 ef0 = y4 := by decide
theorem fl0_13 : SS.bxor z13 ef0 = y5 := by decide
theorem fl0_14 : SS.bxor z14 ef0 = y6 := by decide
theorem fl0_15 : SS.bxor z15 ef0 = y7 := by decide
theorem sg0_0_8 : SS.bdot w0 z8 = false := by decide
theorem sg0_0_9 : SS.bdot w0 z9 = false := by decide
theorem sg0_0_10 : SS.bdot w0 z10 = false := by decide
theorem sg0_0_11 : SS.bdot w0 z11 = false := by decide
theorem sg0_0_12 : SS.bdot w0 z12 = false := by decide
theorem sg0_0_13 : SS.bdot w0 z13 = false := by decide
theorem sg0_0_14 : SS.bdot w0 z14 = false := by decide
theorem sg0_0_15 : SS.bdot w0 z15 = false := by decide
theorem sg0_1_8 : SS.bdot w1 z8 = false := by decide
theorem sg0_1_9 : SS.bdot w1 z9 = false := by decide
theorem sg0_1_10 : SS.bdot w1 z10 = true := by decide
theorem sg0_1_11 : SS.bdot w1 z11 = true := by decide
theorem sg0_1_12 : SS.bdot w1 z12 = false := by decide
theorem sg0_1_13 : SS.bdot w1 z13 = false := by decide
theorem sg0_1_14 : SS.bdot w1 z14 = true := by decide
theorem sg0_1_15 : SS.bdot w1 z15 = true := by decide
theorem sg0_2_8 : SS.bdot w2 z8 = false := by decide
theorem sg0_2_9 : SS.bdot w2 z9 = true := by decide
theorem sg0_2_10 : SS.bdot w2 z10 = false := by decide
theorem sg0_2_11 : SS.bdot w2 z11 = true := by decide
theorem sg0_2_12 : SS.bdot w2 z12 = false := by decide
theorem sg0_2_13 : SS.bdot w2 z13 = true := by decide
theorem sg0_2_14 : SS.bdot w2 z14 = false := by decide
theorem sg0_2_15 : SS.bdot w2 z15 = true := by decide
theorem sg0_3_8 : SS.bdot w3 z8 = false := by decide
theorem sg0_3_9 : SS.bdot w3 z9 = true := by decide
theorem sg0_3_10 : SS.bdot w3 z10 = true := by decide
theorem sg0_3_11 : SS.bdot w3 z11 = false := by decide
theorem sg0_3_12 : SS.bdot w3 z12 = false := by decide
theorem sg0_3_13 : SS.bdot w3 z13 = true := by decide
theorem sg0_3_14 : SS.bdot w3 z14 = true := by decide
theorem sg0_3_15 : SS.bdot w3 z15 = false := by decide

theorem incidence1 :
    S1.filter (fun y => SS.bxor y ef1 ∈ S0) = {z4, z5, z6, z7, z12, z13, z14, z15} := by decide
theorem fl1_4 : SS.bxor z4 ef1 = y0 := by decide
theorem fl1_5 : SS.bxor z5 ef1 = y1 := by decide
theorem fl1_6 : SS.bxor z6 ef1 = y2 := by decide
theorem fl1_7 : SS.bxor z7 ef1 = y3 := by decide
theorem fl1_12 : SS.bxor z12 ef1 = y8 := by decide
theorem fl1_13 : SS.bxor z13 ef1 = y9 := by decide
theorem fl1_14 : SS.bxor z14 ef1 = y10 := by decide
theorem fl1_15 : SS.bxor z15 ef1 = y11 := by decide
theorem sg1_0_4 : SS.bdot w0 z4 = false := by decide
theorem sg1_0_5 : SS.bdot w0 z5 = false := by decide
theorem sg1_0_6 : SS.bdot w0 z6 = false := by decide
theorem sg1_0_7 : SS.bdot w0 z7 = false := by decide
theorem sg1_0_12 : SS.bdot w0 z12 = false := by decide
theorem sg1_0_13 : SS.bdot w0 z13 = false := by decide
theorem sg1_0_14 : SS.bdot w0 z14 = false := by decide
theorem sg1_0_15 : SS.bdot w0 z15 = false := by decide
theorem sg1_1_4 : SS.bdot w1 z4 = false := by decide
theorem sg1_1_5 : SS.bdot w1 z5 = false := by decide
theorem sg1_1_6 : SS.bdot w1 z6 = true := by decide
theorem sg1_1_7 : SS.bdot w1 z7 = true := by decide
theorem sg1_1_12 : SS.bdot w1 z12 = false := by decide
theorem sg1_1_13 : SS.bdot w1 z13 = false := by decide
theorem sg1_1_14 : SS.bdot w1 z14 = true := by decide
theorem sg1_1_15 : SS.bdot w1 z15 = true := by decide
theorem sg1_2_4 : SS.bdot w2 z4 = false := by decide
theorem sg1_2_5 : SS.bdot w2 z5 = true := by decide
theorem sg1_2_6 : SS.bdot w2 z6 = false := by decide
theorem sg1_2_7 : SS.bdot w2 z7 = true := by decide
theorem sg1_2_12 : SS.bdot w2 z12 = false := by decide
theorem sg1_2_13 : SS.bdot w2 z13 = true := by decide
theorem sg1_2_14 : SS.bdot w2 z14 = false := by decide
theorem sg1_2_15 : SS.bdot w2 z15 = true := by decide
theorem sg1_3_4 : SS.bdot w3 z4 = false := by decide
theorem sg1_3_5 : SS.bdot w3 z5 = true := by decide
theorem sg1_3_6 : SS.bdot w3 z6 = true := by decide
theorem sg1_3_7 : SS.bdot w3 z7 = false := by decide
theorem sg1_3_12 : SS.bdot w3 z12 = false := by decide
theorem sg1_3_13 : SS.bdot w3 z13 = true := by decide
theorem sg1_3_14 : SS.bdot w3 z14 = true := by decide
theorem sg1_3_15 : SS.bdot w3 z15 = false := by decide

theorem incidence2 :
    S1.filter (fun y => SS.bxor y ef2 ∈ S0) = {z4, z5, z6, z7, z8, z9, z10, z11} := by decide
theorem fl2_4 : SS.bxor z4 ef2 = y4 := by decide
theorem fl2_5 : SS.bxor z5 ef2 = y5 := by decide
theorem fl2_6 : SS.bxor z6 ef2 = y6 := by decide
theorem fl2_7 : SS.bxor z7 ef2 = y7 := by decide
theorem fl2_8 : SS.bxor z8 ef2 = y8 := by decide
theorem fl2_9 : SS.bxor z9 ef2 = y9 := by decide
theorem fl2_10 : SS.bxor z10 ef2 = y10 := by decide
theorem fl2_11 : SS.bxor z11 ef2 = y11 := by decide
theorem sg2_0_4 : SS.bdot w0 z4 = false := by decide
theorem sg2_0_5 : SS.bdot w0 z5 = false := by decide
theorem sg2_0_6 : SS.bdot w0 z6 = false := by decide
theorem sg2_0_7 : SS.bdot w0 z7 = false := by decide
theorem sg2_0_8 : SS.bdot w0 z8 = false := by decide
theorem sg2_0_9 : SS.bdot w0 z9 = false := by decide
theorem sg2_0_10 : SS.bdot w0 z10 = false := by decide
theorem sg2_0_11 : SS.bdot w0 z11 = false := by decide
theorem sg2_1_4 : SS.bdot w1 z4 = false := by decide
theorem sg2_1_5 : SS.bdot w1 z5 = false := by decide
theorem sg2_1_6 : SS.bdot w1 z6 = true := by decide
theorem sg2_1_7 : SS.bdot w1 z7 = true := by decide
theorem sg2_1_8 : SS.bdot w1 z8 = false := by decide
theorem sg2_1_9 : SS.bdot w1 z9 = false := by decide
theorem sg2_1_10 : SS.bdot w1 z10 = true := by decide
theorem sg2_1_11 : SS.bdot w1 z11 = true := by decide
theorem sg2_2_4 : SS.bdot w2 z4 = false := by decide
theorem sg2_2_5 : SS.bdot w2 z5 = true := by decide
theorem sg2_2_6 : SS.bdot w2 z6 = false := by decide
theorem sg2_2_7 : SS.bdot w2 z7 = true := by decide
theorem sg2_2_8 : SS.bdot w2 z8 = false := by decide
theorem sg2_2_9 : SS.bdot w2 z9 = true := by decide
theorem sg2_2_10 : SS.bdot w2 z10 = false := by decide
theorem sg2_2_11 : SS.bdot w2 z11 = true := by decide
theorem sg2_3_4 : SS.bdot w3 z4 = false := by decide
theorem sg2_3_5 : SS.bdot w3 z5 = true := by decide
theorem sg2_3_6 : SS.bdot w3 z6 = true := by decide
theorem sg2_3_7 : SS.bdot w3 z7 = false := by decide
theorem sg2_3_8 : SS.bdot w3 z8 = false := by decide
theorem sg2_3_9 : SS.bdot w3 z9 = true := by decide
theorem sg2_3_10 : SS.bdot w3 z10 = true := by decide
theorem sg2_3_11 : SS.bdot w3 z11 = false := by decide

/-! ## The moment system -/

/-- The two normalizations, the twenty-one moment equalities, and the
nonnegativity of every probability. -/
structure MomentSystem (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real) : Prop where
  n0 : q0 + q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 + q9 + q10 + q11 + q12 + q13 + q14 + q15 = 1
  n1 : r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15 = 1
  m1 : q8 + q9 + q10 + q11 + q12 + q13 + q14 + q15 = r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15
  m2 : q4 + q5 + q6 + q7 + q12 + q13 + q14 + q15 = r4 + r5 + r6 + r7 + r12 + r13 + r14 + r15
  m3 : q2 + q3 + q6 + q7 + q10 + q11 + q14 + q15 = r2 + r3 + r6 + r7 + r10 + r11 + r14 + r15
  m4 : q1 + q3 + q5 + q7 + q9 + q11 + q13 + q15 = r1 + r3 + r5 + r7 + r9 + r11 + r13 + r15
  m5 : q1 + q2 + q5 + q6 + q9 + q10 + q12 + q15 = r0 + r3 + r5 + r6 + r9 + r10 + r13 + r14
  m6 : q4 + q5 + q6 + q7 + q8 + q9 + q10 + q11 = r0 + r1 + r2 + r3 + r12 + r13 + r14 + r15
  c12 : q12 + q13 + q14 + q15 = r12 + r13 + r14 + r15
  c13 : q10 + q11 + q14 + q15 = r10 + r11 + r14 + r15
  c14 : q9 + q11 + q13 + q15 = r9 + r11 + r13 + r15
  c15 : q9 + q10 + q12 + q15 = r9 + r10 + r13 + r14
  c16 : q8 + q9 + q10 + q11 = r12 + r13 + r14 + r15
  c23 : q6 + q7 + q14 + q15 = r6 + r7 + r14 + r15
  c24 : q5 + q7 + q13 + q15 = r5 + r7 + r13 + r15
  c25 : q5 + q6 + q12 + q15 = r5 + r6 + r13 + r14
  c26 : q4 + q5 + q6 + q7 = r12 + r13 + r14 + r15
  c34 : q3 + q7 + q11 + q15 = r3 + r7 + r11 + r15
  c35 : q2 + q6 + q10 + q15 = r3 + r6 + r10 + r14
  c36 : q6 + q7 + q10 + q11 = r2 + r3 + r14 + r15
  c45 : q1 + q5 + q9 + q15 = r3 + r5 + r9 + r13
  c46 : q5 + q7 + q9 + q11 = r1 + r3 + r13 + r15
  c56 : q5 + q6 + q9 + q10 = r0 + r3 + r13 + r14

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

/-- The exact moment reflection `(A,B,C) = T (E,F,G)` at every middle string. -/
theorem MomentSystem.reflection {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    q0 = (2 * r4 + 2 * r8 - r12) / 3 ∧ q4 = (2 * r4 - r8 + 2 * r12) / 3 ∧ q8 = (-r4 + 2 * r8 + 2 * r12) / 3 ∧ q1 = (2 * r5 + 2 * r9 - r13) / 3 ∧ q5 = (2 * r5 - r9 + 2 * r13) / 3 ∧ q9 = (-r5 + 2 * r9 + 2 * r13) / 3 ∧ q2 = (2 * r6 + 2 * r10 - r14) / 3 ∧ q6 = (2 * r6 - r10 + 2 * r14) / 3 ∧ q10 = (-r6 + 2 * r10 + 2 * r14) / 3 ∧ q3 = (2 * r7 + 2 * r11 - r15) / 3 ∧ q7 = (2 * r7 - r11 + 2 * r15) / 3 ∧ q11 = (-r7 + 2 * r11 + 2 * r15) / 3 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- The row sum that supplies the only positivity in the whole argument. -/
theorem MomentSystem.rowsum {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    r4 + r5 + r6 + r7 = 1 / 4 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  linarith

theorem MomentSystem.some_pos {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    0 < r4 ∨ 0 < r5 ∨ 0 < r6 ∨ 0 < r7 := by
  have hs := h.rowsum
  by_contra hc
  push_neg at hc
  obtain ⟨c0, c1, c2, c3⟩ := hc
  linarith

/-! ## The Walsh systems -/

def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),
      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

theorem ex0_0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w0 = star (c y0) * d z8 + star (c y1) * d z9 + star (c y2) * d z10 + star (c y3) * d z11 + star (c y4) * d z12 + star (c y5) * d z13 + star (c y6) * d z14 + star (c y7) * d z15 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_8, fl0_9, fl0_10, fl0_11, fl0_12, fl0_13, fl0_14, fl0_15]
  simp only [sg0_0_8, sg0_0_9, sg0_0_10, sg0_0_11, sg0_0_12, sg0_0_13, sg0_0_14, sg0_0_15, SixQubit.signMul_false]
  try ring

theorem ex0_1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w1 = star (c y0) * d z8 + star (c y1) * d z9 - star (c y2) * d z10 - star (c y3) * d z11 + star (c y4) * d z12 + star (c y5) * d z13 - star (c y6) * d z14 - star (c y7) * d z15 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_8, fl0_9, fl0_10, fl0_11, fl0_12, fl0_13, fl0_14, fl0_15]
  simp only [sg0_1_8, sg0_1_9, sg0_1_10, sg0_1_11, sg0_1_12, sg0_1_13, sg0_1_14, sg0_1_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex0_2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w2 = star (c y0) * d z8 - star (c y1) * d z9 + star (c y2) * d z10 - star (c y3) * d z11 + star (c y4) * d z12 - star (c y5) * d z13 + star (c y6) * d z14 - star (c y7) * d z15 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_8, fl0_9, fl0_10, fl0_11, fl0_12, fl0_13, fl0_14, fl0_15]
  simp only [sg0_2_8, sg0_2_9, sg0_2_10, sg0_2_11, sg0_2_12, sg0_2_13, sg0_2_14, sg0_2_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex0_3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w3 = star (c y0) * d z8 - star (c y1) * d z9 - star (c y2) * d z10 + star (c y3) * d z11 + star (c y4) * d z12 - star (c y5) * d z13 - star (c y6) * d z14 + star (c y7) * d z15 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_8, fl0_9, fl0_10, fl0_11, fl0_12, fl0_13, fl0_14, fl0_15]
  simp only [sg0_3_8, sg0_3_9, sg0_3_10, sg0_3_11, sg0_3_12, sg0_3_13, sg0_3_14, sg0_3_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

/-- Walsh inversion of flip 0 at middle string 000. -/
theorem eqn0_000 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef0 w0 = 0)
    (h1 : offSum c d ef0 w1 = 0)
    (h2 : offSum c d ef0 w2 = 0)
    (h3 : offSum c d ef0 w3 = 0)
    : star (c y0) * d z8 + star (c y4) * d z12 = 0 := by
  rw [ex0_0] at h0
  rw [ex0_1] at h1
  rw [ex0_2] at h2
  rw [ex0_3] at h3
  linear_combination (1 / 4 : ℂ) * h0 + (1 / 4 : ℂ) * h1 + (1 / 4 : ℂ) * h2 + (1 / 4 : ℂ) * h3

/-- Walsh inversion of flip 0 at middle string 011. -/
theorem eqn0_011 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef0 w0 = 0)
    (h1 : offSum c d ef0 w1 = 0)
    (h2 : offSum c d ef0 w2 = 0)
    (h3 : offSum c d ef0 w3 = 0)
    : star (c y1) * d z9 + star (c y5) * d z13 = 0 := by
  rw [ex0_0] at h0
  rw [ex0_1] at h1
  rw [ex0_2] at h2
  rw [ex0_3] at h3
  linear_combination (1 / 4 : ℂ) * h0 + (1 / 4 : ℂ) * h1 - (1 / 4 : ℂ) * h2 - (1 / 4 : ℂ) * h3

/-- Walsh inversion of flip 0 at middle string 101. -/
theorem eqn0_101 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef0 w0 = 0)
    (h1 : offSum c d ef0 w1 = 0)
    (h2 : offSum c d ef0 w2 = 0)
    (h3 : offSum c d ef0 w3 = 0)
    : star (c y2) * d z10 + star (c y6) * d z14 = 0 := by
  rw [ex0_0] at h0
  rw [ex0_1] at h1
  rw [ex0_2] at h2
  rw [ex0_3] at h3
  linear_combination (1 / 4 : ℂ) * h0 - (1 / 4 : ℂ) * h1 + (1 / 4 : ℂ) * h2 - (1 / 4 : ℂ) * h3

/-- Walsh inversion of flip 0 at middle string 110. -/
theorem eqn0_110 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef0 w0 = 0)
    (h1 : offSum c d ef0 w1 = 0)
    (h2 : offSum c d ef0 w2 = 0)
    (h3 : offSum c d ef0 w3 = 0)
    : star (c y3) * d z11 + star (c y7) * d z15 = 0 := by
  rw [ex0_0] at h0
  rw [ex0_1] at h1
  rw [ex0_2] at h2
  rw [ex0_3] at h3
  linear_combination (1 / 4 : ℂ) * h0 - (1 / 4 : ℂ) * h1 - (1 / 4 : ℂ) * h2 + (1 / 4 : ℂ) * h3

theorem ex1_0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w0 = star (c y0) * d z4 + star (c y1) * d z5 + star (c y2) * d z6 + star (c y3) * d z7 + star (c y8) * d z12 + star (c y9) * d z13 + star (c y10) * d z14 + star (c y11) * d z15 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_4, fl1_5, fl1_6, fl1_7, fl1_12, fl1_13, fl1_14, fl1_15]
  simp only [sg1_0_4, sg1_0_5, sg1_0_6, sg1_0_7, sg1_0_12, sg1_0_13, sg1_0_14, sg1_0_15, SixQubit.signMul_false]
  try ring

theorem ex1_1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w1 = star (c y0) * d z4 + star (c y1) * d z5 - star (c y2) * d z6 - star (c y3) * d z7 + star (c y8) * d z12 + star (c y9) * d z13 - star (c y10) * d z14 - star (c y11) * d z15 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_4, fl1_5, fl1_6, fl1_7, fl1_12, fl1_13, fl1_14, fl1_15]
  simp only [sg1_1_4, sg1_1_5, sg1_1_6, sg1_1_7, sg1_1_12, sg1_1_13, sg1_1_14, sg1_1_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex1_2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w2 = star (c y0) * d z4 - star (c y1) * d z5 + star (c y2) * d z6 - star (c y3) * d z7 + star (c y8) * d z12 - star (c y9) * d z13 + star (c y10) * d z14 - star (c y11) * d z15 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_4, fl1_5, fl1_6, fl1_7, fl1_12, fl1_13, fl1_14, fl1_15]
  simp only [sg1_2_4, sg1_2_5, sg1_2_6, sg1_2_7, sg1_2_12, sg1_2_13, sg1_2_14, sg1_2_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex1_3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w3 = star (c y0) * d z4 - star (c y1) * d z5 - star (c y2) * d z6 + star (c y3) * d z7 + star (c y8) * d z12 - star (c y9) * d z13 - star (c y10) * d z14 + star (c y11) * d z15 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_4, fl1_5, fl1_6, fl1_7, fl1_12, fl1_13, fl1_14, fl1_15]
  simp only [sg1_3_4, sg1_3_5, sg1_3_6, sg1_3_7, sg1_3_12, sg1_3_13, sg1_3_14, sg1_3_15, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

/-- Walsh inversion of flip 1 at middle string 000. -/
theorem eqn1_000 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef1 w0 = 0)
    (h1 : offSum c d ef1 w1 = 0)
    (h2 : offSum c d ef1 w2 = 0)
    (h3 : offSum c d ef1 w3 = 0)
    : star (c y0) * d z4 + star (c y8) * d z12 = 0 := by
  rw [ex1_0] at h0
  rw [ex1_1] at h1
  rw [ex1_2] at h2
  rw [ex1_3] at h3
  linear_combination (1 / 4 : ℂ) * h0 + (1 / 4 : ℂ) * h1 + (1 / 4 : ℂ) * h2 + (1 / 4 : ℂ) * h3

/-- Walsh inversion of flip 1 at middle string 011. -/
theorem eqn1_011 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef1 w0 = 0)
    (h1 : offSum c d ef1 w1 = 0)
    (h2 : offSum c d ef1 w2 = 0)
    (h3 : offSum c d ef1 w3 = 0)
    : star (c y1) * d z5 + star (c y9) * d z13 = 0 := by
  rw [ex1_0] at h0
  rw [ex1_1] at h1
  rw [ex1_2] at h2
  rw [ex1_3] at h3
  linear_combination (1 / 4 : ℂ) * h0 + (1 / 4 : ℂ) * h1 - (1 / 4 : ℂ) * h2 - (1 / 4 : ℂ) * h3

/-- Walsh inversion of flip 1 at middle string 101. -/
theorem eqn1_101 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef1 w0 = 0)
    (h1 : offSum c d ef1 w1 = 0)
    (h2 : offSum c d ef1 w2 = 0)
    (h3 : offSum c d ef1 w3 = 0)
    : star (c y2) * d z6 + star (c y10) * d z14 = 0 := by
  rw [ex1_0] at h0
  rw [ex1_1] at h1
  rw [ex1_2] at h2
  rw [ex1_3] at h3
  linear_combination (1 / 4 : ℂ) * h0 - (1 / 4 : ℂ) * h1 + (1 / 4 : ℂ) * h2 - (1 / 4 : ℂ) * h3

/-- Walsh inversion of flip 1 at middle string 110. -/
theorem eqn1_110 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef1 w0 = 0)
    (h1 : offSum c d ef1 w1 = 0)
    (h2 : offSum c d ef1 w2 = 0)
    (h3 : offSum c d ef1 w3 = 0)
    : star (c y3) * d z7 + star (c y11) * d z15 = 0 := by
  rw [ex1_0] at h0
  rw [ex1_1] at h1
  rw [ex1_2] at h2
  rw [ex1_3] at h3
  linear_combination (1 / 4 : ℂ) * h0 - (1 / 4 : ℂ) * h1 - (1 / 4 : ℂ) * h2 + (1 / 4 : ℂ) * h3

theorem ex2_0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w0 = star (c y4) * d z4 + star (c y5) * d z5 + star (c y6) * d z6 + star (c y7) * d z7 + star (c y8) * d z8 + star (c y9) * d z9 + star (c y10) * d z10 + star (c y11) * d z11 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_4, fl2_5, fl2_6, fl2_7, fl2_8, fl2_9, fl2_10, fl2_11]
  simp only [sg2_0_4, sg2_0_5, sg2_0_6, sg2_0_7, sg2_0_8, sg2_0_9, sg2_0_10, sg2_0_11, SixQubit.signMul_false]
  try ring

theorem ex2_1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w1 = star (c y4) * d z4 + star (c y5) * d z5 - star (c y6) * d z6 - star (c y7) * d z7 + star (c y8) * d z8 + star (c y9) * d z9 - star (c y10) * d z10 - star (c y11) * d z11 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_4, fl2_5, fl2_6, fl2_7, fl2_8, fl2_9, fl2_10, fl2_11]
  simp only [sg2_1_4, sg2_1_5, sg2_1_6, sg2_1_7, sg2_1_8, sg2_1_9, sg2_1_10, sg2_1_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex2_2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w2 = star (c y4) * d z4 - star (c y5) * d z5 + star (c y6) * d z6 - star (c y7) * d z7 + star (c y8) * d z8 - star (c y9) * d z9 + star (c y10) * d z10 - star (c y11) * d z11 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_4, fl2_5, fl2_6, fl2_7, fl2_8, fl2_9, fl2_10, fl2_11]
  simp only [sg2_2_4, sg2_2_5, sg2_2_6, sg2_2_7, sg2_2_8, sg2_2_9, sg2_2_10, sg2_2_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex2_3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w3 = star (c y4) * d z4 - star (c y5) * d z5 - star (c y6) * d z6 + star (c y7) * d z7 + star (c y8) * d z8 - star (c y9) * d z9 - star (c y10) * d z10 + star (c y11) * d z11 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_4, fl2_5, fl2_6, fl2_7, fl2_8, fl2_9, fl2_10, fl2_11]
  simp only [sg2_3_4, sg2_3_5, sg2_3_6, sg2_3_7, sg2_3_8, sg2_3_9, sg2_3_10, sg2_3_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

/-- Walsh inversion of flip 2 at middle string 000. -/
theorem eqn2_000 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef2 w0 = 0)
    (h1 : offSum c d ef2 w1 = 0)
    (h2 : offSum c d ef2 w2 = 0)
    (h3 : offSum c d ef2 w3 = 0)
    : star (c y4) * d z4 + star (c y8) * d z8 = 0 := by
  rw [ex2_0] at h0
  rw [ex2_1] at h1
  rw [ex2_2] at h2
  rw [ex2_3] at h3
  linear_combination (1 / 4 : ℂ) * h0 + (1 / 4 : ℂ) * h1 + (1 / 4 : ℂ) * h2 + (1 / 4 : ℂ) * h3

/-- Walsh inversion of flip 2 at middle string 011. -/
theorem eqn2_011 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef2 w0 = 0)
    (h1 : offSum c d ef2 w1 = 0)
    (h2 : offSum c d ef2 w2 = 0)
    (h3 : offSum c d ef2 w3 = 0)
    : star (c y5) * d z5 + star (c y9) * d z9 = 0 := by
  rw [ex2_0] at h0
  rw [ex2_1] at h1
  rw [ex2_2] at h2
  rw [ex2_3] at h3
  linear_combination (1 / 4 : ℂ) * h0 + (1 / 4 : ℂ) * h1 - (1 / 4 : ℂ) * h2 - (1 / 4 : ℂ) * h3

/-- Walsh inversion of flip 2 at middle string 101. -/
theorem eqn2_101 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef2 w0 = 0)
    (h1 : offSum c d ef2 w1 = 0)
    (h2 : offSum c d ef2 w2 = 0)
    (h3 : offSum c d ef2 w3 = 0)
    : star (c y6) * d z6 + star (c y10) * d z10 = 0 := by
  rw [ex2_0] at h0
  rw [ex2_1] at h1
  rw [ex2_2] at h2
  rw [ex2_3] at h3
  linear_combination (1 / 4 : ℂ) * h0 - (1 / 4 : ℂ) * h1 + (1 / 4 : ℂ) * h2 - (1 / 4 : ℂ) * h3

/-- Walsh inversion of flip 2 at middle string 110. -/
theorem eqn2_110 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef2 w0 = 0)
    (h1 : offSum c d ef2 w1 = 0)
    (h2 : offSum c d ef2 w2 = 0)
    (h3 : offSum c d ef2 w3 = 0)
    : star (c y7) * d z7 + star (c y11) * d z11 = 0 := by
  rw [ex2_0] at h0
  rw [ex2_1] at h1
  rw [ex2_2] at h2
  rw [ex2_3] at h3
  linear_combination (1 / 4 : ℂ) * h0 - (1 / 4 : ℂ) * h1 - (1 / 4 : ℂ) * h2 + (1 / 4 : ℂ) * h3

/-! ## The no-go -/

/-- **Orbit 32 is impossible.** -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11)) (Complex.normSq (c y12)) (Complex.normSq (c y13)) (Complex.normSq (c y14)) (Complex.normSq (c y15))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)) (Complex.normSq (d z12)) (Complex.normSq (d z13)) (Complex.normSq (d z14)) (Complex.normSq (d z15)))
    (e0_0 : offSum c d ef0 w0 = 0)
    (e0_1 : offSum c d ef0 w1 = 0)
    (e0_2 : offSum c d ef0 w2 = 0)
    (e0_3 : offSum c d ef0 w3 = 0)
    (e1_0 : offSum c d ef1 w0 = 0)
    (e1_1 : offSum c d ef1 w1 = 0)
    (e1_2 : offSum c d ef1 w2 = 0)
    (e1_3 : offSum c d ef1 w3 = 0)
    (e2_0 : offSum c d ef2 w0 = 0)
    (e2_1 : offSum c d ef2 w1 = 0)
    (e2_2 : offSum c d ef2 w2 = 0)
    (e2_3 : offSum c d ef2 w3 = 0)
    : False := by
  obtain ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11⟩ := hm.reflection
  rcases hm.some_pos with hp | hp | hp | hp
  · exact local_nogo (c y0) (c y4) (c y8) (d z4) (d z8) (d z12)
      _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl R0 R2 R1 hp
      (eqn0_000 c d e0_0 e0_1 e0_2 e0_3)
      (eqn1_000 c d e1_0 e1_1 e1_2 e1_3)
      (eqn2_000 c d e2_0 e2_1 e2_2 e2_3)
  · exact local_nogo (c y1) (c y5) (c y9) (d z5) (d z9) (d z13)
      _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl R3 R5 R4 hp
      (eqn0_011 c d e0_0 e0_1 e0_2 e0_3)
      (eqn1_011 c d e1_0 e1_1 e1_2 e1_3)
      (eqn2_011 c d e2_0 e2_1 e2_2 e2_3)
  · exact local_nogo (c y2) (c y6) (c y10) (d z6) (d z10) (d z14)
      _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl R6 R8 R7 hp
      (eqn0_101 c d e0_0 e0_1 e0_2 e0_3)
      (eqn1_101 c d e1_0 e1_1 e1_2 e1_3)
      (eqn2_101 c d e2_0 e2_1 e2_2 e2_3)
  · exact local_nogo (c y3) (c y7) (c y11) (d z7) (d z11) (d z15)
      _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl R9 R11 R10 hp
      (eqn0_110 c d e0_0 e0_1 e0_2 e0_3)
      (eqn1_110 c d e1_0 e1_1 e1_2 e1_3)
      (eqn2_110 c d e2_0 e2_1 e2_2 e2_3)

end

end SixQubit.Orbit32
