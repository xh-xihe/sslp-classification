import Mathlib

import SS.FullKL
import SixQubit.Common

/-!
# Six-qubit no-go for moment orbit 38

Orbit 38 of `six_qubit_sslp_v7.tex`: q = 5, angle vector
a = (1, 1, 2, 2, 2, 3), residues 0 and 1, closed in Section 17.

The bottom fiber is a two-by-four grid `B_ij` together with four points `A_j`
and a single star `S`; the top fiber is its bitwise complement.  The moment
system forces `q_S = r_Shat = 1/5` and both row sums to `3/10` on each fiber,
but no individual grid probability is forced positive -- which is why the
earlier certificates all fail here.

Each grid point has exactly one weight-two flip whose incidence set is the
reciprocal pair `{B_ij <-> Shat, S <-> B_ij-hat}`; since `u_S` and `v_Shat`
are nonzero, that equation ties the two fibers together, and `c_{B_ij}`
vanishes exactly when `d_{B_ij-hat}` does.  Each pair of columns has exactly
one weight-two flip carrying a permanent; transitivity through the hub `S`,
division-free, collapses it to a two-term relation.  A vanishing grid
amplitude would then force a whole row to vanish against its row sum, so none
vanishes, and the collapsed relations close a length-three odd cycle.

Everything computational is decided by the Lean kernel; `native_decide` is
not used.
-/

namespace SixQubit.Orbit38

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]

def y0 : SS.BitString 6 := bs false false false false false false  -- 000000
def y1 : SS.BitString 6 := bs false false false false true  true   -- 000011
def y2 : SS.BitString 6 := bs false false false true  false true   -- 000101
def y3 : SS.BitString 6 := bs false false true  false false true   -- 001001
def y4 : SS.BitString 6 := bs false true  false true  true  false  -- 010110
def y5 : SS.BitString 6 := bs false true  true  false true  false  -- 011010
def y6 : SS.BitString 6 := bs false true  true  true  false false  -- 011100
def y7 : SS.BitString 6 := bs false true  true  true  true  true   -- 011111
def y8 : SS.BitString 6 := bs true  false false true  true  false  -- 100110
def y9 : SS.BitString 6 := bs true  false true  false true  false  -- 101010
def y10 : SS.BitString 6 := bs true  false true  true  false false  -- 101100
def y11 : SS.BitString 6 := bs true  false true  true  true  true   -- 101111
def y12 : SS.BitString 6 := bs true  true  false false false true   -- 110001

def z0 : SS.BitString 6 := bs false false true  true  true  false  -- 001110
def z1 : SS.BitString 6 := bs false true  false false false false  -- 010000
def z2 : SS.BitString 6 := bs false true  false false true  true   -- 010011
def z3 : SS.BitString 6 := bs false true  false true  false true   -- 010101
def z4 : SS.BitString 6 := bs false true  true  false false true   -- 011001
def z5 : SS.BitString 6 := bs true  false false false false false  -- 100000
def z6 : SS.BitString 6 := bs true  false false false true  true   -- 100011
def z7 : SS.BitString 6 := bs true  false false true  false true   -- 100101
def z8 : SS.BitString 6 := bs true  false true  false false true   -- 101001
def z9 : SS.BitString 6 := bs true  true  false true  true  false  -- 110110
def z10 : SS.BitString 6 := bs true  true  true  false true  false  -- 111010
def z11 : SS.BitString 6 := bs true  true  true  true  false false  -- 111100
def z12 : SS.BitString 6 := bs true  true  true  true  true  true   -- 111111

def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12}
def S1 : Finset (SS.BitString 6) := {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12}

def av : Fin 6 -> ZMod 5 := ![1, 1, 2, 2, 2, 3]

/-- Each support is exactly its residue fiber, decided over all 64 strings. -/
theorem S0_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 0) = S0 := by
  decide

theorem S1_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 1) = S1 := by
  decide

def ef0 : SS.BitString 6 := bs false false false false true  true   -- mask 000011
def ef1 : SS.BitString 6 := bs false false false true  false true   -- mask 000101
def ef2 : SS.BitString 6 := bs false false false true  true  false  -- mask 000110
def ef3 : SS.BitString 6 := bs false false true  false false true   -- mask 001001
def ef4 : SS.BitString 6 := bs false false true  false true  false  -- mask 001010
def ef5 : SS.BitString 6 := bs false false true  true  false false  -- mask 001100
def ef6 : SS.BitString 6 := bs false true  false false false true   -- mask 010001
def ef7 : SS.BitString 6 := bs false true  false false true  false  -- mask 010010
def ef8 : SS.BitString 6 := bs false true  false true  false false  -- mask 010100
def ef9 : SS.BitString 6 := bs false true  true  false false false  -- mask 011000
def ef10 : SS.BitString 6 := bs true  false false false false true   -- mask 100001
def ef11 : SS.BitString 6 := bs true  false false false true  false  -- mask 100010
def ef12 : SS.BitString 6 := bs true  false false true  false false  -- mask 100100
def ef13 : SS.BitString 6 := bs true  false true  false false false  -- mask 101000
def w0 : SS.BitString 6 := bs false false false false false false

theorem incidence0 :
    S1.filter (fun y => SS.bxor y ef0 ∈ S0) = {z3, z4, z7, z8} := by decide
theorem fl0_3 : SS.bxor z3 ef0 = y4 := by decide
theorem sg0_3 : SS.bdot w0 z3 = false := by decide
theorem fl0_4 : SS.bxor z4 ef0 = y5 := by decide
theorem sg0_4 : SS.bdot w0 z4 = false := by decide
theorem fl0_7 : SS.bxor z7 ef0 = y8 := by decide
theorem sg0_7 : SS.bdot w0 z7 = false := by decide
theorem fl0_8 : SS.bxor z8 ef0 = y9 := by decide
theorem sg0_8 : SS.bdot w0 z8 = false := by decide
theorem incidence1 :
    S1.filter (fun y => SS.bxor y ef1 ∈ S0) = {z2, z4, z6, z8} := by decide
theorem fl1_2 : SS.bxor z2 ef1 = y4 := by decide
theorem sg1_2 : SS.bdot w0 z2 = false := by decide
theorem fl1_4 : SS.bxor z4 ef1 = y6 := by decide
theorem sg1_4 : SS.bdot w0 z4 = false := by decide
theorem fl1_6 : SS.bxor z6 ef1 = y8 := by decide
theorem sg1_6 : SS.bdot w0 z6 = false := by decide
theorem fl1_8 : SS.bxor z8 ef1 = y10 := by decide
theorem sg1_8 : SS.bdot w0 z8 = false := by decide
theorem incidence2 :
    S1.filter (fun y => SS.bxor y ef2 ∈ S0) = {z1, z4, z5, z8} := by decide
theorem fl2_1 : SS.bxor z1 ef2 = y4 := by decide
theorem sg2_1 : SS.bdot w0 z1 = false := by decide
theorem fl2_4 : SS.bxor z4 ef2 = y7 := by decide
theorem sg2_4 : SS.bdot w0 z4 = false := by decide
theorem fl2_5 : SS.bxor z5 ef2 = y8 := by decide
theorem sg2_5 : SS.bdot w0 z5 = false := by decide
theorem fl2_8 : SS.bxor z8 ef2 = y11 := by decide
theorem sg2_8 : SS.bdot w0 z8 = false := by decide
theorem incidence3 :
    S1.filter (fun y => SS.bxor y ef3 ∈ S0) = {z2, z3, z6, z7} := by decide
theorem fl3_2 : SS.bxor z2 ef3 = y5 := by decide
theorem sg3_2 : SS.bdot w0 z2 = false := by decide
theorem fl3_3 : SS.bxor z3 ef3 = y6 := by decide
theorem sg3_3 : SS.bdot w0 z3 = false := by decide
theorem fl3_6 : SS.bxor z6 ef3 = y9 := by decide
theorem sg3_6 : SS.bdot w0 z6 = false := by decide
theorem fl3_7 : SS.bxor z7 ef3 = y10 := by decide
theorem sg3_7 : SS.bdot w0 z7 = false := by decide
theorem incidence4 :
    S1.filter (fun y => SS.bxor y ef4 ∈ S0) = {z1, z3, z5, z7} := by decide
theorem fl4_1 : SS.bxor z1 ef4 = y5 := by decide
theorem sg4_1 : SS.bdot w0 z1 = false := by decide
theorem fl4_3 : SS.bxor z3 ef4 = y7 := by decide
theorem sg4_3 : SS.bdot w0 z3 = false := by decide
theorem fl4_5 : SS.bxor z5 ef4 = y9 := by decide
theorem sg4_5 : SS.bdot w0 z5 = false := by decide
theorem fl4_7 : SS.bxor z7 ef4 = y11 := by decide
theorem sg4_7 : SS.bdot w0 z7 = false := by decide
theorem incidence5 :
    S1.filter (fun y => SS.bxor y ef5 ∈ S0) = {z1, z2, z5, z6} := by decide
theorem fl5_1 : SS.bxor z1 ef5 = y6 := by decide
theorem sg5_1 : SS.bdot w0 z1 = false := by decide
theorem fl5_2 : SS.bxor z2 ef5 = y7 := by decide
theorem sg5_2 : SS.bdot w0 z2 = false := by decide
theorem fl5_5 : SS.bxor z5 ef5 = y10 := by decide
theorem sg5_5 : SS.bdot w0 z5 = false := by decide
theorem fl5_6 : SS.bxor z6 ef5 = y11 := by decide
theorem sg5_6 : SS.bdot w0 z6 = false := by decide
theorem incidence6 :
    S1.filter (fun y => SS.bxor y ef6 ∈ S0) = {z0, z5} := by decide
theorem fl6_0 : SS.bxor z0 ef6 = y7 := by decide
theorem sg6_0 : SS.bdot w0 z0 = false := by decide
theorem fl6_5 : SS.bxor z5 ef6 = y12 := by decide
theorem sg6_5 : SS.bdot w0 z5 = false := by decide
theorem incidence7 :
    S1.filter (fun y => SS.bxor y ef7 ∈ S0) = {z0, z6} := by decide
theorem fl7_0 : SS.bxor z0 ef7 = y6 := by decide
theorem sg7_0 : SS.bdot w0 z0 = false := by decide
theorem fl7_6 : SS.bxor z6 ef7 = y12 := by decide
theorem sg7_6 : SS.bdot w0 z6 = false := by decide
theorem incidence8 :
    S1.filter (fun y => SS.bxor y ef8 ∈ S0) = {z0, z7} := by decide
theorem fl8_0 : SS.bxor z0 ef8 = y5 := by decide
theorem sg8_0 : SS.bdot w0 z0 = false := by decide
theorem fl8_7 : SS.bxor z7 ef8 = y12 := by decide
theorem sg8_7 : SS.bdot w0 z7 = false := by decide
theorem incidence9 :
    S1.filter (fun y => SS.bxor y ef9 ∈ S0) = {z0, z8} := by decide
theorem fl9_0 : SS.bxor z0 ef9 = y4 := by decide
theorem sg9_0 : SS.bdot w0 z0 = false := by decide
theorem fl9_8 : SS.bxor z8 ef9 = y12 := by decide
theorem sg9_8 : SS.bdot w0 z8 = false := by decide
theorem incidence10 :
    S1.filter (fun y => SS.bxor y ef10 ∈ S0) = {z0, z1} := by decide
theorem fl10_0 : SS.bxor z0 ef10 = y11 := by decide
theorem sg10_0 : SS.bdot w0 z0 = false := by decide
theorem fl10_1 : SS.bxor z1 ef10 = y12 := by decide
theorem sg10_1 : SS.bdot w0 z1 = false := by decide
theorem incidence11 :
    S1.filter (fun y => SS.bxor y ef11 ∈ S0) = {z0, z2} := by decide
theorem fl11_0 : SS.bxor z0 ef11 = y10 := by decide
theorem sg11_0 : SS.bdot w0 z0 = false := by decide
theorem fl11_2 : SS.bxor z2 ef11 = y12 := by decide
theorem sg11_2 : SS.bdot w0 z2 = false := by decide
theorem incidence12 :
    S1.filter (fun y => SS.bxor y ef12 ∈ S0) = {z0, z3} := by decide
theorem fl12_0 : SS.bxor z0 ef12 = y9 := by decide
theorem sg12_0 : SS.bdot w0 z0 = false := by decide
theorem fl12_3 : SS.bxor z3 ef12 = y12 := by decide
theorem sg12_3 : SS.bdot w0 z3 = false := by decide
theorem incidence13 :
    S1.filter (fun y => SS.bxor y ef13 ∈ S0) = {z0, z4} := by decide
theorem fl13_0 : SS.bxor z0 ef13 = y8 := by decide
theorem sg13_0 : SS.bdot w0 z0 = false := by decide
theorem fl13_4 : SS.bxor z4 ef13 = y12 := by decide
theorem sg13_4 : SS.bdot w0 z4 = false := by decide

/-! ## The moment system -/

/-- The two normalizations, the twenty-one moment equalities, and the
nonnegativity of every probability. -/
structure MomentSystem (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : Real) : Prop where
  n0 : q0 + q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 + q9 + q10 + q11 + q12 = 1
  n1 : r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 = 1
  m1 : q8 + q9 + q10 + q11 + q12 = r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12
  m2 : q4 + q5 + q6 + q7 + q12 = r1 + r2 + r3 + r4 + r9 + r10 + r11 + r12
  m3 : q3 + q5 + q6 + q7 + q9 + q10 + q11 = r0 + r4 + r8 + r10 + r11 + r12
  m4 : q2 + q4 + q6 + q7 + q8 + q10 + q11 = r0 + r3 + r7 + r9 + r11 + r12
  m5 : q1 + q4 + q5 + q7 + q8 + q9 + q11 = r0 + r2 + r6 + r9 + r10 + r12
  m6 : q1 + q2 + q3 + q7 + q11 + q12 = r2 + r3 + r4 + r6 + r7 + r8 + r12
  c12 : q12 = r9 + r10 + r11 + r12
  c13 : q9 + q10 + q11 = r8 + r10 + r11 + r12
  c14 : q8 + q10 + q11 = r7 + r9 + r11 + r12
  c15 : q8 + q9 + q11 = r6 + r9 + r10 + r12
  c16 : q11 + q12 = r6 + r7 + r8 + r12
  c23 : q5 + q6 + q7 = r4 + r10 + r11 + r12
  c24 : q4 + q6 + q7 = r3 + r9 + r11 + r12
  c25 : q4 + q5 + q7 = r2 + r9 + r10 + r12
  c26 : q7 + q12 = r2 + r3 + r4 + r12
  c34 : q6 + q7 + q10 + q11 = r0 + r11 + r12
  c35 : q5 + q7 + q9 + q11 = r0 + r10 + r12
  c36 : q3 + q7 + q11 = r4 + r8 + r12
  c45 : q4 + q7 + q8 + q11 = r0 + r9 + r12
  c46 : q2 + q7 + q11 = r3 + r7 + r12
  c56 : q1 + q7 + q11 = r2 + r6 + r12

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

/-- The star probabilities, the four row sums, and the column agreement. -/
theorem MomentSystem.facts {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) :
    q12 = 1/5 ∧ r0 = 1/5 ∧ q4 + q5 + q6 + q7 = 3/10 ∧ q8 + q9 + q10 + q11 = 3/10 ∧ r8 + r7 + r6 + r5 = 3/10 ∧ r4 + r3 + r2 + r1 = 3/10 ∧ q4 + q8 = q3 + 1/10 ∧ q5 + q9 = q2 + 1/10 ∧ q6 + q10 = q1 + 1/10 ∧ q7 + q11 = q0 + 1/10 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-! ## The Walsh equations -/

def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),
      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

theorem ex0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w0 = star (c y4) * d z3 + star (c y5) * d z4 + star (c y8) * d z7 + star (c y9) * d z8 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_3, fl0_4, fl0_7, fl0_8]
  simp only [sg0_3, sg0_4, sg0_7, sg0_8, SixQubit.signMul_false]
  try ring

theorem ex1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w0 = star (c y4) * d z2 + star (c y6) * d z4 + star (c y8) * d z6 + star (c y10) * d z8 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_2, fl1_4, fl1_6, fl1_8]
  simp only [sg1_2, sg1_4, sg1_6, sg1_8, SixQubit.signMul_false]
  try ring

theorem ex2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w0 = star (c y4) * d z1 + star (c y7) * d z4 + star (c y8) * d z5 + star (c y11) * d z8 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_1, fl2_4, fl2_5, fl2_8]
  simp only [sg2_1, sg2_4, sg2_5, sg2_8, SixQubit.signMul_false]
  try ring

theorem ex3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w0 = star (c y5) * d z2 + star (c y6) * d z3 + star (c y9) * d z6 + star (c y10) * d z7 := by
  unfold offSum
  rw [incidence3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl3_2, fl3_3, fl3_6, fl3_7]
  simp only [sg3_2, sg3_3, sg3_6, sg3_7, SixQubit.signMul_false]
  try ring

theorem ex4 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w0 = star (c y5) * d z1 + star (c y7) * d z3 + star (c y9) * d z5 + star (c y11) * d z7 := by
  unfold offSum
  rw [incidence4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl4_1, fl4_3, fl4_5, fl4_7]
  simp only [sg4_1, sg4_3, sg4_5, sg4_7, SixQubit.signMul_false]
  try ring

theorem ex5 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef5 w0 = star (c y6) * d z1 + star (c y7) * d z2 + star (c y10) * d z5 + star (c y11) * d z6 := by
  unfold offSum
  rw [incidence5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl5_1, fl5_2, fl5_5, fl5_6]
  simp only [sg5_1, sg5_2, sg5_5, sg5_6, SixQubit.signMul_false]
  try ring

theorem ex6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w0 = star (c y7) * d z0 + star (c y12) * d z5 := by
  unfold offSum
  rw [incidence6]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl6_0, fl6_5]
  simp only [sg6_0, sg6_5, SixQubit.signMul_false]
  try ring

theorem ex7 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef7 w0 = star (c y6) * d z0 + star (c y12) * d z6 := by
  unfold offSum
  rw [incidence7]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl7_0, fl7_6]
  simp only [sg7_0, sg7_6, SixQubit.signMul_false]
  try ring

theorem ex8 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef8 w0 = star (c y5) * d z0 + star (c y12) * d z7 := by
  unfold offSum
  rw [incidence8]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl8_0, fl8_7]
  simp only [sg8_0, sg8_7, SixQubit.signMul_false]
  try ring

theorem ex9 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef9 w0 = star (c y4) * d z0 + star (c y12) * d z8 := by
  unfold offSum
  rw [incidence9]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl9_0, fl9_8]
  simp only [sg9_0, sg9_8, SixQubit.signMul_false]
  try ring

theorem ex10 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef10 w0 = star (c y11) * d z0 + star (c y12) * d z1 := by
  unfold offSum
  rw [incidence10]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl10_0, fl10_1]
  simp only [sg10_0, sg10_1, SixQubit.signMul_false]
  try ring

theorem ex11 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef11 w0 = star (c y10) * d z0 + star (c y12) * d z2 := by
  unfold offSum
  rw [incidence11]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl11_0, fl11_2]
  simp only [sg11_0, sg11_2, SixQubit.signMul_false]
  try ring

theorem ex12 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef12 w0 = star (c y9) * d z0 + star (c y12) * d z3 := by
  unfold offSum
  rw [incidence12]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl12_0, fl12_3]
  simp only [sg12_0, sg12_3, SixQubit.signMul_false]
  try ring

theorem ex13 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef13 w0 = star (c y8) * d z0 + star (c y12) * d z4 := by
  unfold offSum
  rw [incidence13]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl13_0, fl13_4]
  simp only [sg13_0, sg13_4, SixQubit.signMul_false]
  try ring

/-! ## The reciprocal pairs and the hub -/

/-- Reciprocal pair at the grid point B_11. -/
theorem rec11 (c d : SS.BitString 6 -> ℂ) (h : offSum c d ef9 w0 = 0) :
    star (c y4) * d z0 + star (c y12) * d z8 = 0 := by
  rw [ex9] at h
  linear_combination h

/-- Reciprocal pair at the grid point B_12. -/
theorem rec12 (c d : SS.BitString 6 -> ℂ) (h : offSum c d ef8 w0 = 0) :
    star (c y5) * d z0 + star (c y12) * d z7 = 0 := by
  rw [ex8] at h
  linear_combination h

/-- Reciprocal pair at the grid point B_13. -/
theorem rec13 (c d : SS.BitString 6 -> ℂ) (h : offSum c d ef7 w0 = 0) :
    star (c y6) * d z0 + star (c y12) * d z6 = 0 := by
  rw [ex7] at h
  linear_combination h

/-- Reciprocal pair at the grid point B_14. -/
theorem rec14 (c d : SS.BitString 6 -> ℂ) (h : offSum c d ef6 w0 = 0) :
    star (c y7) * d z0 + star (c y12) * d z5 = 0 := by
  rw [ex6] at h
  linear_combination h

/-- Reciprocal pair at the grid point B_21. -/
theorem rec21 (c d : SS.BitString 6 -> ℂ) (h : offSum c d ef13 w0 = 0) :
    star (c y8) * d z0 + star (c y12) * d z4 = 0 := by
  rw [ex13] at h
  linear_combination h

/-- Reciprocal pair at the grid point B_22. -/
theorem rec22 (c d : SS.BitString 6 -> ℂ) (h : offSum c d ef12 w0 = 0) :
    star (c y9) * d z0 + star (c y12) * d z3 = 0 := by
  rw [ex12] at h
  linear_combination h

/-- Reciprocal pair at the grid point B_23. -/
theorem rec23 (c d : SS.BitString 6 -> ℂ) (h : offSum c d ef11 w0 = 0) :
    star (c y10) * d z0 + star (c y12) * d z2 = 0 := by
  rw [ex11] at h
  linear_combination h

/-- Reciprocal pair at the grid point B_24. -/
theorem rec24 (c d : SS.BitString 6 -> ℂ) (h : offSum c d ef10 w0 = 0) :
    star (c y11) * d z0 + star (c y12) * d z1 = 0 := by
  rw [ex10] at h
  linear_combination h

/-! ## The permanents and their collapse -/

/-- The permanent of columns 1 and 2, collapsed through the hub. -/
theorem perm12 (c d : SS.BitString 6 -> ℂ)
    (h : offSum c d ef0 w0 = 0)
    (s1 : star (c y9) * d z8 = star (c y4) * d z3)
    (s2 : star (c y8) * d z7 = star (c y5) * d z4) :
    star (c y4) * d z3 + star (c y5) * d z4 = 0 := by
  rw [ex0] at h
  linear_combination h / 2 - s1 / 2 - s2 / 2

/-- The same four terms read the other way. -/
theorem perm12' (c d : SS.BitString 6 -> ℂ)
    (h : offSum c d ef0 w0 = 0)
    (s1 : star (c y9) * d z8 = star (c y4) * d z3)
    (s2 : star (c y8) * d z7 = star (c y5) * d z4) :
    star (c y9) * d z8 + star (c y8) * d z7 = 0 := by
  rw [ex0] at h
  linear_combination h / 2 + s1 / 2 + s2 / 2

/-- The permanent of columns 1 and 3, collapsed through the hub. -/
theorem perm13 (c d : SS.BitString 6 -> ℂ)
    (h : offSum c d ef1 w0 = 0)
    (s1 : star (c y10) * d z8 = star (c y4) * d z2)
    (s2 : star (c y8) * d z6 = star (c y6) * d z4) :
    star (c y4) * d z2 + star (c y6) * d z4 = 0 := by
  rw [ex1] at h
  linear_combination h / 2 - s1 / 2 - s2 / 2

/-- The same four terms read the other way. -/
theorem perm13' (c d : SS.BitString 6 -> ℂ)
    (h : offSum c d ef1 w0 = 0)
    (s1 : star (c y10) * d z8 = star (c y4) * d z2)
    (s2 : star (c y8) * d z6 = star (c y6) * d z4) :
    star (c y10) * d z8 + star (c y8) * d z6 = 0 := by
  rw [ex1] at h
  linear_combination h / 2 + s1 / 2 + s2 / 2

/-- The permanent of columns 1 and 4, collapsed through the hub. -/
theorem perm14 (c d : SS.BitString 6 -> ℂ)
    (h : offSum c d ef2 w0 = 0)
    (s1 : star (c y11) * d z8 = star (c y4) * d z1)
    (s2 : star (c y8) * d z5 = star (c y7) * d z4) :
    star (c y4) * d z1 + star (c y7) * d z4 = 0 := by
  rw [ex2] at h
  linear_combination h / 2 - s1 / 2 - s2 / 2

/-- The same four terms read the other way. -/
theorem perm14' (c d : SS.BitString 6 -> ℂ)
    (h : offSum c d ef2 w0 = 0)
    (s1 : star (c y11) * d z8 = star (c y4) * d z1)
    (s2 : star (c y8) * d z5 = star (c y7) * d z4) :
    star (c y11) * d z8 + star (c y8) * d z5 = 0 := by
  rw [ex2] at h
  linear_combination h / 2 + s1 / 2 + s2 / 2

/-- The permanent of columns 2 and 3, collapsed through the hub. -/
theorem perm23 (c d : SS.BitString 6 -> ℂ)
    (h : offSum c d ef3 w0 = 0)
    (s1 : star (c y10) * d z7 = star (c y5) * d z2)
    (s2 : star (c y9) * d z6 = star (c y6) * d z3) :
    star (c y5) * d z2 + star (c y6) * d z3 = 0 := by
  rw [ex3] at h
  linear_combination h / 2 - s1 / 2 - s2 / 2

/-- The same four terms read the other way. -/
theorem perm23' (c d : SS.BitString 6 -> ℂ)
    (h : offSum c d ef3 w0 = 0)
    (s1 : star (c y10) * d z7 = star (c y5) * d z2)
    (s2 : star (c y9) * d z6 = star (c y6) * d z3) :
    star (c y10) * d z7 + star (c y9) * d z6 = 0 := by
  rw [ex3] at h
  linear_combination h / 2 + s1 / 2 + s2 / 2

/-- The permanent of columns 2 and 4, collapsed through the hub. -/
theorem perm24 (c d : SS.BitString 6 -> ℂ)
    (h : offSum c d ef4 w0 = 0)
    (s1 : star (c y11) * d z7 = star (c y5) * d z1)
    (s2 : star (c y9) * d z5 = star (c y7) * d z3) :
    star (c y5) * d z1 + star (c y7) * d z3 = 0 := by
  rw [ex4] at h
  linear_combination h / 2 - s1 / 2 - s2 / 2

/-- The same four terms read the other way. -/
theorem perm24' (c d : SS.BitString 6 -> ℂ)
    (h : offSum c d ef4 w0 = 0)
    (s1 : star (c y11) * d z7 = star (c y5) * d z1)
    (s2 : star (c y9) * d z5 = star (c y7) * d z3) :
    star (c y11) * d z7 + star (c y9) * d z5 = 0 := by
  rw [ex4] at h
  linear_combination h / 2 + s1 / 2 + s2 / 2

/-- The permanent of columns 3 and 4, collapsed through the hub. -/
theorem perm34 (c d : SS.BitString 6 -> ℂ)
    (h : offSum c d ef5 w0 = 0)
    (s1 : star (c y11) * d z6 = star (c y6) * d z1)
    (s2 : star (c y10) * d z5 = star (c y7) * d z2) :
    star (c y6) * d z1 + star (c y7) * d z2 = 0 := by
  rw [ex5] at h
  linear_combination h / 2 - s1 / 2 - s2 / 2

/-- The same four terms read the other way. -/
theorem perm34' (c d : SS.BitString 6 -> ℂ)
    (h : offSum c d ef5 w0 = 0)
    (s1 : star (c y11) * d z6 = star (c y6) * d z1)
    (s2 : star (c y10) * d z5 = star (c y7) * d z2) :
    star (c y11) * d z6 + star (c y10) * d z5 = 0 := by
  rw [ex5] at h
  linear_combination h / 2 + s1 / 2 + s2 / 2

/-- Transitivity through the hub: division-free. -/
theorem hub (c d : SS.BitString 6 -> ℂ) (x1 x2 : SS.BitString 6) (yh1 yh2 : SS.BitString 6)
    (h1 : star (c x1) * d z0 + star (c y12) * d yh1 = 0)
    (h2 : star (c x2) * d z0 + star (c y12) * d yh2 = 0)
    (hs : star (c y12) * d z0 ≠ 0) :
    star (c x2) * d yh1 = star (c x1) * d yh2 := by
  have key : (star (c x2) * d yh1 - star (c x1) * d yh2) *
      (star (c y12) * d z0) = 0 := by
    linear_combination (star (c x2) * d z0) * h1 - (star (c x1) * d z0) * h2
  rcases mul_eq_zero.mp key with hh | hh
  · linear_combination hh
  · exact absurd hh hs

/-! ## The row argument -/

/-- If one factor of a two-term relation vanishes while the other coefficient
does not, the remaining amplitude vanishes. -/
theorem kill (a b w wj : ℂ) (ha : a = 0) (hw : wj ≠ 0)
    (R : a * w + b * wj = 0) : b = 0 := by
  have hb : b * wj = 0 := by rw [ha] at R; linear_combination R
  rcases mul_eq_zero.mp hb with h | h
  · exact h
  · exact absurd h hw

/-- The reciprocal pair read the other way: a vanishing top amplitude forces
its bottom partner to vanish. -/
theorem bridge2 (c d : SS.BitString 6 -> ℂ) (x : SS.BitString 6) (yh : SS.BitString 6)
    (hrec : star (c x) * d z0 + star (c y12) * d yh = 0)
    (hs : d z0 ≠ 0) (hy : d yh = 0) : c x = 0 := by
  have h2 : star (c x) * d z0 = 0 := by
    rw [hy] at hrec; linear_combination hrec
  rcases mul_eq_zero.mp h2 with h | h
  · simpa using congrArg star h
  · exact absurd h hs

/-! ## The no-go -/

/-- **Orbit 38 is impossible.** -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11)) (Complex.normSq (c y12))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)) (Complex.normSq (d z12)))
    (E0 : offSum c d ef0 w0 = 0)
    (E1 : offSum c d ef1 w0 = 0)
    (E2 : offSum c d ef2 w0 = 0)
    (E3 : offSum c d ef3 w0 = 0)
    (E4 : offSum c d ef4 w0 = 0)
    (E5 : offSum c d ef5 w0 = 0)
    (E6 : offSum c d ef6 w0 = 0)
    (E7 : offSum c d ef7 w0 = 0)
    (E8 : offSum c d ef8 w0 = 0)
    (E9 : offSum c d ef9 w0 = 0)
    (E10 : offSum c d ef10 w0 = 0)
    (E11 : offSum c d ef11 w0 = 0)
    (E12 : offSum c d ef12 w0 = 0)
    (E13 : offSum c d ef13 w0 = 0)
    : False := by
  obtain ⟨fqS, frS, fb1, fb2, ft1, ft2, fa0, fa1, fa2, fa3⟩ := hm.facts
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12⟩ := hm
  have hcS : c y12 ≠ 0 := fun h => by rw [h] at fqS; norm_num at fqS
  have hdS : d z0 ≠ 0 := fun h => by rw [h] at frS; norm_num at frS
  have hstar : star (c y12) * d z0 ≠ 0 :=
    mul_ne_zero (star_ne_zero.mpr hcS) hdS
  -- the eight reciprocal relations
  have C11 := rec11 c d E9
  have C12 := rec12 c d E8
  have C13 := rec13 c d E7
  have C14 := rec14 c d E6
  have C21 := rec21 c d E13
  have C22 := rec22 c d E12
  have C23 := rec23 c d E11
  have C24 := rec24 c d E10
  -- transitivity through the hub, twice per column pair
  have H12a := hub c d y4 y9 z8 z3 C11 C22 hstar
  have H12b := hub c d y5 y8 z7 z4 C12 C21 hstar
  have H13a := hub c d y4 y10 z8 z2 C11 C23 hstar
  have H13b := hub c d y6 y8 z6 z4 C13 C21 hstar
  have H14a := hub c d y4 y11 z8 z1 C11 C24 hstar
  have H14b := hub c d y7 y8 z5 z4 C14 C21 hstar
  have H23a := hub c d y5 y10 z7 z2 C12 C23 hstar
  have H23b := hub c d y6 y9 z6 z3 C13 C22 hstar
  have H24a := hub c d y5 y11 z7 z1 C12 C24 hstar
  have H24b := hub c d y7 y9 z5 z3 C14 C22 hstar
  have H34a := hub c d y6 y11 z6 z1 C13 C24 hstar
  have H34b := hub c d y7 y10 z5 z2 C14 C23 hstar
  -- the six collapsed permanents, each read both ways
  have R12 := perm12 c d E0 H12a H12b
  have Rp12 := perm12' c d E0 H12a H12b
  have R13 := perm13 c d E1 H13a H13b
  have Rp13 := perm13' c d E1 H13a H13b
  have R14 := perm14 c d E2 H14a H14b
  have Rp14 := perm14' c d E2 H14a H14b
  have R23 := perm23 c d E3 H23a H23b
  have Rp23 := perm23' c d E3 H23a H23b
  have R24 := perm24 c d E4 H24a H24b
  have Rp24 := perm24' c d E4 H24a H24b
  have R34 := perm34 c d E5 H34a H34b
  have Rp34 := perm34' c d E5 H34a H34b
  -- no first-row amplitude vanishes
  have N0 : c y4 ≠ 0 := by
    intro hv
    have e0 : Complex.normSq (c y4) = 0 := by rw [hv]; simp
    have hb2 : c y8 ≠ 0 := by
      intro h2
      have e2 : Complex.normSq (c y8) = 0 := by rw [h2]; simp
      linarith [fa0, nq3, e0, e2]
    have hw : d z4 ≠ 0 := fun h => hb2 (bridge2 c d y8 z4 C21 hdS h)
    have hus : (star (c y4)) = 0 := by rw [hv]; simp
    have K1 : (star (c y5)) = 0 :=
      kill (star (c y4)) (star (c y5)) (d z3) (d z4) hus hw (by linear_combination R12)
    have e1 : Complex.normSq (c y5) = 0 := by
      rw [show c y5 = 0 from by simpa using congrArg star K1]; simp
    have K2 : (star (c y6)) = 0 :=
      kill (star (c y4)) (star (c y6)) (d z2) (d z4) hus hw (by linear_combination R13)
    have e2 : Complex.normSq (c y6) = 0 := by
      rw [show c y6 = 0 from by simpa using congrArg star K2]; simp
    have K3 : (star (c y7)) = 0 :=
      kill (star (c y4)) (star (c y7)) (d z1) (d z4) hus hw (by linear_combination R14)
    have e3 : Complex.normSq (c y7) = 0 := by
      rw [show c y7 = 0 from by simpa using congrArg star K3]; simp
    linarith [fb1, e0, e1, e2, e3]
  have N1 : c y5 ≠ 0 := by
    intro hv
    have e1 : Complex.normSq (c y5) = 0 := by rw [hv]; simp
    have hb2 : c y9 ≠ 0 := by
      intro h2
      have e2 : Complex.normSq (c y9) = 0 := by rw [h2]; simp
      linarith [fa1, nq2, e1, e2]
    have hw : d z3 ≠ 0 := fun h => hb2 (bridge2 c d y9 z3 C22 hdS h)
    have hus : (star (c y5)) = 0 := by rw [hv]; simp
    have K0 : (star (c y4)) = 0 :=
      kill (star (c y5)) (star (c y4)) (d z4) (d z3) hus hw (by linear_combination R12)
    have e0 : Complex.normSq (c y4) = 0 := by
      rw [show c y4 = 0 from by simpa using congrArg star K0]; simp
    have K2 : (star (c y6)) = 0 :=
      kill (star (c y5)) (star (c y6)) (d z2) (d z3) hus hw (by linear_combination R23)
    have e2 : Complex.normSq (c y6) = 0 := by
      rw [show c y6 = 0 from by simpa using congrArg star K2]; simp
    have K3 : (star (c y7)) = 0 :=
      kill (star (c y5)) (star (c y7)) (d z1) (d z3) hus hw (by linear_combination R24)
    have e3 : Complex.normSq (c y7) = 0 := by
      rw [show c y7 = 0 from by simpa using congrArg star K3]; simp
    linarith [fb1, e0, e1, e2, e3]
  have N2 : c y6 ≠ 0 := by
    intro hv
    have e2 : Complex.normSq (c y6) = 0 := by rw [hv]; simp
    have hb2 : c y10 ≠ 0 := by
      intro h2
      have e2 : Complex.normSq (c y10) = 0 := by rw [h2]; simp
      linarith [fa2, nq1, e2, e2]
    have hw : d z2 ≠ 0 := fun h => hb2 (bridge2 c d y10 z2 C23 hdS h)
    have hus : (star (c y6)) = 0 := by rw [hv]; simp
    have K0 : (star (c y4)) = 0 :=
      kill (star (c y6)) (star (c y4)) (d z4) (d z2) hus hw (by linear_combination R13)
    have e0 : Complex.normSq (c y4) = 0 := by
      rw [show c y4 = 0 from by simpa using congrArg star K0]; simp
    have K1 : (star (c y5)) = 0 :=
      kill (star (c y6)) (star (c y5)) (d z3) (d z2) hus hw (by linear_combination R23)
    have e1 : Complex.normSq (c y5) = 0 := by
      rw [show c y5 = 0 from by simpa using congrArg star K1]; simp
    have K3 : (star (c y7)) = 0 :=
      kill (star (c y6)) (star (c y7)) (d z1) (d z2) hus hw (by linear_combination R34)
    have e3 : Complex.normSq (c y7) = 0 := by
      rw [show c y7 = 0 from by simpa using congrArg star K3]; simp
    linarith [fb1, e0, e1, e2, e3]
  have N3 : c y7 ≠ 0 := by
    intro hv
    have e3 : Complex.normSq (c y7) = 0 := by rw [hv]; simp
    have hb2 : c y11 ≠ 0 := by
      intro h2
      have e2 : Complex.normSq (c y11) = 0 := by rw [h2]; simp
      linarith [fa3, nq0, e3, e2]
    have hw : d z1 ≠ 0 := fun h => hb2 (bridge2 c d y11 z1 C24 hdS h)
    have hus : (star (c y7)) = 0 := by rw [hv]; simp
    have K0 : (star (c y4)) = 0 :=
      kill (star (c y7)) (star (c y4)) (d z4) (d z1) hus hw (by linear_combination R14)
    have e0 : Complex.normSq (c y4) = 0 := by
      rw [show c y4 = 0 from by simpa using congrArg star K0]; simp
    have K1 : (star (c y5)) = 0 :=
      kill (star (c y7)) (star (c y5)) (d z3) (d z1) hus hw (by linear_combination R24)
    have e1 : Complex.normSq (c y5) = 0 := by
      rw [show c y5 = 0 from by simpa using congrArg star K1]; simp
    have K2 : (star (c y6)) = 0 :=
      kill (star (c y7)) (star (c y6)) (d z2) (d z1) hus hw (by linear_combination R34)
    have e2 : Complex.normSq (c y6) = 0 := by
      rw [show c y6 = 0 from by simpa using congrArg star K2]; simp
    linarith [fb1, e0, e1, e2, e3]
  -- their partners on the top fiber are therefore nonzero too
  have T0 : d z8 ≠ 0 := fun h => N0 (bridge2 c d y4 z8 C11 hdS h)
  have T1 : d z7 ≠ 0 := fun h => N1 (bridge2 c d y5 z7 C12 hdS h)
  have T2 : d z6 ≠ 0 := fun h => N2 (bridge2 c d y6 z6 C13 hdS h)
  have T3 : d z5 ≠ 0 := fun h => N3 (bridge2 c d y7 z5 C14 hdS h)
  -- and now the same argument on the second row, via the mirror relations
  have P0 : c y8 ≠ 0 := by
    intro hv
    have f0 : Complex.normSq (c y8) = 0 := by rw [hv]; simp
    have hus : (star (c y8)) = 0 := by rw [hv]; simp
    have L1 : (star (c y9)) = 0 :=
      kill (star (c y8)) (star (c y9)) (d z7) (d z8) hus T0 (by linear_combination Rp12)
    have f1 : Complex.normSq (c y9) = 0 := by
      rw [show c y9 = 0 from by simpa using congrArg star L1]; simp
    have L2 : (star (c y10)) = 0 :=
      kill (star (c y8)) (star (c y10)) (d z6) (d z8) hus T0 (by linear_combination Rp13)
    have f2 : Complex.normSq (c y10) = 0 := by
      rw [show c y10 = 0 from by simpa using congrArg star L2]; simp
    have L3 : (star (c y11)) = 0 :=
      kill (star (c y8)) (star (c y11)) (d z5) (d z8) hus T0 (by linear_combination Rp14)
    have f3 : Complex.normSq (c y11) = 0 := by
      rw [show c y11 = 0 from by simpa using congrArg star L3]; simp
    linarith [fb2, f0, f1, f2, f3]
  have P1 : c y9 ≠ 0 := by
    intro hv
    have f1 : Complex.normSq (c y9) = 0 := by rw [hv]; simp
    have hus : (star (c y9)) = 0 := by rw [hv]; simp
    have L0 : (star (c y8)) = 0 :=
      kill (star (c y9)) (star (c y8)) (d z8) (d z7) hus T1 (by linear_combination Rp12)
    have f0 : Complex.normSq (c y8) = 0 := by
      rw [show c y8 = 0 from by simpa using congrArg star L0]; simp
    have L2 : (star (c y10)) = 0 :=
      kill (star (c y9)) (star (c y10)) (d z6) (d z7) hus T1 (by linear_combination Rp23)
    have f2 : Complex.normSq (c y10) = 0 := by
      rw [show c y10 = 0 from by simpa using congrArg star L2]; simp
    have L3 : (star (c y11)) = 0 :=
      kill (star (c y9)) (star (c y11)) (d z5) (d z7) hus T1 (by linear_combination Rp24)
    have f3 : Complex.normSq (c y11) = 0 := by
      rw [show c y11 = 0 from by simpa using congrArg star L3]; simp
    linarith [fb2, f0, f1, f2, f3]
  have P2 : c y10 ≠ 0 := by
    intro hv
    have f2 : Complex.normSq (c y10) = 0 := by rw [hv]; simp
    have hus : (star (c y10)) = 0 := by rw [hv]; simp
    have L0 : (star (c y8)) = 0 :=
      kill (star (c y10)) (star (c y8)) (d z8) (d z6) hus T2 (by linear_combination Rp13)
    have f0 : Complex.normSq (c y8) = 0 := by
      rw [show c y8 = 0 from by simpa using congrArg star L0]; simp
    have L1 : (star (c y9)) = 0 :=
      kill (star (c y10)) (star (c y9)) (d z7) (d z6) hus T2 (by linear_combination Rp23)
    have f1 : Complex.normSq (c y9) = 0 := by
      rw [show c y9 = 0 from by simpa using congrArg star L1]; simp
    have L3 : (star (c y11)) = 0 :=
      kill (star (c y10)) (star (c y11)) (d z5) (d z6) hus T2 (by linear_combination Rp34)
    have f3 : Complex.normSq (c y11) = 0 := by
      rw [show c y11 = 0 from by simpa using congrArg star L3]; simp
    linarith [fb2, f0, f1, f2, f3]
  have P3 : c y11 ≠ 0 := by
    intro hv
    have f3 : Complex.normSq (c y11) = 0 := by rw [hv]; simp
    have hus : (star (c y11)) = 0 := by rw [hv]; simp
    have L0 : (star (c y8)) = 0 :=
      kill (star (c y11)) (star (c y8)) (d z8) (d z5) hus T3 (by linear_combination Rp14)
    have f0 : Complex.normSq (c y8) = 0 := by
      rw [show c y8 = 0 from by simpa using congrArg star L0]; simp
    have L1 : (star (c y9)) = 0 :=
      kill (star (c y11)) (star (c y9)) (d z7) (d z5) hus T3 (by linear_combination Rp24)
    have f1 : Complex.normSq (c y9) = 0 := by
      rw [show c y9 = 0 from by simpa using congrArg star L1]; simp
    have L2 : (star (c y10)) = 0 :=
      kill (star (c y11)) (star (c y10)) (d z6) (d z5) hus T3 (by linear_combination Rp34)
    have f2 : Complex.normSq (c y10) = 0 := by
      rw [show c y10 = 0 from by simpa using congrArg star L2]; simp
    linarith [fb2, f0, f1, f2, f3]
  have M0 : d z4 ≠ 0 := fun h => P0 (bridge2 c d y8 z4 C21 hdS h)
  have M1 : d z3 ≠ 0 := fun h => P1 (bridge2 c d y9 z3 C22 hdS h)
  have M2 : d z2 ≠ 0 := fun h => P2 (bridge2 c d y10 z2 C23 hdS h)
  have M3 : d z1 ≠ 0 := fun h => P3 (bridge2 c d y11 z1 C24 hdS h)
  -- the odd cycle on the first three columns
  have key : (2 : ℂ) * ((star (c y4) * d z3) * (star (c y5) * d z2) * (star (c y6) * d z4)) = 0 := by
    linear_combination ((star (c y5) * d z2) * (star (c y6) * d z4)) * R12
      - ((star (c y5) * d z4) * (star (c y6) * d z4)) * R23
      + ((star (c y5) * d z4) * (star (c y6) * d z3)) * R13
  have hcyc : (star (c y4) * d z3) * (star (c y5) * d z2) * (star (c y6) * d z4) = 0 := by linear_combination key / 2
  simp [N0, N1, N2, M0, M1, M2] at hcyc

end

end SixQubit.Orbit38
