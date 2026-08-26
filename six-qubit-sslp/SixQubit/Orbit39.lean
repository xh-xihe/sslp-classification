import Mathlib

import SS.FullKL
import SixQubit.Common

/-!
# Six-qubit no-go for moment orbit 39

Orbit 39 of `six_qubit_sslp_v7.tex`: q = 5, angle vector
a = (1, 1, 2, 3, 3, 3), residues 0 and 1, closed in Section 17.

The flip mask 100000 has 5 incidences on the two fibers.  The 7 admissible
dressings of that flip give 7 linear equations in the surviving edge
products, and 2 of them combine to force one product to vanish -- while the
same moment polytope forces both of its endpoint probabilities to be
strictly positive.  This is the k = 5 case of the Section 11 mechanism.

Everything computational is decided by the Lean kernel; `native_decide` is
not used.
-/

namespace SixQubit.Orbit39

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]

def y0 : SS.BitString 6 := bs false false false false false false  -- 000000
def y1 : SS.BitString 6 := bs false false true  false false true   -- 001001
def y2 : SS.BitString 6 := bs false false true  false true  false  -- 001010
def y3 : SS.BitString 6 := bs false false true  true  false false  -- 001100
def y4 : SS.BitString 6 := bs false true  false true  true  true   -- 010111
def y5 : SS.BitString 6 := bs true  false false true  true  true   -- 100111
def y6 : SS.BitString 6 := bs true  true  false false false true   -- 110001
def y7 : SS.BitString 6 := bs true  true  false false true  false  -- 110010
def y8 : SS.BitString 6 := bs true  true  false true  false false  -- 110100
def y9 : SS.BitString 6 := bs true  true  true  false true  true   -- 111011
def y10 : SS.BitString 6 := bs true  true  true  true  false true   -- 111101
def y11 : SS.BitString 6 := bs true  true  true  true  true  false  -- 111110

def z0 : SS.BitString 6 := bs false false false false true  true   -- 000011
def z1 : SS.BitString 6 := bs false false false true  false true   -- 000101
def z2 : SS.BitString 6 := bs false false false true  true  false  -- 000110
def z3 : SS.BitString 6 := bs false false true  true  true  true   -- 001111
def z4 : SS.BitString 6 := bs false true  false false false false  -- 010000
def z5 : SS.BitString 6 := bs false true  true  false false true   -- 011001
def z6 : SS.BitString 6 := bs false true  true  false true  false  -- 011010
def z7 : SS.BitString 6 := bs false true  true  true  false false  -- 011100
def z8 : SS.BitString 6 := bs true  false false false false false  -- 100000
def z9 : SS.BitString 6 := bs true  false true  false false true   -- 101001
def z10 : SS.BitString 6 := bs true  false true  false true  false  -- 101010
def z11 : SS.BitString 6 := bs true  false true  true  false false  -- 101100
def z12 : SS.BitString 6 := bs true  true  false true  true  true   -- 110111

def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11}
def S1 : Finset (SS.BitString 6) := {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12}

def av : Fin 6 -> ZMod 5 := ![1, 1, 2, 3, 3, 3]

/-- Each support is exactly its residue fiber, decided over all 64 strings. -/
theorem S0_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 0) = S0 := by
  decide

theorem S1_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 1) = S1 := by
  decide

/-- Flip mask 100000. -/
def ef : SS.BitString 6 := bs true  false false false false false

/-- Dressing 0: Z-mask 000000. -/
def w0 : SS.BitString 6 := bs false false false false false false
/-- Dressing 1: Z-mask 010000. -/
def w1 : SS.BitString 6 := bs false true  false false false false

theorem incidence :
    S1.filter (fun y => SS.bxor y ef ∈ S0) = {z8, z9, z10, z11, z12} := by decide

theorem flip_z8 : SS.bxor z8 ef = y0 := by decide
theorem flip_z9 : SS.bxor z9 ef = y1 := by decide
theorem flip_z10 : SS.bxor z10 ef = y2 := by decide
theorem flip_z11 : SS.bxor z11 ef = y3 := by decide
theorem flip_z12 : SS.bxor z12 ef = y4 := by decide

theorem sg0_8 : SS.bdot w0 z8 = false := by decide
theorem sg0_9 : SS.bdot w0 z9 = false := by decide
theorem sg0_10 : SS.bdot w0 z10 = false := by decide
theorem sg0_11 : SS.bdot w0 z11 = false := by decide
theorem sg0_12 : SS.bdot w0 z12 = false := by decide
theorem sg1_8 : SS.bdot w1 z8 = false := by decide
theorem sg1_9 : SS.bdot w1 z9 = false := by decide
theorem sg1_10 : SS.bdot w1 z10 = false := by decide
theorem sg1_11 : SS.bdot w1 z11 = false := by decide
theorem sg1_12 : SS.bdot w1 z12 = true := by decide

theorem signMul_zero (b : Bool) : SixQubit.signMul b (0 : ℂ) = 0 := by
  cases b <;> simp [SixQubit.signMul]

/-! ## The moment system -/

/-- The two normalizations, the twenty-one moment equalities, and the
nonnegativity of every probability. -/
structure MomentSystem (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : Real) : Prop where
  n0 : q0 + q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 + q9 + q10 + q11 = 1
  n1 : r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 = 1
  m1 : q5 + q6 + q7 + q8 + q9 + q10 + q11 = r8 + r9 + r10 + r11 + r12
  m2 : q4 + q6 + q7 + q8 + q9 + q10 + q11 = r4 + r5 + r6 + r7 + r12
  m3 : q1 + q2 + q3 + q9 + q10 + q11 = r3 + r5 + r6 + r7 + r9 + r10 + r11
  m4 : q3 + q4 + q5 + q8 + q10 + q11 = r1 + r2 + r3 + r7 + r11 + r12
  m5 : q2 + q4 + q5 + q7 + q9 + q11 = r0 + r2 + r3 + r6 + r10 + r12
  m6 : q1 + q4 + q5 + q6 + q9 + q10 = r0 + r1 + r3 + r5 + r9 + r12
  c12 : q6 + q7 + q8 + q9 + q10 + q11 = r12
  c13 : q9 + q10 + q11 = r9 + r10 + r11
  c14 : q5 + q8 + q10 + q11 = r11 + r12
  c15 : q5 + q7 + q9 + q11 = r10 + r12
  c16 : q5 + q6 + q9 + q10 = r9 + r12
  c23 : q9 + q10 + q11 = r5 + r6 + r7
  c24 : q4 + q8 + q10 + q11 = r7 + r12
  c25 : q4 + q7 + q9 + q11 = r6 + r12
  c26 : q4 + q6 + q9 + q10 = r5 + r12
  c34 : q3 + q10 + q11 = r3 + r7 + r11
  c35 : q2 + q9 + q11 = r3 + r6 + r10
  c36 : q1 + q9 + q10 = r3 + r5 + r9
  c45 : q4 + q5 + q11 = r2 + r3 + r12
  c46 : q4 + q5 + q10 = r1 + r3 + r12
  c56 : q4 + q5 + q9 = r0 + r3 + r12

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

/-- The two endpoint probabilities of the target edge are forced. -/
theorem MomentSystem.endpoints {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : Real}
    (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) :
    q4 = 1/5 ∧ r12 = 3/10 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12⟩ := h
  refine ⟨?_, ?_⟩ <;> linarith

theorem MomentSystem.endpoints_pos {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : Real}
    (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) :
    0 < q4 ∧ 0 < r12 := by
  obtain ⟨e1, e2⟩ := h.endpoints
  refine ⟨?_, ?_⟩ <;> simp_all

/-! ## The Walsh system -/

def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),
      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

theorem expand0 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef w0 = star (c y0) * d z8 + star (c y1) * d z9 + star (c y2) * d z10 + star (c y3) * d z11 + star (c y4) * d z12 := by
  unfold offSum
  rw [incidence]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_z8, flip_z9, flip_z10, flip_z11, flip_z12]
  simp only [sg0_8, sg0_9, sg0_10, sg0_11, sg0_12, SixQubit.signMul_false]
  ring

theorem expand1 (c d : SS.BitString 6 -> ℂ)
    : offSum c d ef w1 = star (c y0) * d z8 + star (c y1) * d z9 + star (c y2) * d z10 + star (c y3) * d z11 - star (c y4) * d z12 := by
  unfold offSum
  rw [incidence]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_z8, flip_z9, flip_z10, flip_z11, flip_z12]
  simp only [sg1_8, sg1_9, sg1_10, sg1_11, sg1_12, SixQubit.signMul_true, SixQubit.signMul_false]
  ring

/-- The target edge product is forced to vanish. -/
theorem target_zero (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef w0 = 0)
    (h1 : offSum c d ef w1 = 0)
    : star (c y4) * d z12 = 0 := by
  rw [expand0 c d ] at h0
  rw [expand1 c d ] at h1
  linear_combination ((1 / 2) : ℂ) * h0 + ((-1 / 2) : ℂ) * h1

/-- **Orbit 39 is impossible.** -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)) (Complex.normSq (d z12)))
    (h0 : offSum c d ef w0 = 0)
    (h1 : offSum c d ef w1 = 0)
    : False := by
  obtain ⟨hq, hr⟩ := hm.endpoints_pos
  have ht := target_zero c d  h0 h1
  rcases mul_eq_zero.mp ht with h | h
  · rw [show c y4 = 0 from by simpa using congrArg star h] at hq; simp at hq
  · rw [h] at hr; simp at hr

end

end SixQubit.Orbit39
