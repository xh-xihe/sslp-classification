import Mathlib

import SS.FullKL
import SixQubit.Common

/-!
# Six-qubit no-go for moment orbit 28

Orbit 28 of `six_qubit_sslp_v7.tex`: q = 4, angle vector
a = (1, 1, 1, 1, 1, 2), residues 0 and 1, closed in Section 15.

The support here is a *proper* subset of the fiber.  The flip has 8
incidences on the two fibers, but the moment polytope forces 6 of the
endpoint probabilities to zero, and only two edges survive.  The support is
derived, not assumed: `MomentSystem.tops_zero` proves the vanishing from the
moment equations together with the nonnegativity of probability.

Everything computational is decided by the Lean kernel; `native_decide` is
not used.
-/

namespace SixQubit.Orbit28

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

/-! ## The two fibers -/

def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]

def y0 : SS.BitString 6 := bs false false false false false false  -- 000000
def y1 : SS.BitString 6 := bs false false false true  true  true   -- 000111
def y2 : SS.BitString 6 := bs false false true  false true  true   -- 001011
def y3 : SS.BitString 6 := bs false false true  true  false true   -- 001101
def y4 : SS.BitString 6 := bs false true  false false true  true   -- 010011
def y5 : SS.BitString 6 := bs false true  false true  false true   -- 010101
def y6 : SS.BitString 6 := bs false true  true  false false true   -- 011001
def y7 : SS.BitString 6 := bs false true  true  true  true  false  -- 011110
def y8 : SS.BitString 6 := bs true  false false false true  true   -- 100011
def y9 : SS.BitString 6 := bs true  false false true  false true   -- 100101
def y10 : SS.BitString 6 := bs true  false true  false false true   -- 101001
def y11 : SS.BitString 6 := bs true  false true  true  true  false  -- 101110
def y12 : SS.BitString 6 := bs true  true  false false false true   -- 110001
def y13 : SS.BitString 6 := bs true  true  false true  true  false  -- 110110
def y14 : SS.BitString 6 := bs true  true  true  false true  false  -- 111010
def y15 : SS.BitString 6 := bs true  true  true  true  false false  -- 111100

def z0 : SS.BitString 6 := bs false false false false true  false  -- 000010
def z1 : SS.BitString 6 := bs false false false true  false false  -- 000100
def z2 : SS.BitString 6 := bs false false true  false false false  -- 001000
def z3 : SS.BitString 6 := bs false false true  true  true  true   -- 001111
def z4 : SS.BitString 6 := bs false true  false false false false  -- 010000
def z5 : SS.BitString 6 := bs false true  false true  true  true   -- 010111
def z6 : SS.BitString 6 := bs false true  true  false true  true   -- 011011
def z7 : SS.BitString 6 := bs false true  true  true  false true   -- 011101
def z8 : SS.BitString 6 := bs true  false false false false false  -- 100000
def z9 : SS.BitString 6 := bs true  false false true  true  true   -- 100111
def z10 : SS.BitString 6 := bs true  false true  false true  true   -- 101011
def z11 : SS.BitString 6 := bs true  false true  true  false true   -- 101101
def z12 : SS.BitString 6 := bs true  true  false false true  true   -- 110011
def z13 : SS.BitString 6 := bs true  true  false true  false true   -- 110101
def z14 : SS.BitString 6 := bs true  true  true  false false true   -- 111001
def z15 : SS.BitString 6 := bs true  true  true  true  true  false  -- 111110

def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15}
def S1 : Finset (SS.BitString 6) := {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15}

def av : Fin 6 -> ZMod 4 := ![1, 1, 1, 1, 1, 2]

theorem S0_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 0) = S0 := by
  decide

theorem S1_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 1) = S1 := by
  decide

/-! ## The incidence set of the flip -/

/-- Flip mask 100000. -/
def ef : SS.BitString 6 := bs true  false false false false false

/-- The separating coordinate, qubit 2. -/
def ez : SS.BitString 6 := SS.stdBasis 1

theorem incidence :
    S1.filter (fun y => SS.bxor y ef ∈ S0) = {z8, z9, z10, z11, z12, z13, z14, z15} := by decide

theorem flip_z8 : SS.bxor z8 ef = y0 := by decide
theorem flip_z9 : SS.bxor z9 ef = y1 := by decide
theorem flip_z10 : SS.bxor z10 ef = y2 := by decide
theorem flip_z11 : SS.bxor z11 ef = y3 := by decide
theorem flip_z12 : SS.bxor z12 ef = y4 := by decide
theorem flip_z13 : SS.bxor z13 ef = y5 := by decide
theorem flip_z14 : SS.bxor z14 ef = y6 := by decide
theorem flip_z15 : SS.bxor z15 ef = y7 := by decide

theorem sign_zA : SS.bdot ez z8 = false := by decide
theorem sign_zB : SS.bdot ez z15 = true := by decide
theorem sign0_zA : SS.bdot (fun _ => false) z8 = false := by decide
theorem sign0_zB : SS.bdot (fun _ => false) z15 = false := by decide

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
  m5 : q1 + q2 + q4 + q7 + q8 + q11 + q13 + q14 = r0 + r3 + r5 + r6 + r9 + r10 + r12 + r15
  m6 : q1 + q2 + q3 + q4 + q5 + q6 + q8 + q9 + q10 + q12 = r3 + r5 + r6 + r7 + r9 + r10 + r11 + r12 + r13 + r14
  c12 : q12 + q13 + q14 + q15 = r12 + r13 + r14 + r15
  c13 : q10 + q11 + q14 + q15 = r10 + r11 + r14 + r15
  c14 : q9 + q11 + q13 + q15 = r9 + r11 + r13 + r15
  c15 : q8 + q11 + q13 + q14 = r9 + r10 + r12 + r15
  c16 : q8 + q9 + q10 + q12 = r9 + r10 + r11 + r12 + r13 + r14
  c23 : q6 + q7 + q14 + q15 = r6 + r7 + r14 + r15
  c24 : q5 + q7 + q13 + q15 = r5 + r7 + r13 + r15
  c25 : q4 + q7 + q13 + q14 = r5 + r6 + r12 + r15
  c26 : q4 + q5 + q6 + q12 = r5 + r6 + r7 + r12 + r13 + r14
  c34 : q3 + q7 + q11 + q15 = r3 + r7 + r11 + r15
  c35 : q2 + q7 + q11 + q14 = r3 + r6 + r10 + r15
  c36 : q2 + q3 + q6 + q10 = r3 + r6 + r7 + r10 + r11 + r14
  c45 : q1 + q7 + q11 + q13 = r3 + r5 + r9 + r15
  c46 : q1 + q3 + q5 + q9 = r3 + r5 + r7 + r9 + r11 + r13
  c56 : q1 + q2 + q4 + q8 = r3 + r5 + r6 + r9 + r10 + r12

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

/-- The probabilities at the 6 spurious incidences vanish. -/
theorem MomentSystem.spurious_zero {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real}
    (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    r9 = 0 ∧ r10 = 0 ∧ r11 = 0 ∧ r12 = 0 ∧ r13 = 0 ∧ r14 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- The four surviving endpoint probabilities are forced, hence positive. -/
theorem MomentSystem.endpoints {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real}
    (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    q0 = 3/8 ∧ q7 = 1/8 ∧ r8 = 1/8 ∧ r15 = 3/8 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nq12, nq13, nq14, nq15, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11, nr12, nr13, nr14, nr15⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem MomentSystem.endpoints_pos {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Real}
    (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) :
    0 < q0 ∧ 0 < q7 ∧ 0 < r8 ∧ 0 < r15 := by
  obtain ⟨e1, e2, e3, e4⟩ := h.endpoints
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp_all

/-! ## Collapsing the incidence sum to the two live edges -/

def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),
      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

theorem signMul_zero (b : Bool) : SixQubit.signMul b (0 : ℂ) = 0 := by
  cases b <;> simp [SixQubit.signMul]

def A (c d : SS.BitString 6 -> ℂ) : ℂ := star (c y0) * d z8
def B (c d : SS.BitString 6 -> ℂ) : ℂ := star (c y7) * d z15

theorem offSum_reduce (c d : SS.BitString 6 -> ℂ) (zz : SS.BitString 6)
    (hd9 : d z9 = 0)
    (hd10 : d z10 = 0)
    (hd11 : d z11 = 0)
    (hd12 : d z12 = 0)
    (hd13 : d z13 = 0)
    (hd14 : d z14 = 0)
    : offSum c d ef zz
      = SixQubit.signMul (SS.bdot zz z8) (A c d)
        + SixQubit.signMul (SS.bdot zz z15) (B c d) := by
  unfold offSum
  rw [incidence]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_z8, flip_z9, flip_z10, flip_z11, flip_z12, flip_z13, flip_z14, flip_z15]
  rw [hd9, hd10, hd11, hd12, hd13, hd14]
  simp [A, B, signMul_zero]

theorem offSum_flip (c d : SS.BitString 6 -> ℂ)
    (hd9 : d z9 = 0)
    (hd10 : d z10 = 0)
    (hd11 : d z11 = 0)
    (hd12 : d z12 = 0)
    (hd13 : d z13 = 0)
    (hd14 : d z14 = 0)
    : offSum c d ef (fun _ => false) = A c d + B c d := by
  rw [offSum_reduce c d _ hd9 hd10 hd11 hd12 hd13 hd14, sign0_zA, sign0_zB]
  simp

theorem offSum_flipZ (c d : SS.BitString 6 -> ℂ)
    (hd9 : d z9 = 0)
    (hd10 : d z10 = 0)
    (hd11 : d z11 = 0)
    (hd12 : d z12 = 0)
    (hd13 : d z13 = 0)
    (hd14 : d z14 = 0)
    : offSum c d ef ez = A c d - B c d := by
  rw [offSum_reduce c d _ hd9 hd10 hd11 hd12 hd13 hd14, sign_zA, sign_zB]
  simp
  ring

/-! ## The no-go -/

theorem two_edge {u v : ℂ} (h1 : u + v = 0) (h2 : u - v = 0) : u = 0 ∧ v = 0 := by
  constructor
  · linear_combination (h1 + h2) / 2
  · linear_combination (h1 - h2) / 2

/-- **Orbit 28 is impossible.** -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11)) (Complex.normSq (c y12)) (Complex.normSq (c y13)) (Complex.normSq (c y14)) (Complex.normSq (c y15))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)) (Complex.normSq (d z12)) (Complex.normSq (d z13)) (Complex.normSq (d z14)) (Complex.normSq (d z15)))
    (hf : offSum c d ef (fun _ => false) = 0)
    (hfz : offSum c d ef ez = 0) : False := by
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := hm.spurious_zero
  have hz0 : d z9 = 0 := Complex.normSq_eq_zero.mp s0
  have hz1 : d z10 = 0 := Complex.normSq_eq_zero.mp s1
  have hz2 : d z11 = 0 := Complex.normSq_eq_zero.mp s2
  have hz3 : d z12 = 0 := Complex.normSq_eq_zero.mp s3
  have hz4 : d z13 = 0 := Complex.normSq_eq_zero.mp s4
  have hz5 : d z14 = 0 := Complex.normSq_eq_zero.mp s5
  obtain ⟨hqA, hqB, hrA, hrB⟩ := hm.endpoints_pos
  rw [offSum_flip c d hz0 hz1 hz2 hz3 hz4 hz5] at hf
  rw [offSum_flipZ c d hz0 hz1 hz2 hz3 hz4 hz5] at hfz
  have hA := (two_edge hf hfz).1
  unfold A at hA
  rcases mul_eq_zero.mp hA with h | h
  · rw [show c y0 = 0 from by simpa using congrArg star h] at hqA; simp at hqA
  · rw [h] at hrA; simp at hrA

end

end SixQubit.Orbit28
