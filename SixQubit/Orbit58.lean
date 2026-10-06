import Mathlib

import SS.FullKL
import SixQubit.Common

/-!
# Six-qubit no-go for moment orbit 58

Orbit 58 of `six_qubit_sslp_v7.tex`: q = 7, angle vector
a = (1, 1, 2, 3, 3, 5), residues 0 and 1, closed in Section 13.

Two one-dimensional Walsh kernels give quadratic identities which, reduced
against the moment system, collapse the polytope to a single point; every
amplitude is then nonzero.  Four further flips have exactly two incidences
each, and each such equation is a phase-ratio link.  Chaining two links is a
genuinely transitive step, invisible at the level of individual products, but
division-free all the same: the difference of the two products, multiplied by
a third nonzero product, vanishes by `linear_combination`.

With the two chained links the four-term equation of the flip 000110 collapses
to a two-term relation, and that relation closes a length-three odd cycle
against the two kernels.

Everything computational is decided by the Lean kernel; `native_decide` is
not used.
-/

namespace SixQubit.Orbit58

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]

def y0 : SS.BitString 6 := bs false false false false false false  -- 000000
def y1 : SS.BitString 6 := bs false false true  false false true   -- 001001
def y2 : SS.BitString 6 := bs false true  false true  true  false  -- 010110
def y3 : SS.BitString 6 := bs false true  true  true  true  true   -- 011111
def y4 : SS.BitString 6 := bs true  false false true  true  false  -- 100110
def y5 : SS.BitString 6 := bs true  false true  true  true  true   -- 101111
def y6 : SS.BitString 6 := bs true  true  false false false true   -- 110001
def y7 : SS.BitString 6 := bs true  true  true  false true  false  -- 111010
def y8 : SS.BitString 6 := bs true  true  true  true  false false  -- 111100

def z0 : SS.BitString 6 := bs false false false false true  true   -- 000011
def z1 : SS.BitString 6 := bs false false false true  false true   -- 000101
def z2 : SS.BitString 6 := bs false false true  true  true  false  -- 001110
def z3 : SS.BitString 6 := bs false true  false false false false  -- 010000
def z4 : SS.BitString 6 := bs false true  true  false false true   -- 011001
def z5 : SS.BitString 6 := bs true  false false false false false  -- 100000
def z6 : SS.BitString 6 := bs true  false true  false false true   -- 101001
def z7 : SS.BitString 6 := bs true  true  false true  true  false  -- 110110
def z8 : SS.BitString 6 := bs true  true  true  true  true  true   -- 111111

def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6, y7, y8}
def S1 : Finset (SS.BitString 6) := {z0, z1, z2, z3, z4, z5, z6, z7, z8}

def av : Fin 6 -> ZMod 7 := ![1, 1, 2, 3, 3, 5]

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
/-- Flip 2: mask 100001. -/
def ef2 : SS.BitString 6 := bs true  false false false false true 
/-- Flip 3: mask 011000. -/
def ef3 : SS.BitString 6 := bs false true  true  false false false
/-- Flip 4: mask 101000. -/
def ef4 : SS.BitString 6 := bs true  false true  false false false
/-- Flip 5: mask 010001. -/
def ef5 : SS.BitString 6 := bs false true  false false false true 
/-- Flip 6: mask 000110. -/
def ef6 : SS.BitString 6 := bs false false false true  true  false
def w0 : SS.BitString 6 := bs false false false false false false  -- dressing 000000
def wx1 : SS.BitString 6 := bs false false true  false false false  -- dressing 001000
def wx2 : SS.BitString 6 := bs false true  false false false false  -- dressing 010000
def wx3 : SS.BitString 6 := bs true  false false false false false  -- dressing 100000

theorem incidence0 :
    S1.filter (fun y => SS.bxor y ef0 ∈ S0) = {z5, z6, z7, z8} := by decide
theorem fl0_5 : SS.bxor z5 ef0 = y0 := by decide
theorem fl0_6 : SS.bxor z6 ef0 = y1 := by decide
theorem fl0_7 : SS.bxor z7 ef0 = y2 := by decide
theorem fl0_8 : SS.bxor z8 ef0 = y3 := by decide
theorem sg0_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg0_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg0_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg0_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg0_wx1_5 : SS.bdot wx1 z5 = false := by decide
theorem sg0_wx1_6 : SS.bdot wx1 z6 = true := by decide
theorem sg0_wx1_7 : SS.bdot wx1 z7 = false := by decide
theorem sg0_wx1_8 : SS.bdot wx1 z8 = true := by decide
theorem sg0_wx2_5 : SS.bdot wx2 z5 = false := by decide
theorem sg0_wx2_6 : SS.bdot wx2 z6 = false := by decide
theorem sg0_wx2_7 : SS.bdot wx2 z7 = true := by decide
theorem sg0_wx2_8 : SS.bdot wx2 z8 = true := by decide
theorem incidence1 :
    S1.filter (fun y => SS.bxor y ef1 ∈ S0) = {z3, z4, z7, z8} := by decide
theorem fl1_3 : SS.bxor z3 ef1 = y0 := by decide
theorem fl1_4 : SS.bxor z4 ef1 = y1 := by decide
theorem fl1_7 : SS.bxor z7 ef1 = y4 := by decide
theorem fl1_8 : SS.bxor z8 ef1 = y5 := by decide
theorem sg1_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg1_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg1_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg1_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg1_wx1_3 : SS.bdot wx1 z3 = false := by decide
theorem sg1_wx1_4 : SS.bdot wx1 z4 = true := by decide
theorem sg1_wx1_7 : SS.bdot wx1 z7 = false := by decide
theorem sg1_wx1_8 : SS.bdot wx1 z8 = true := by decide
theorem sg1_wx3_3 : SS.bdot wx3 z3 = false := by decide
theorem sg1_wx3_4 : SS.bdot wx3 z4 = false := by decide
theorem sg1_wx3_7 : SS.bdot wx3 z7 = true := by decide
theorem sg1_wx3_8 : SS.bdot wx3 z8 = true := by decide
theorem incidence2 :
    S1.filter (fun y => SS.bxor y ef2 ∈ S0) = {z2, z3} := by decide
theorem fl2_2 : SS.bxor z2 ef2 = y5 := by decide
theorem fl2_3 : SS.bxor z3 ef2 = y6 := by decide
theorem sg2_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg2_w0_3 : SS.bdot w0 z3 = false := by decide
theorem incidence3 :
    S1.filter (fun y => SS.bxor y ef3 ∈ S0) = {z2, z6} := by decide
theorem fl3_2 : SS.bxor z2 ef3 = y2 := by decide
theorem fl3_6 : SS.bxor z6 ef3 = y6 := by decide
theorem sg3_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg3_w0_6 : SS.bdot w0 z6 = false := by decide
theorem incidence4 :
    S1.filter (fun y => SS.bxor y ef4 ∈ S0) = {z2, z4} := by decide
theorem fl4_2 : SS.bxor z2 ef4 = y4 := by decide
theorem fl4_4 : SS.bxor z4 ef4 = y6 := by decide
theorem sg4_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg4_w0_4 : SS.bdot w0 z4 = false := by decide
theorem incidence5 :
    S1.filter (fun y => SS.bxor y ef5 ∈ S0) = {z2, z5} := by decide
theorem fl5_2 : SS.bxor z2 ef5 = y3 := by decide
theorem fl5_5 : SS.bxor z5 ef5 = y6 := by decide
theorem sg5_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg5_w0_5 : SS.bdot w0 z5 = false := by decide
theorem incidence6 :
    S1.filter (fun y => SS.bxor y ef6 ∈ S0) = {z3, z4, z5, z6} := by decide
theorem fl6_3 : SS.bxor z3 ef6 = y2 := by decide
theorem fl6_4 : SS.bxor z4 ef6 = y3 := by decide
theorem fl6_5 : SS.bxor z5 ef6 = y4 := by decide
theorem fl6_6 : SS.bxor z6 ef6 = y5 := by decide
theorem sg6_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg6_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg6_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg6_w0_6 : SS.bdot w0 z6 = false := by decide

/-! ## The moment system -/

/-- The two normalizations, the twenty-one moment equalities, and the
nonnegativity of every probability. -/
structure MomentSystem (q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8 : Real) : Prop where
  n0 : q0 + q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 = 1
  n1 : r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 = 1
  m1 : q4 + q5 + q6 + q7 + q8 = r5 + r6 + r7 + r8
  m2 : q2 + q3 + q6 + q7 + q8 = r3 + r4 + r7 + r8
  m3 : q1 + q3 + q5 + q7 + q8 = r2 + r4 + r6 + r8
  m4 : q2 + q3 + q4 + q5 + q8 = r1 + r2 + r7 + r8
  m5 : q2 + q3 + q4 + q5 + q7 = r0 + r2 + r7 + r8
  m6 : q1 + q3 + q5 + q6 = r0 + r1 + r4 + r6 + r8
  c12 : q6 + q7 + q8 = r7 + r8
  c13 : q5 + q7 + q8 = r6 + r8
  c14 : q4 + q5 + q8 = r7 + r8
  c15 : q4 + q5 + q7 = r7 + r8
  c16 : q5 + q6 = r6 + r8
  c23 : q3 + q7 + q8 = r4 + r8
  c24 : q2 + q3 + q8 = r7 + r8
  c25 : q2 + q3 + q7 = r7 + r8
  c26 : q3 + q6 = r4 + r8
  c34 : q3 + q5 + q8 = r2 + r8
  c35 : q3 + q5 + q7 = r2 + r8
  c36 : q1 + q3 + q5 = r4 + r6 + r8
  c45 : q2 + q3 + q4 + q5 = r2 + r7 + r8
  c46 : q3 + q5 = r1 + r8
  c56 : q3 + q5 = r0 + r8

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

/-! ## The Walsh systems -/

def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),
      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

theorem ex0_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w0 = star (c y0) * d z5 + star (c y1) * d z6 + star (c y2) * d z7 + star (c y3) * d z8 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_5, fl0_6, fl0_7, fl0_8]
  simp only [sg0_w0_5, sg0_w0_6, sg0_w0_7, sg0_w0_8, SixQubit.signMul_false]
  try ring

theorem ex0_wx1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 wx1 = star (c y0) * d z5 - star (c y1) * d z6 + star (c y2) * d z7 - star (c y3) * d z8 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_5, fl0_6, fl0_7, fl0_8]
  simp only [sg0_wx1_5, sg0_wx1_6, sg0_wx1_7, sg0_wx1_8, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex0_wx2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 wx2 = star (c y0) * d z5 + star (c y1) * d z6 - star (c y2) * d z7 - star (c y3) * d z8 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_5, fl0_6, fl0_7, fl0_8]
  simp only [sg0_wx2_5, sg0_wx2_6, sg0_wx2_7, sg0_wx2_8, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex1_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w0 = star (c y0) * d z3 + star (c y1) * d z4 + star (c y4) * d z7 + star (c y5) * d z8 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_3, fl1_4, fl1_7, fl1_8]
  simp only [sg1_w0_3, sg1_w0_4, sg1_w0_7, sg1_w0_8, SixQubit.signMul_false]
  try ring

theorem ex1_wx1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 wx1 = star (c y0) * d z3 - star (c y1) * d z4 + star (c y4) * d z7 - star (c y5) * d z8 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_3, fl1_4, fl1_7, fl1_8]
  simp only [sg1_wx1_3, sg1_wx1_4, sg1_wx1_7, sg1_wx1_8, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex1_wx3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 wx3 = star (c y0) * d z3 + star (c y1) * d z4 - star (c y4) * d z7 - star (c y5) * d z8 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_3, fl1_4, fl1_7, fl1_8]
  simp only [sg1_wx3_3, sg1_wx3_4, sg1_wx3_7, sg1_wx3_8, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex2_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w0 = star (c y5) * d z2 + star (c y6) * d z3 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_2, fl2_3]
  simp only [sg2_w0_2, sg2_w0_3, SixQubit.signMul_false]
  try ring

theorem ex3_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w0 = star (c y2) * d z2 + star (c y6) * d z6 := by
  unfold offSum
  rw [incidence3]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl3_2, fl3_6]
  simp only [sg3_w0_2, sg3_w0_6, SixQubit.signMul_false]
  try ring

theorem ex4_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w0 = star (c y4) * d z2 + star (c y6) * d z4 := by
  unfold offSum
  rw [incidence4]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl4_2, fl4_4]
  simp only [sg4_w0_2, sg4_w0_4, SixQubit.signMul_false]
  try ring

theorem ex5_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef5 w0 = star (c y3) * d z2 + star (c y6) * d z5 := by
  unfold offSum
  rw [incidence5]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl5_2, fl5_5]
  simp only [sg5_w0_2, sg5_w0_5, SixQubit.signMul_false]
  try ring

theorem ex6_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w0 = star (c y2) * d z3 + star (c y3) * d z4 + star (c y4) * d z5 + star (c y5) * d z6 := by
  unfold offSum
  rw [incidence6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl6_3, fl6_4, fl6_5, fl6_6]
  simp only [sg6_w0_3, sg6_w0_4, sg6_w0_5, sg6_w0_6, SixQubit.signMul_false]
  try ring

/-! ## The two kernels and the quadratic closure -/

/-- The one-dimensional kernel of flip 100000, at the cycle pair. -/
theorem kr0 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef0 w0 = 0)
    (h1 : offSum c d ef0 wx1 = 0)
    : star (c y0) * d z5 + star (c y2) * d z7 = 0 := by
  rw [ex0_w0] at h0
  rw [ex0_wx1] at h1
  linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- The one-dimensional kernel of flip 010000, at the cycle pair. -/
theorem kr1 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef1 w0 = 0)
    (h1 : offSum c d ef1 wx1 = 0)
    : star (c y0) * d z3 + star (c y4) * d z7 = 0 := by
  rw [ex1_w0] at h0
  rw [ex1_wx1] at h1
  linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- The kernel pair carrying quadratic identity 0. -/
theorem qr0 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef0 w0 = 0)
    (h1 : offSum c d ef0 wx2 = 0)
    : star (c y2) * d z7 + star (c y3) * d z8 = 0 := by
  rw [ex0_w0] at h0
  rw [ex0_wx2] at h1
  linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1

/-- Its squared-modulus consequence. -/
theorem qm0 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef0 w0 = 0)
    (h1 : offSum c d ef0 wx2 = 0)
    : Complex.normSq (c y2) * Complex.normSq (d z7)
      = Complex.normSq (c y3) * Complex.normSq (d z8) := by
  have hr := qr0 c d h0 h1
  have he : star (c y2) * d z7 = -(star (c y3) * d z8) := by linear_combination hr
  simpa [Complex.normSq_mul] using congrArg Complex.normSq he

/-- Quadratic identity 0, reduced against the moment system. -/
theorem lin0 {q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8)
    (hq : q2 * r7 = q3 * r8) :
    2*r6/7 - 3*r8/14 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8⟩ := h
  linear_combination hq + (-2*r6/7 + 3*r8/14) * n1 + (-2*r6/7 + 3*r8/14) * m1 + (-2*r6/7 + 3*r8/14) * m2 + (-r6/7 - r8/7) * c12 + (8*r6/7 + r7 + r8/7) * c15 + (-r7 - r8) * c16 + (-5*r6/7 - r7 - 5*r8/7) * c23 + (8*r6/7 + r8/7) * c25 + (5*r6/7 + r7 + 5*r8/7) * c26 + (10*r6/7 + r7 + 3*r8/7) * c34 + (-6*r6/7 + r8/7) * c35 + (-6*r6/7 - r7 - 5*r8/14) * c45 + (-2*r6/7 + 3*r8/14) * c46 + (-2*r6/7 + 3*r8/14) * c56

/-- The kernel pair carrying quadratic identity 1. -/
theorem qr1 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef1 w0 = 0)
    (h1 : offSum c d ef1 wx3 = 0)
    : star (c y4) * d z7 + star (c y5) * d z8 = 0 := by
  rw [ex1_w0] at h0
  rw [ex1_wx3] at h1
  linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1

/-- Its squared-modulus consequence. -/
theorem qm1 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef1 w0 = 0)
    (h1 : offSum c d ef1 wx3 = 0)
    : Complex.normSq (c y4) * Complex.normSq (d z7)
      = Complex.normSq (c y5) * Complex.normSq (d z8) := by
  have hr := qr1 c d h0 h1
  have he : star (c y4) * d z7 = -(star (c y5) * d z8) := by linear_combination hr
  simpa [Complex.normSq_mul] using congrArg Complex.normSq he

/-- Quadratic identity 1, reduced against the moment system. -/
theorem lin1 {q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8)
    (hq : q4 * r7 = q5 * r8) :
    -2*r6/7 - r8/2 + 5/49 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8⟩ := h
  linear_combination hq + (2*r6/7 - 5*r7/14 + r8/7 - 5/49) * n1 + (2*r6/7 - 5*r7/14 + r8/7 - 5/49) * m1 + (2*r6/7 - 5*r7/14 + r8/7 - 5/49) * m2 + (r6/7 - 3*r7/7 - 3*r8/7 - 5/98) * c12 + (-8*r6/7 + 3*r7/7 - 4*r8/7 + 20/49) * c15 + (r7 + r8) * c16 + (5*r6/7 - r7/7 + 6*r8/7 - 25/98) * c23 + (-8*r6/7 + 10*r7/7 - 4*r8/7 + 20/49) * c25 + (-5*r6/7 + r7/7 - 6*r8/7 + 25/98) * c26 + (-10*r6/7 + 9*r7/7 - 5*r8/7 + 25/49) * c34 + (6*r6/7 - 4*r7/7 + 3*r8/7 - 15/49) * c35 + (6*r6/7 - 15*r7/14 + 3*r8/7 - 15/49) * c45 + (2*r6/7 - 5*r7/14 + r8/7 - 5/49) * c46 + (2*r6/7 - 5*r7/14 + r8/7 - 5/49) * c56

/-- The closure pins every probability the argument uses. -/
theorem pinned {q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8)
    (v0 : 2*r6/7 - 3*r8/14 = 0)
    (v1 : -2*r6/7 - r8/2 + 5/49 = 0)
    : q0 = 1/7 ∧ q2 = 3/28 ∧ q4 = 3/28 ∧ q6 = 1/7 ∧ r2 = 1/7 ∧ r3 = 3/28 ∧ r5 = 3/28 ∧ r7 = 1/7 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-! ## Phase-ratio links and their transitivity -/

/-- Flip 100001 has exactly two incidences. -/
theorem lk0 (c d : SS.BitString 6 -> ℂ) (h : offSum c d ef2 w0 = 0)
    : star (c y5) * d z2 + star (c y6) * d z3 = 0 := by
  rw [ex2_w0] at h
  linear_combination h

/-- Flip 011000 has exactly two incidences. -/
theorem lk1 (c d : SS.BitString 6 -> ℂ) (h : offSum c d ef3 w0 = 0)
    : star (c y2) * d z2 + star (c y6) * d z6 = 0 := by
  rw [ex3_w0] at h
  linear_combination h

/-- Flip 101000 has exactly two incidences. -/
theorem lk2 (c d : SS.BitString 6 -> ℂ) (h : offSum c d ef4 w0 = 0)
    : star (c y4) * d z2 + star (c y6) * d z4 = 0 := by
  rw [ex4_w0] at h
  linear_combination h

/-- Flip 010001 has exactly two incidences. -/
theorem lk3 (c d : SS.BitString 6 -> ℂ) (h : offSum c d ef5 w0 = 0)
    : star (c y3) * d z2 + star (c y6) * d z5 = 0 := by
  rw [ex5_w0] at h
  linear_combination h

/-- Transitivity of two phase-ratio links, division-free. -/
theorem tr0 (c d : SS.BitString 6 -> ℂ)
    (h1 : star (c y5) * d z2 + star (c y6) * d z3 = 0)
    (h2 : star (c y2) * d z2 + star (c y6) * d z6 = 0)
    (hm : star (c y6) * d z2 ≠ 0)
    : star (c y2) * d z3 = star (c y5) * d z6 := by
  have key : (star (c y2) * d z3 - star (c y5) * d z6) * (star (c y6) * d z2) = 0 := by
    linear_combination (star (c y2) * d z2) * h1 - (star (c y5) * d z2) * h2
  rcases mul_eq_zero.mp key with h | h
  · linear_combination h
  · exact absurd h hm

/-- Transitivity of two phase-ratio links, division-free. -/
theorem tr1 (c d : SS.BitString 6 -> ℂ)
    (h1 : star (c y4) * d z2 + star (c y6) * d z4 = 0)
    (h2 : star (c y3) * d z2 + star (c y6) * d z5 = 0)
    (hm : star (c y6) * d z2 ≠ 0)
    : star (c y3) * d z4 = star (c y4) * d z5 := by
  have key : (star (c y3) * d z4 - star (c y4) * d z5) * (star (c y6) * d z2) = 0 := by
    linear_combination (star (c y3) * d z2) * h1 - (star (c y4) * d z2) * h2
  rcases mul_eq_zero.mp key with h | h
  · linear_combination h
  · exact absurd h hm

/-- With both links chained, the four-term equation collapses. -/
theorem collapse (c d : SS.BitString 6 -> ℂ)
    (h : offSum c d ef6 w0 = 0)
    (e1 : star (c y2) * d z3 = star (c y5) * d z6)
    (e2 : star (c y3) * d z4 = star (c y4) * d z5)
    : star (c y2) * d z3 + star (c y4) * d z5 = 0 := by
  rw [ex6_w0] at h
  linear_combination h / 2 + e1 / 2 - e2 / 2

/-! ## The odd cycle -/

/-- **Orbit 58 is impossible.** -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)))
    (E0_w0 : offSum c d ef0 w0 = 0)
    (E0_wx1 : offSum c d ef0 wx1 = 0)
    (E0_wx2 : offSum c d ef0 wx2 = 0)
    (E1_w0 : offSum c d ef1 w0 = 0)
    (E1_wx1 : offSum c d ef1 wx1 = 0)
    (E1_wx3 : offSum c d ef1 wx3 = 0)
    (E2_w0 : offSum c d ef2 w0 = 0)
    (E3_w0 : offSum c d ef3 w0 = 0)
    (E4_w0 : offSum c d ef4 w0 = 0)
    (E5_w0 : offSum c d ef5 w0 = 0)
    (E6_w0 : offSum c d ef6 w0 = 0)
    : False := by
  have v0 := lin0 hm (qm0 c d E0_w0 E0_wx2)
  have v1 := lin1 hm (qm1 c d E1_w0 E1_wx3)
  obtain ⟨p0, p2, p4, p6, p11, p12, p14, p16⟩ := pinned hm v0 v1
  have n0 : c y0 ≠ 0 := fun hz => by rw [hz] at p0; norm_num at p0
  have n2 : c y2 ≠ 0 := fun hz => by rw [hz] at p2; norm_num at p2
  have n4 : c y4 ≠ 0 := fun hz => by rw [hz] at p4; norm_num at p4
  have n6 : c y6 ≠ 0 := fun hz => by rw [hz] at p6; norm_num at p6
  have n11 : d z2 ≠ 0 := fun hz => by rw [hz] at p11; norm_num at p11
  have n12 : d z3 ≠ 0 := fun hz => by rw [hz] at p12; norm_num at p12
  have n14 : d z5 ≠ 0 := fun hz => by rw [hz] at p14; norm_num at p14
  have n16 : d z7 ≠ 0 := fun hz => by rw [hz] at p16; norm_num at p16
  have hmul : star (c y6) * d z2 ≠ 0 := by
    exact mul_ne_zero (star_ne_zero.mpr n6) n11
  have K0 := lk0 c d E2_w0
  have K1 := lk1 c d E3_w0
  have K2 := lk2 c d E4_w0
  have K3 := lk3 c d E5_w0
  have T0 := tr0 c d K0 K1 hmul
  have T1 := tr1 c d K2 K3 hmul
  have C := collapse c d E6_w0 T0 T1
  have R0 := kr0 c d E0_w0 E0_wx1
  have R1 := kr1 c d E1_w0 E1_wx1
  have key : (2 : ℂ) * ((star (c y0) * d z5) * (star (c y4) * d z7) * (star (c y2) * d z3)) = 0 := by
    linear_combination ((star (c y4) * d z7) * (star (c y2) * d z3)) * R0 - ((star (c y2) * d z7) * (star (c y2) * d z3)) * R1 + ((star (c y2) * d z7) * (star (c y0) * d z3)) * C
  have hz : ((star (c y0) * d z5) * (star (c y4) * d z7) * (star (c y2) * d z3)) = 0 := by linear_combination key / 2
  simp [n0, n2, n4, n12, n14, n16] at hz

end

end SixQubit.Orbit58
