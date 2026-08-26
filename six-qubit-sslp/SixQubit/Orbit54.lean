import Mathlib

import SS.FullKL
import SixQubit.Common

/-!
# Six-qubit no-go for moment orbit 54

Orbit 54 of `six_qubit_sslp_v7.tex`: q = 6, angle vector
a = (1, 1, 2, 2, 2, 5), residues 0 and 1, closed in Section 14.

The moment polytope of this orbit forces no probability to be positive, so
none of the earlier certificates applies.  What closes it is that each of
the 3 flips below has a one-dimensional Walsh kernel.  A one-dimensional
kernel pins its products to a single scalar, which gives simultaneously

* an antisymmetric two-term relation between two products, and
* after taking squared moduli, a quadratic identity between probabilities.

The quadratic identities collapse the polytope to a single point at which
every probability is an explicit positive rational; the two-term relations
then close an odd cancellation cycle, forcing a product of six nonzero
amplitudes to vanish.

Everything computational is decided by the Lean kernel; `native_decide` is
not used.
-/

namespace SixQubit.Orbit54

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]

def y0 : SS.BitString 6 := bs false false false false false false  -- 000000
def y1 : SS.BitString 6 := bs false false true  true  true  false  -- 001110
def y2 : SS.BitString 6 := bs false true  false false false true   -- 010001
def y3 : SS.BitString 6 := bs false true  true  true  true  true   -- 011111
def y4 : SS.BitString 6 := bs true  false false false false true   -- 100001
def y5 : SS.BitString 6 := bs true  false true  true  true  true   -- 101111
def y6 : SS.BitString 6 := bs true  true  false true  true  false  -- 110110
def y7 : SS.BitString 6 := bs true  true  true  false true  false  -- 111010
def y8 : SS.BitString 6 := bs true  true  true  true  false false  -- 111100

def z0 : SS.BitString 6 := bs false false false false true  true   -- 000011
def z1 : SS.BitString 6 := bs false false false true  false true   -- 000101
def z2 : SS.BitString 6 := bs false false true  false false true   -- 001001
def z3 : SS.BitString 6 := bs false true  false false false false  -- 010000
def z4 : SS.BitString 6 := bs false true  true  true  true  false  -- 011110
def z5 : SS.BitString 6 := bs true  false false false false false  -- 100000
def z6 : SS.BitString 6 := bs true  false true  true  true  false  -- 101110
def z7 : SS.BitString 6 := bs true  true  false false false true   -- 110001
def z8 : SS.BitString 6 := bs true  true  true  true  true  true   -- 111111

def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6, y7, y8}
def S1 : Finset (SS.BitString 6) := {z0, z1, z2, z3, z4, z5, z6, z7, z8}

def av : Fin 6 -> ZMod 6 := ![1, 1, 2, 2, 2, 5]

/-- Each support is exactly its residue fiber, decided over all 64 strings. -/
theorem S0_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 0) = S0 := by
  decide

theorem S1_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 1) = S1 := by
  decide

/-! ## The three flips and their dressings -/

/-- Flip 0: mask 100000. -/
def ef0 : SS.BitString 6 := bs true  false false false false false
def w0_0 : SS.BitString 6 := bs false false false false false false  -- dressing 000000
def w0_1 : SS.BitString 6 := bs false false true  false false false  -- dressing 001000
/-- Flip 1: mask 010000. -/
def ef1 : SS.BitString 6 := bs false true  false false false false
def w1_0 : SS.BitString 6 := bs false false false false false false  -- dressing 000000
def w1_1 : SS.BitString 6 := bs false false true  false false false  -- dressing 001000
/-- Flip 2: mask 000001. -/
def ef2 : SS.BitString 6 := bs false false false false false true 
def w2_0 : SS.BitString 6 := bs false false false false false false  -- dressing 000000
def w2_1 : SS.BitString 6 := bs false false true  false false false  -- dressing 001000

theorem incidence0 :
    S1.filter (fun y => SS.bxor y ef0 ∈ S0) = {z5, z6, z7, z8} := by decide
theorem fl0_5 : SS.bxor z5 ef0 = y0 := by decide
theorem fl0_6 : SS.bxor z6 ef0 = y1 := by decide
theorem fl0_7 : SS.bxor z7 ef0 = y2 := by decide
theorem fl0_8 : SS.bxor z8 ef0 = y3 := by decide
theorem sg0_0_5 : SS.bdot w0_0 z5 = false := by decide
theorem sg0_0_6 : SS.bdot w0_0 z6 = false := by decide
theorem sg0_0_7 : SS.bdot w0_0 z7 = false := by decide
theorem sg0_0_8 : SS.bdot w0_0 z8 = false := by decide
theorem sg0_1_5 : SS.bdot w0_1 z5 = false := by decide
theorem sg0_1_6 : SS.bdot w0_1 z6 = true := by decide
theorem sg0_1_7 : SS.bdot w0_1 z7 = false := by decide
theorem sg0_1_8 : SS.bdot w0_1 z8 = true := by decide

theorem incidence1 :
    S1.filter (fun y => SS.bxor y ef1 ∈ S0) = {z3, z4, z7, z8} := by decide
theorem fl1_3 : SS.bxor z3 ef1 = y0 := by decide
theorem fl1_4 : SS.bxor z4 ef1 = y1 := by decide
theorem fl1_7 : SS.bxor z7 ef1 = y4 := by decide
theorem fl1_8 : SS.bxor z8 ef1 = y5 := by decide
theorem sg1_0_3 : SS.bdot w1_0 z3 = false := by decide
theorem sg1_0_4 : SS.bdot w1_0 z4 = false := by decide
theorem sg1_0_7 : SS.bdot w1_0 z7 = false := by decide
theorem sg1_0_8 : SS.bdot w1_0 z8 = false := by decide
theorem sg1_1_3 : SS.bdot w1_1 z3 = false := by decide
theorem sg1_1_4 : SS.bdot w1_1 z4 = true := by decide
theorem sg1_1_7 : SS.bdot w1_1 z7 = false := by decide
theorem sg1_1_8 : SS.bdot w1_1 z8 = true := by decide

theorem incidence2 :
    S1.filter (fun y => SS.bxor y ef2 ∈ S0) = {z3, z4, z5, z6} := by decide
theorem fl2_3 : SS.bxor z3 ef2 = y2 := by decide
theorem fl2_4 : SS.bxor z4 ef2 = y3 := by decide
theorem fl2_5 : SS.bxor z5 ef2 = y4 := by decide
theorem fl2_6 : SS.bxor z6 ef2 = y5 := by decide
theorem sg2_0_3 : SS.bdot w2_0 z3 = false := by decide
theorem sg2_0_4 : SS.bdot w2_0 z4 = false := by decide
theorem sg2_0_5 : SS.bdot w2_0 z5 = false := by decide
theorem sg2_0_6 : SS.bdot w2_0 z6 = false := by decide
theorem sg2_1_3 : SS.bdot w2_1 z3 = false := by decide
theorem sg2_1_4 : SS.bdot w2_1 z4 = true := by decide
theorem sg2_1_5 : SS.bdot w2_1 z5 = false := by decide
theorem sg2_1_6 : SS.bdot w2_1 z6 = true := by decide

/-! ## The moment system -/

/-- The two normalizations, the twenty-one moment equalities, and the
nonnegativity of every probability. -/
structure MomentSystem (q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8 : Real) : Prop where
  n0 : q0 + q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 = 1
  n1 : r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 = 1
  m1 : q4 + q5 + q6 + q7 + q8 = r5 + r6 + r7 + r8
  m2 : q2 + q3 + q6 + q7 + q8 = r3 + r4 + r7 + r8
  m3 : q1 + q3 + q5 + q7 + q8 = r2 + r4 + r6 + r8
  m4 : q1 + q3 + q5 + q6 + q8 = r1 + r4 + r6 + r8
  m5 : q1 + q3 + q5 + q6 + q7 = r0 + r4 + r6 + r8
  m6 : q2 + q3 + q4 + q5 = r0 + r1 + r2 + r7 + r8
  c12 : q6 + q7 + q8 = r7 + r8
  c13 : q5 + q7 + q8 = r6 + r8
  c14 : q5 + q6 + q8 = r6 + r8
  c15 : q5 + q6 + q7 = r6 + r8
  c16 : q4 + q5 = r7 + r8
  c23 : q3 + q7 + q8 = r4 + r8
  c24 : q3 + q6 + q8 = r4 + r8
  c25 : q3 + q6 + q7 = r4 + r8
  c26 : q2 + q3 = r7 + r8
  c34 : q1 + q3 + q5 + q8 = r4 + r6 + r8
  c35 : q1 + q3 + q5 + q7 = r4 + r6 + r8
  c36 : q3 + q5 = r2 + r8
  c45 : q1 + q3 + q5 + q6 = r4 + r6 + r8
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

theorem ex0_0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w0_0 = star (c y0) * d z5 + star (c y1) * d z6 + star (c y2) * d z7 + star (c y3) * d z8 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_5, fl0_6, fl0_7, fl0_8]
  simp only [sg0_0_5, sg0_0_6, sg0_0_7, sg0_0_8, SixQubit.signMul_false]
  try ring

theorem ex0_1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w0_1 = star (c y0) * d z5 - star (c y1) * d z6 + star (c y2) * d z7 - star (c y3) * d z8 := by
  unfold offSum
  rw [incidence0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl0_5, fl0_6, fl0_7, fl0_8]
  simp only [sg0_1_5, sg0_1_6, sg0_1_7, sg0_1_8, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

/-- The one-dimensional kernel of flip 0 gives an antisymmetric relation. -/
theorem rel0 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef0 w0_0 = 0)
    (h1 : offSum c d ef0 w0_1 = 0)
    : star (c y0) * d z5 + star (c y2) * d z7 = 0 := by
  rw [ex0_0] at h0
  rw [ex0_1] at h1
  linear_combination ((1 / 2) : ℂ) * h0 + ((1 / 2) : ℂ) * h1

/-- Squared moduli turn that relation into a quadratic identity. -/
theorem quad0 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef0 w0_0 = 0)
    (h1 : offSum c d ef0 w0_1 = 0)
    : Complex.normSq (c y0) * Complex.normSq (d z5)
      = Complex.normSq (c y2) * Complex.normSq (d z7) := by
  have hr := rel0 c d h0 h1
  have he : star (c y0) * d z5 = -(star (c y2) * d z7) := by
    linear_combination hr
  simpa [Complex.normSq_mul] using congrArg Complex.normSq he

theorem ex1_0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w1_0 = star (c y0) * d z3 + star (c y1) * d z4 + star (c y4) * d z7 + star (c y5) * d z8 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_3, fl1_4, fl1_7, fl1_8]
  simp only [sg1_0_3, sg1_0_4, sg1_0_7, sg1_0_8, SixQubit.signMul_false]
  try ring

theorem ex1_1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w1_1 = star (c y0) * d z3 - star (c y1) * d z4 + star (c y4) * d z7 - star (c y5) * d z8 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_3, fl1_4, fl1_7, fl1_8]
  simp only [sg1_1_3, sg1_1_4, sg1_1_7, sg1_1_8, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

/-- The one-dimensional kernel of flip 1 gives an antisymmetric relation. -/
theorem rel1 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef1 w1_0 = 0)
    (h1 : offSum c d ef1 w1_1 = 0)
    : star (c y0) * d z3 + star (c y4) * d z7 = 0 := by
  rw [ex1_0] at h0
  rw [ex1_1] at h1
  linear_combination ((1 / 2) : ℂ) * h0 + ((1 / 2) : ℂ) * h1

/-- Squared moduli turn that relation into a quadratic identity. -/
theorem quad1 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef1 w1_0 = 0)
    (h1 : offSum c d ef1 w1_1 = 0)
    : Complex.normSq (c y0) * Complex.normSq (d z3)
      = Complex.normSq (c y4) * Complex.normSq (d z7) := by
  have hr := rel1 c d h0 h1
  have he : star (c y0) * d z3 = -(star (c y4) * d z7) := by
    linear_combination hr
  simpa [Complex.normSq_mul] using congrArg Complex.normSq he

theorem ex2_0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w2_0 = star (c y2) * d z3 + star (c y3) * d z4 + star (c y4) * d z5 + star (c y5) * d z6 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_3, fl2_4, fl2_5, fl2_6]
  simp only [sg2_0_3, sg2_0_4, sg2_0_5, sg2_0_6, SixQubit.signMul_false]
  try ring

theorem ex2_1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w2_1 = star (c y2) * d z3 - star (c y3) * d z4 + star (c y4) * d z5 - star (c y5) * d z6 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_3, fl2_4, fl2_5, fl2_6]
  simp only [sg2_1_3, sg2_1_4, sg2_1_5, sg2_1_6, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

/-- The one-dimensional kernel of flip 2 gives an antisymmetric relation. -/
theorem rel2 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef2 w2_0 = 0)
    (h1 : offSum c d ef2 w2_1 = 0)
    : star (c y2) * d z3 + star (c y4) * d z5 = 0 := by
  rw [ex2_0] at h0
  rw [ex2_1] at h1
  linear_combination ((1 / 2) : ℂ) * h0 + ((1 / 2) : ℂ) * h1

/-- Squared moduli turn that relation into a quadratic identity. -/
theorem quad2 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef2 w2_0 = 0)
    (h1 : offSum c d ef2 w2_1 = 0)
    : Complex.normSq (c y2) * Complex.normSq (d z3)
      = Complex.normSq (c y4) * Complex.normSq (d z5) := by
  have hr := rel2 c d h0 h1
  have he : star (c y2) * d z3 = -(star (c y4) * d z5) := by
    linear_combination hr
  simpa [Complex.normSq_mul] using congrArg Complex.normSq he

/-! ## The collapse of the polytope -/

/-- Quadratic identity 0, reduced against the moment system. -/
theorem lin0 {q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8)
    (hq : q0 * r3 = q4 * r7) :
    r6/4 + r8/2 - 5/48 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8⟩ := h
  linear_combination hq + (-r3) * n0 + (r3 - r6/4 + 5*r7/12 - r8/12 + 5/48) * n1 + (r3 - r6/4 + 5*r7/12 - r8/12 + 5/48) * m1 + (r3 - r6/4 + 5*r7/12 + 11*r8/12 + 5/48) * m2 + (r3 - r6/4 + 5*r7/12 - 5*r8/12 + 5/48) * m6 + (r6/2 - r7/6 + r8/2 - 5/24) * c12 + (-r3 - r7 - r8) * c15 + (-r3 + r6/2 + r7/6 + r8/2 - 5/24) * c16 + (-r3 - r8) * c25 + (-r3 + r6/2 - 5*r7/6 - r8/2 - 5/24) * c26 + (-r3 - 2*r7/3 - 4*r8/3) * c34 + (r3 + r7/3 + 2*r8/3) * c35 + (r8/3) * c36 + (r3 + r7/3 + 2*r8/3) * c45 + (r8/3) * c46 + (r8/3) * c56

/-- Quadratic identity 1, reduced against the moment system. -/
theorem lin1 {q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8)
    (hq : q2 * r3 = q4 * r5) :
    r6/2 + r8/4 - 5/48 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8⟩ := h
  linear_combination hq + (5*r5/12 - r6/12 - r8/4 + 5/48) * n1 + (5*r5/12 + 11*r6/12 + 3*r8/4 - 5/16) * m1 + (5*r5/12 + 11*r6/12 - r8/4 + 5/48) * m2 + (-r3/3 + 5*r5/12 - 5*r6/12 - r8/4 + 5/48) * m6 + (2*r3/3 - r5/6 - r6/2 - r8/2 + 5/24) * c12 + (-r3 - r5 - r6) * c15 + (r3/3 + r5/6 - r6/2 - r8/2 + 5/24) * c16 + (-r6) * c25 + (-2*r3/3 - 5*r5/6 - r6/2 + r8/2 - 5/24) * c26 + (-2*r3/3 - 2*r5/3 - 4*r6/3) * c34 + (r3/3 + r5/3 + 2*r6/3) * c35 + (r3/3 + r6/3) * c36 + (r3/3 + r5/3 + 2*r6/3) * c45 + (r3/3 + r6/3) * c46 + (r3/3 + r6/3) * c56

/-- Every probability the cycle uses is forced to an exact positive value. -/
theorem pinned {q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8)
    (v0 : r6/4 + r8/2 - 5/48 = 0)
    (v1 : r6/2 + r8/4 - 5/48 = 0)
    : q0 = 5/36 ∧ q2 = 5/36 ∧ q4 = 5/36 ∧ r3 = 1/9 ∧ r5 = 1/9 ∧ r7 = 1/9 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-! ## The odd cycle -/

/-- **Orbit 54 is impossible.** -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)))
    (e0_0 : offSum c d ef0 w0_0 = 0)
    (e0_1 : offSum c d ef0 w0_1 = 0)
    (e1_0 : offSum c d ef1 w1_0 = 0)
    (e1_1 : offSum c d ef1 w1_1 = 0)
    (e2_0 : offSum c d ef2 w2_0 = 0)
    (e2_1 : offSum c d ef2 w2_1 = 0)
    : False := by
  have v0 := lin0 hm (quad1 c d e1_0 e1_1)
  have v1 := lin1 hm (quad2 c d e2_0 e2_1)
  obtain ⟨p0, p2, p4, p12, p14, p16⟩ := pinned hm v0 v1
  have n0 : c y0 ≠ 0 := fun hz => by rw [hz] at p0; norm_num at p0
  have n2 : c y2 ≠ 0 := fun hz => by rw [hz] at p2; norm_num at p2
  have n4 : c y4 ≠ 0 := fun hz => by rw [hz] at p4; norm_num at p4
  have n12 : d z3 ≠ 0 := fun hz => by rw [hz] at p12; norm_num at p12
  have n14 : d z5 ≠ 0 := fun hz => by rw [hz] at p14; norm_num at p14
  have n16 : d z7 ≠ 0 := fun hz => by rw [hz] at p16; norm_num at p16
  have R0 := rel0 c d e0_0 e0_1
  have R1 := rel1 c d e1_0 e1_1
  have R2 := rel2 c d e2_0 e2_1
  have key : (2 : ℂ) * ((star (c y0) * d z5) * (star (c y4) * d z7) * (star (c y2) * d z3)) = 0 := by
    linear_combination ((star (c y4) * d z7) * (star (c y2) * d z3)) * R0 - ((star (c y2) * d z7) * (star (c y2) * d z3)) * R1 + ((star (c y2) * d z7) * (star (c y0) * d z3)) * R2
  have hz : ((star (c y0) * d z5) * (star (c y4) * d z7) * (star (c y2) * d z3)) = 0 := by linear_combination key / 2
  simp [n0, n2, n4, n12, n14, n16] at hz

end

end SixQubit.Orbit54
