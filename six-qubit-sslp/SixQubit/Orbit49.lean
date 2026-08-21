import Mathlib

import SS.FullKL
import SixQubit.Common
import SixQubit.Triangle

/-!
# Six-qubit no-go for moment orbit 49

Orbit 49 of `six_qubit_sslp.tex`: q = 6, angle vector a = (1, 1, 1, 3, 3, 5),
residues 0 and 2.  The two fibers are complementary, so the top fiber is
indexed by bitwise complement of the bottom one.

The eight weight-two masks that pair an index `i <= 7` with the anchor index 8
each isolate a *reciprocal* relation `star (c y8) * d zi + star (c yi) * d z8 = 0`.
Four further masks have a single rank-one row, for instance

```
star (c y3) * d z0 + star (c y2) * d z1 + star (c y1) * d z2 + star (c y0) * d z3 = 0 .
```

The paper divides by amplitudes to introduce phase ratios `rho_i = d_i / conj(c_i)`
and propagates a uniform phase.  This module never divides.  Multiplying a
rank-one row by `star (c y8)` and substituting the four reciprocal relations
gives, identically,

```
star (c y8) * (row)  =  -2 * (d z8) * (star (c y0) * star (c y3) + star (c y1) * star (c y2)) ,
```

and the moment polytope pins `normSq (d z8) = 1/6`, so the quadric factor
vanishes.  Conjugating turns it into `c y0 * c y3 + c y1 * c y2 = 0`; taking
`normSq` turns the four such quadrics into the three moment equations
`p0 p3 = p1 p2`, `p0 p5 = p1 p4`, `p0 p7 = p1 p6`, which collapse the whole
three-dimensional polytope to the single point where `p0 = ... = p7 = 1/12`.
With every amplitude nonzero, `SixQubit.Triangle.pair_contradiction_of_normSq`
closes the resulting mixed pair triangle.

Everything computational is decided by the Lean kernel; `native_decide`
is not used.
-/

namespace SixQubit.Orbit49

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

/-! ## The two fibers -/

def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]

def y0 : SS.BitString 6 := bs false false false false false false  -- 000000
def y1 : SS.BitString 6 := bs false false false true  true  false  -- 000110
def y2 : SS.BitString 6 := bs false false true  false false true   -- 001001
def y3 : SS.BitString 6 := bs false false true  true  true  true   -- 001111
def y4 : SS.BitString 6 := bs false true  false false false true   -- 010001
def y5 : SS.BitString 6 := bs false true  false true  true  true   -- 010111
def y6 : SS.BitString 6 := bs true  false false false false true   -- 100001
def y7 : SS.BitString 6 := bs true  false false true  true  true   -- 100111
def y8 : SS.BitString 6 := bs true  true  true  false true  false  -- 111010
def y9 : SS.BitString 6 := bs true  true  true  true  false false  -- 111100

def z0 : SS.BitString 6 := bs true  true  true  true  true  true   -- 111111
def z1 : SS.BitString 6 := bs true  true  true  false false true   -- 111001
def z2 : SS.BitString 6 := bs true  true  false true  true  false  -- 110110
def z3 : SS.BitString 6 := bs true  true  false false false false  -- 110000
def z4 : SS.BitString 6 := bs true  false true  true  true  false  -- 101110
def z5 : SS.BitString 6 := bs true  false true  false false false  -- 101000
def z6 : SS.BitString 6 := bs false true  true  true  true  false  -- 011110
def z7 : SS.BitString 6 := bs false true  true  false false false  -- 011000
def z8 : SS.BitString 6 := bs false false false true  false true   -- 000101
def z9 : SS.BitString 6 := bs false false false false true  true   -- 000011

def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9}
def S1 : Finset (SS.BitString 6) := {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9}

def av : Fin 6 -> ZMod 6 := ![1, 1, 1, 3, 3, 5]

theorem S0_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 0) = S0 := by
  decide

theorem S1_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 2) = S1 := by
  decide

/-! ## Flip masks, dressings, incidences and signs -/

def ef0 : SS.BitString 6 := bs false false false true  false true   -- 000101
def ef1 : SS.BitString 6 := bs false false false false true  true   -- 000011
def ef2 : SS.BitString 6 := bs false false true  true  false false  -- 001100
def ef3 : SS.BitString 6 := bs false false true  false true  false  -- 001010
def ef4 : SS.BitString 6 := bs false true  false true  false false  -- 010100
def ef5 : SS.BitString 6 := bs false true  false false true  false  -- 010010
def ef6 : SS.BitString 6 := bs true  false false true  false false  -- 100100
def ef7 : SS.BitString 6 := bs true  false false false true  false  -- 100010
def ef8 : SS.BitString 6 := bs true  true  false false false false  -- 110000
def ef9 : SS.BitString 6 := bs true  false true  false false false  -- 101000
def ef10 : SS.BitString 6 := bs true  false false false false true   -- 100001
def ef11 : SS.BitString 6 := bs false true  true  false false false  -- 011000

def w0 : SS.BitString 6 := bs false false false false false false  -- 000000
def w1 : SS.BitString 6 := bs false false false true  false false  -- 000100
def w2 : SS.BitString 6 := bs false false false false true  false  -- 000010

theorem incidence_ef0 :
    S1.filter (fun y => SS.bxor y ef0 ∈ S0) = {z0, z1, z8, z9} := by decide
theorem flip_ef0_z0 : SS.bxor z0 ef0 = y8 := by decide
theorem flip_ef0_z1 : SS.bxor z1 ef0 = y9 := by decide
theorem flip_ef0_z8 : SS.bxor z8 ef0 = y0 := by decide
theorem flip_ef0_z9 : SS.bxor z9 ef0 = y1 := by decide
theorem incidence_ef1 :
    S1.filter (fun y => SS.bxor y ef1 ∈ S0) = {z0, z1, z8, z9} := by decide
theorem flip_ef1_z0 : SS.bxor z0 ef1 = y9 := by decide
theorem flip_ef1_z1 : SS.bxor z1 ef1 = y8 := by decide
theorem flip_ef1_z8 : SS.bxor z8 ef1 = y1 := by decide
theorem flip_ef1_z9 : SS.bxor z9 ef1 = y0 := by decide
theorem incidence_ef2 :
    S1.filter (fun y => SS.bxor y ef2 ∈ S0) = {z2, z3, z8, z9} := by decide
theorem flip_ef2_z2 : SS.bxor z2 ef2 = y8 := by decide
theorem flip_ef2_z3 : SS.bxor z3 ef2 = y9 := by decide
theorem flip_ef2_z8 : SS.bxor z8 ef2 = y2 := by decide
theorem flip_ef2_z9 : SS.bxor z9 ef2 = y3 := by decide
theorem incidence_ef3 :
    S1.filter (fun y => SS.bxor y ef3 ∈ S0) = {z2, z3, z8, z9} := by decide
theorem flip_ef3_z2 : SS.bxor z2 ef3 = y9 := by decide
theorem flip_ef3_z3 : SS.bxor z3 ef3 = y8 := by decide
theorem flip_ef3_z8 : SS.bxor z8 ef3 = y3 := by decide
theorem flip_ef3_z9 : SS.bxor z9 ef3 = y2 := by decide
theorem incidence_ef4 :
    S1.filter (fun y => SS.bxor y ef4 ∈ S0) = {z4, z5, z8, z9} := by decide
theorem flip_ef4_z4 : SS.bxor z4 ef4 = y8 := by decide
theorem flip_ef4_z5 : SS.bxor z5 ef4 = y9 := by decide
theorem flip_ef4_z8 : SS.bxor z8 ef4 = y4 := by decide
theorem flip_ef4_z9 : SS.bxor z9 ef4 = y5 := by decide
theorem incidence_ef5 :
    S1.filter (fun y => SS.bxor y ef5 ∈ S0) = {z4, z5, z8, z9} := by decide
theorem flip_ef5_z4 : SS.bxor z4 ef5 = y9 := by decide
theorem flip_ef5_z5 : SS.bxor z5 ef5 = y8 := by decide
theorem flip_ef5_z8 : SS.bxor z8 ef5 = y5 := by decide
theorem flip_ef5_z9 : SS.bxor z9 ef5 = y4 := by decide
theorem incidence_ef6 :
    S1.filter (fun y => SS.bxor y ef6 ∈ S0) = {z6, z7, z8, z9} := by decide
theorem flip_ef6_z6 : SS.bxor z6 ef6 = y8 := by decide
theorem flip_ef6_z7 : SS.bxor z7 ef6 = y9 := by decide
theorem flip_ef6_z8 : SS.bxor z8 ef6 = y6 := by decide
theorem flip_ef6_z9 : SS.bxor z9 ef6 = y7 := by decide
theorem incidence_ef7 :
    S1.filter (fun y => SS.bxor y ef7 ∈ S0) = {z6, z7, z8, z9} := by decide
theorem flip_ef7_z6 : SS.bxor z6 ef7 = y9 := by decide
theorem flip_ef7_z7 : SS.bxor z7 ef7 = y8 := by decide
theorem flip_ef7_z8 : SS.bxor z8 ef7 = y7 := by decide
theorem flip_ef7_z9 : SS.bxor z9 ef7 = y6 := by decide
theorem incidence_ef8 :
    S1.filter (fun y => SS.bxor y ef8 ∈ S0) = {z0, z1, z2, z3} := by decide
theorem flip_ef8_z0 : SS.bxor z0 ef8 = y3 := by decide
theorem flip_ef8_z1 : SS.bxor z1 ef8 = y2 := by decide
theorem flip_ef8_z2 : SS.bxor z2 ef8 = y1 := by decide
theorem flip_ef8_z3 : SS.bxor z3 ef8 = y0 := by decide
theorem incidence_ef9 :
    S1.filter (fun y => SS.bxor y ef9 ∈ S0) = {z0, z1, z4, z5} := by decide
theorem flip_ef9_z0 : SS.bxor z0 ef9 = y5 := by decide
theorem flip_ef9_z1 : SS.bxor z1 ef9 = y4 := by decide
theorem flip_ef9_z4 : SS.bxor z4 ef9 = y1 := by decide
theorem flip_ef9_z5 : SS.bxor z5 ef9 = y0 := by decide
theorem incidence_ef10 :
    S1.filter (fun y => SS.bxor y ef10 ∈ S0) = {z2, z3, z4, z5} := by decide
theorem flip_ef10_z2 : SS.bxor z2 ef10 = y5 := by decide
theorem flip_ef10_z3 : SS.bxor z3 ef10 = y4 := by decide
theorem flip_ef10_z4 : SS.bxor z4 ef10 = y3 := by decide
theorem flip_ef10_z5 : SS.bxor z5 ef10 = y2 := by decide
theorem incidence_ef11 :
    S1.filter (fun y => SS.bxor y ef11 ∈ S0) = {z0, z1, z6, z7} := by decide
theorem flip_ef11_z0 : SS.bxor z0 ef11 = y7 := by decide
theorem flip_ef11_z1 : SS.bxor z1 ef11 = y6 := by decide
theorem flip_ef11_z6 : SS.bxor z6 ef11 = y1 := by decide
theorem flip_ef11_z7 : SS.bxor z7 ef11 = y0 := by decide

theorem sg_w0_z0 : SS.bdot w0 z0 = false := by decide
theorem sg_w0_z1 : SS.bdot w0 z1 = false := by decide
theorem sg_w0_z8 : SS.bdot w0 z8 = false := by decide
theorem sg_w0_z9 : SS.bdot w0 z9 = false := by decide
theorem sg_w1_z0 : SS.bdot w1 z0 = true := by decide
theorem sg_w1_z1 : SS.bdot w1 z1 = false := by decide
theorem sg_w1_z8 : SS.bdot w1 z8 = true := by decide
theorem sg_w1_z9 : SS.bdot w1 z9 = false := by decide
theorem sg_w2_z0 : SS.bdot w2 z0 = true := by decide
theorem sg_w2_z1 : SS.bdot w2 z1 = false := by decide
theorem sg_w2_z8 : SS.bdot w2 z8 = false := by decide
theorem sg_w2_z9 : SS.bdot w2 z9 = true := by decide
theorem sg_w0_z2 : SS.bdot w0 z2 = false := by decide
theorem sg_w0_z3 : SS.bdot w0 z3 = false := by decide
theorem sg_w1_z2 : SS.bdot w1 z2 = true := by decide
theorem sg_w1_z3 : SS.bdot w1 z3 = false := by decide
theorem sg_w2_z2 : SS.bdot w2 z2 = true := by decide
theorem sg_w2_z3 : SS.bdot w2 z3 = false := by decide
theorem sg_w0_z4 : SS.bdot w0 z4 = false := by decide
theorem sg_w0_z5 : SS.bdot w0 z5 = false := by decide
theorem sg_w1_z4 : SS.bdot w1 z4 = true := by decide
theorem sg_w1_z5 : SS.bdot w1 z5 = false := by decide
theorem sg_w2_z4 : SS.bdot w2 z4 = true := by decide
theorem sg_w2_z5 : SS.bdot w2 z5 = false := by decide
theorem sg_w0_z6 : SS.bdot w0 z6 = false := by decide
theorem sg_w0_z7 : SS.bdot w0 z7 = false := by decide
theorem sg_w1_z6 : SS.bdot w1 z6 = true := by decide
theorem sg_w1_z7 : SS.bdot w1 z7 = false := by decide
theorem sg_w2_z6 : SS.bdot w2 z6 = true := by decide
theorem sg_w2_z7 : SS.bdot w2 z7 = false := by decide

/-! ## The moment system -/

/-- The two normalizations, the twenty-one moment equalities, and the
nonnegativity of every probability. -/
structure MomentSystem (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Real) : Prop where
  n0 : q0 + q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 + q9 = 1
  n1 : r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 = 1
  m1 : q6 + q7 + q8 + q9 = r0 + r1 + r2 + r3 + r4 + r5
  m2 : q4 + q5 + q8 + q9 = r0 + r1 + r2 + r3 + r6 + r7
  m3 : q2 + q3 + q8 + q9 = r0 + r1 + r4 + r5 + r6 + r7
  m4 : q1 + q3 + q5 + q7 + q9 = r0 + r2 + r4 + r6 + r8
  m5 : q1 + q3 + q5 + q7 + q8 = r0 + r2 + r4 + r6 + r9
  m6 : q2 + q3 + q4 + q5 + q6 + q7 = r0 + r1 + r8 + r9
  m12 : q8 + q9 = r0 + r1 + r2 + r3
  m13 : q8 + q9 = r0 + r1 + r4 + r5
  m14 : q7 + q9 = r0 + r2 + r4
  m15 : q7 + q8 = r0 + r2 + r4
  m16 : q6 + q7 = r0 + r1
  m23 : q8 + q9 = r0 + r1 + r6 + r7
  m24 : q5 + q9 = r0 + r2 + r6
  m25 : q5 + q8 = r0 + r2 + r6
  m26 : q4 + q5 = r0 + r1
  m34 : q3 + q9 = r0 + r4 + r6
  m35 : q3 + q8 = r0 + r4 + r6
  m36 : q2 + q3 = r0 + r1
  m45 : q1 + q3 + q5 + q7 = r0 + r2 + r4 + r6
  m46 : q3 + q5 + q7 = r0 + r8
  m56 : q3 + q5 + q7 = r0 + r9

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

/-- The top probability at the anchor index 8 is pinned by the moment
polytope alone. -/
theorem MomentSystem.top8 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Real}
    (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r8 = 1/6 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, m12, m13, m14, m15, m16, m23, m24, m25, m26, m34, m35, m36, m45, m46, m56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9⟩ := h
  linarith

/-- With the three quadratic consequences of the rank-one masks the whole
polytope collapses to the single point `1/12`. -/
theorem MomentSystem.pinned {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Real}
    (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9)
    (e1 : q0 * q3 = q1 * q2)
    (e2 : q0 * q5 = q1 * q4)
    (e3 : q0 * q7 = q1 * q6) :
    q1 = 1/12 ∧ q2 = 1/12 ∧ q4 = 1/12 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, m12, m13, m14, m15, m16, m23, m24, m25, m26, m34, m35, m36, m45, m46, m56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9⟩ := h
  have hq1 : q1 = 1/6 - q0 := by linarith
  have hq3 : q3 = 1/6 - q2 := by linarith
  have hq5 : q5 = 1/6 - q4 := by linarith
  have hq7 : q7 = 1/6 - q6 := by linarith
  rw [hq1, hq3] at e1
  rw [hq1, hq5] at e2
  rw [hq1, hq7] at e3
  have t1 : q0 = q2 := by linear_combination (6 : Real) * e1
  have t2 : q0 = q4 := by linear_combination (6 : Real) * e2
  have t3 : q0 = q6 := by linear_combination (6 : Real) * e3
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-! ## The Walsh expansions -/

def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),
      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

theorem ex_ef0_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w0 = star (c y8) * d z0 + star (c y9) * d z1 + star (c y0) * d z8 + star (c y1) * d z9 := by
  unfold offSum
  rw [incidence_ef0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef0_z0, flip_ef0_z1, flip_ef0_z8, flip_ef0_z9]
  simp only [sg_w0_z0, sg_w0_z1, sg_w0_z8, sg_w0_z9, SixQubit.signMul_false]
  try ring

theorem ex_ef0_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w1 = - star (c y8) * d z0 + star (c y9) * d z1 - star (c y0) * d z8 + star (c y1) * d z9 := by
  unfold offSum
  rw [incidence_ef0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef0_z0, flip_ef0_z1, flip_ef0_z8, flip_ef0_z9]
  simp only [sg_w1_z0, sg_w1_z1, sg_w1_z8, sg_w1_z9, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef1_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w0 = star (c y9) * d z0 + star (c y8) * d z1 + star (c y1) * d z8 + star (c y0) * d z9 := by
  unfold offSum
  rw [incidence_ef1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef1_z0, flip_ef1_z1, flip_ef1_z8, flip_ef1_z9]
  simp only [sg_w0_z0, sg_w0_z1, sg_w0_z8, sg_w0_z9, SixQubit.signMul_false]
  try ring

theorem ex_ef1_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w2 = - star (c y9) * d z0 + star (c y8) * d z1 + star (c y1) * d z8 - star (c y0) * d z9 := by
  unfold offSum
  rw [incidence_ef1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef1_z0, flip_ef1_z1, flip_ef1_z8, flip_ef1_z9]
  simp only [sg_w2_z0, sg_w2_z1, sg_w2_z8, sg_w2_z9, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef2_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w0 = star (c y8) * d z2 + star (c y9) * d z3 + star (c y2) * d z8 + star (c y3) * d z9 := by
  unfold offSum
  rw [incidence_ef2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef2_z2, flip_ef2_z3, flip_ef2_z8, flip_ef2_z9]
  simp only [sg_w0_z2, sg_w0_z3, sg_w0_z8, sg_w0_z9, SixQubit.signMul_false]
  try ring

theorem ex_ef2_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w1 = - star (c y8) * d z2 + star (c y9) * d z3 - star (c y2) * d z8 + star (c y3) * d z9 := by
  unfold offSum
  rw [incidence_ef2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef2_z2, flip_ef2_z3, flip_ef2_z8, flip_ef2_z9]
  simp only [sg_w1_z2, sg_w1_z3, sg_w1_z8, sg_w1_z9, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef3_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w0 = star (c y9) * d z2 + star (c y8) * d z3 + star (c y3) * d z8 + star (c y2) * d z9 := by
  unfold offSum
  rw [incidence_ef3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef3_z2, flip_ef3_z3, flip_ef3_z8, flip_ef3_z9]
  simp only [sg_w0_z2, sg_w0_z3, sg_w0_z8, sg_w0_z9, SixQubit.signMul_false]
  try ring

theorem ex_ef3_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w2 = - star (c y9) * d z2 + star (c y8) * d z3 + star (c y3) * d z8 - star (c y2) * d z9 := by
  unfold offSum
  rw [incidence_ef3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef3_z2, flip_ef3_z3, flip_ef3_z8, flip_ef3_z9]
  simp only [sg_w2_z2, sg_w2_z3, sg_w2_z8, sg_w2_z9, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef4_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w0 = star (c y8) * d z4 + star (c y9) * d z5 + star (c y4) * d z8 + star (c y5) * d z9 := by
  unfold offSum
  rw [incidence_ef4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef4_z4, flip_ef4_z5, flip_ef4_z8, flip_ef4_z9]
  simp only [sg_w0_z4, sg_w0_z5, sg_w0_z8, sg_w0_z9, SixQubit.signMul_false]
  try ring

theorem ex_ef4_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w1 = - star (c y8) * d z4 + star (c y9) * d z5 - star (c y4) * d z8 + star (c y5) * d z9 := by
  unfold offSum
  rw [incidence_ef4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef4_z4, flip_ef4_z5, flip_ef4_z8, flip_ef4_z9]
  simp only [sg_w1_z4, sg_w1_z5, sg_w1_z8, sg_w1_z9, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef5_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef5 w0 = star (c y9) * d z4 + star (c y8) * d z5 + star (c y5) * d z8 + star (c y4) * d z9 := by
  unfold offSum
  rw [incidence_ef5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef5_z4, flip_ef5_z5, flip_ef5_z8, flip_ef5_z9]
  simp only [sg_w0_z4, sg_w0_z5, sg_w0_z8, sg_w0_z9, SixQubit.signMul_false]
  try ring

theorem ex_ef5_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef5 w2 = - star (c y9) * d z4 + star (c y8) * d z5 + star (c y5) * d z8 - star (c y4) * d z9 := by
  unfold offSum
  rw [incidence_ef5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef5_z4, flip_ef5_z5, flip_ef5_z8, flip_ef5_z9]
  simp only [sg_w2_z4, sg_w2_z5, sg_w2_z8, sg_w2_z9, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef6_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w0 = star (c y8) * d z6 + star (c y9) * d z7 + star (c y6) * d z8 + star (c y7) * d z9 := by
  unfold offSum
  rw [incidence_ef6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef6_z6, flip_ef6_z7, flip_ef6_z8, flip_ef6_z9]
  simp only [sg_w0_z6, sg_w0_z7, sg_w0_z8, sg_w0_z9, SixQubit.signMul_false]
  try ring

theorem ex_ef6_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w1 = - star (c y8) * d z6 + star (c y9) * d z7 - star (c y6) * d z8 + star (c y7) * d z9 := by
  unfold offSum
  rw [incidence_ef6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef6_z6, flip_ef6_z7, flip_ef6_z8, flip_ef6_z9]
  simp only [sg_w1_z6, sg_w1_z7, sg_w1_z8, sg_w1_z9, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef7_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef7 w0 = star (c y9) * d z6 + star (c y8) * d z7 + star (c y7) * d z8 + star (c y6) * d z9 := by
  unfold offSum
  rw [incidence_ef7]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef7_z6, flip_ef7_z7, flip_ef7_z8, flip_ef7_z9]
  simp only [sg_w0_z6, sg_w0_z7, sg_w0_z8, sg_w0_z9, SixQubit.signMul_false]
  try ring

theorem ex_ef7_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef7 w2 = - star (c y9) * d z6 + star (c y8) * d z7 + star (c y7) * d z8 - star (c y6) * d z9 := by
  unfold offSum
  rw [incidence_ef7]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef7_z6, flip_ef7_z7, flip_ef7_z8, flip_ef7_z9]
  simp only [sg_w2_z6, sg_w2_z7, sg_w2_z8, sg_w2_z9, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef8_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef8 w0 = star (c y3) * d z0 + star (c y2) * d z1 + star (c y1) * d z2 + star (c y0) * d z3 := by
  unfold offSum
  rw [incidence_ef8]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef8_z0, flip_ef8_z1, flip_ef8_z2, flip_ef8_z3]
  simp only [sg_w0_z0, sg_w0_z1, sg_w0_z2, sg_w0_z3, SixQubit.signMul_false]
  try ring

theorem ex_ef9_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef9 w0 = star (c y5) * d z0 + star (c y4) * d z1 + star (c y1) * d z4 + star (c y0) * d z5 := by
  unfold offSum
  rw [incidence_ef9]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef9_z0, flip_ef9_z1, flip_ef9_z4, flip_ef9_z5]
  simp only [sg_w0_z0, sg_w0_z1, sg_w0_z4, sg_w0_z5, SixQubit.signMul_false]
  try ring

theorem ex_ef10_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef10 w0 = star (c y5) * d z2 + star (c y4) * d z3 + star (c y3) * d z4 + star (c y2) * d z5 := by
  unfold offSum
  rw [incidence_ef10]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef10_z2, flip_ef10_z3, flip_ef10_z4, flip_ef10_z5]
  simp only [sg_w0_z2, sg_w0_z3, sg_w0_z4, sg_w0_z5, SixQubit.signMul_false]
  try ring

theorem ex_ef11_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef11 w0 = star (c y7) * d z0 + star (c y6) * d z1 + star (c y1) * d z6 + star (c y0) * d z7 := by
  unfold offSum
  rw [incidence_ef11]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef11_z0, flip_ef11_z1, flip_ef11_z6, flip_ef11_z7]
  simp only [sg_w0_z0, sg_w0_z1, sg_w0_z6, sg_w0_z7, SixQubit.signMul_false]
  try ring

/-! ## The no-go -/

/-- **Orbit 49 is impossible.** -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)))
    (h0 : offSum c d ef0 w0 = 0)
    (h1 : offSum c d ef0 w1 = 0)
    (h2 : offSum c d ef1 w0 = 0)
    (h3 : offSum c d ef1 w2 = 0)
    (h4 : offSum c d ef2 w0 = 0)
    (h5 : offSum c d ef2 w1 = 0)
    (h6 : offSum c d ef3 w0 = 0)
    (h7 : offSum c d ef3 w2 = 0)
    (h8 : offSum c d ef4 w0 = 0)
    (h9 : offSum c d ef4 w1 = 0)
    (h10 : offSum c d ef5 w0 = 0)
    (h11 : offSum c d ef5 w2 = 0)
    (h12 : offSum c d ef6 w0 = 0)
    (h13 : offSum c d ef6 w1 = 0)
    (h14 : offSum c d ef7 w0 = 0)
    (h15 : offSum c d ef7 w2 = 0)
    (h16 : offSum c d ef8 w0 = 0)
    (h17 : offSum c d ef9 w0 = 0)
    (h18 : offSum c d ef10 w0 = 0)
    (h19 : offSum c d ef11 w0 = 0)
    : False := by
  rw [ex_ef0_w0] at h0
  rw [ex_ef0_w1] at h1
  rw [ex_ef1_w0] at h2
  rw [ex_ef1_w2] at h3
  rw [ex_ef2_w0] at h4
  rw [ex_ef2_w1] at h5
  rw [ex_ef3_w0] at h6
  rw [ex_ef3_w2] at h7
  rw [ex_ef4_w0] at h8
  rw [ex_ef4_w1] at h9
  rw [ex_ef5_w0] at h10
  rw [ex_ef5_w2] at h11
  rw [ex_ef6_w0] at h12
  rw [ex_ef6_w1] at h13
  rw [ex_ef7_w0] at h14
  rw [ex_ef7_w2] at h15
  rw [ex_ef8_w0] at h16
  rw [ex_ef9_w0] at h17
  rw [ex_ef10_w0] at h18
  rw [ex_ef11_w0] at h19
  have rec0 : star (c y8) * d z0 + star (c y0) * d z8 = 0 := by
    linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1
  have rec1 : star (c y8) * d z1 + star (c y1) * d z8 = 0 := by
    linear_combination (1/2 : ℂ) * h2 + (1/2 : ℂ) * h3
  have rec2 : star (c y8) * d z2 + star (c y2) * d z8 = 0 := by
    linear_combination (1/2 : ℂ) * h4 + (-1/2 : ℂ) * h5
  have rec3 : star (c y8) * d z3 + star (c y3) * d z8 = 0 := by
    linear_combination (1/2 : ℂ) * h6 + (1/2 : ℂ) * h7
  have rec4 : star (c y8) * d z4 + star (c y4) * d z8 = 0 := by
    linear_combination (1/2 : ℂ) * h8 + (-1/2 : ℂ) * h9
  have rec5 : star (c y8) * d z5 + star (c y5) * d z8 = 0 := by
    linear_combination (1/2 : ℂ) * h10 + (1/2 : ℂ) * h11
  have rec6 : star (c y8) * d z6 + star (c y6) * d z8 = 0 := by
    linear_combination (1/2 : ℂ) * h12 + (-1/2 : ℂ) * h13
  have rec7 : star (c y8) * d z7 + star (c y7) * d z8 = 0 := by
    linear_combination (1/2 : ℂ) * h14 + (1/2 : ℂ) * h15
  have mk1 : star (c y3) * d z0 + star (c y2) * d z1 + star (c y1) * d z2 + star (c y0) * d z3 = 0 := by
    linear_combination (1 : ℂ) * h16
  have mk2 : star (c y5) * d z0 + star (c y4) * d z1 + star (c y1) * d z4 + star (c y0) * d z5 = 0 := by
    linear_combination (1 : ℂ) * h17
  have mk3 : star (c y5) * d z2 + star (c y4) * d z3 + star (c y3) * d z4 + star (c y2) * d z5 = 0 := by
    linear_combination (1 : ℂ) * h18
  have mk4 : star (c y7) * d z0 + star (c y6) * d z1 + star (c y1) * d z6 + star (c y0) * d z7 = 0 := by
    linear_combination (1 : ℂ) * h19
  have hz8 : d z8 ≠ 0 :=
    Complex.normSq_pos.mp (by rw [hm.top8]; norm_num)
  have P1 : star (c y0) * star (c y3) + star (c y1) * star (c y2) = 0 := by
    have key : (star (c y0) * star (c y3) + star (c y1) * star (c y2)) * d z8 = 0 := by
      linear_combination (-star (c y8) / 2) * mk1
        + (star (c y3) / 2) * rec0 + (star (c y2) / 2) * rec1 + (star (c y1) / 2) * rec2 + (star (c y0) / 2) * rec3
    exact (mul_eq_zero.mp key).resolve_right hz8
  have P2 : star (c y0) * star (c y5) + star (c y1) * star (c y4) = 0 := by
    have key : (star (c y0) * star (c y5) + star (c y1) * star (c y4)) * d z8 = 0 := by
      linear_combination (-star (c y8) / 2) * mk2
        + (star (c y5) / 2) * rec0 + (star (c y4) / 2) * rec1 + (star (c y1) / 2) * rec4 + (star (c y0) / 2) * rec5
    exact (mul_eq_zero.mp key).resolve_right hz8
  have P3 : star (c y2) * star (c y5) + star (c y3) * star (c y4) = 0 := by
    have key : (star (c y2) * star (c y5) + star (c y3) * star (c y4)) * d z8 = 0 := by
      linear_combination (-star (c y8) / 2) * mk3
        + (star (c y5) / 2) * rec2 + (star (c y4) / 2) * rec3 + (star (c y3) / 2) * rec4 + (star (c y2) / 2) * rec5
    exact (mul_eq_zero.mp key).resolve_right hz8
  have P4 : star (c y0) * star (c y7) + star (c y1) * star (c y6) = 0 := by
    have key : (star (c y0) * star (c y7) + star (c y1) * star (c y6)) * d z8 = 0 := by
      linear_combination (-star (c y8) / 2) * mk4
        + (star (c y7) / 2) * rec0 + (star (c y6) / 2) * rec1 + (star (c y1) / 2) * rec6 + (star (c y0) / 2) * rec7
    exact (mul_eq_zero.mp key).resolve_right hz8
  have Q1 : c y0 * c y3 + c y1 * c y2 = 0 := by
    have hst := congrArg star P1
    simp only [star_add, star_mul, star_star, star_zero] at hst
    linear_combination hst
  have Q2 : c y0 * c y5 + c y1 * c y4 = 0 := by
    have hst := congrArg star P2
    simp only [star_add, star_mul, star_star, star_zero] at hst
    linear_combination hst
  have Q3 : c y2 * c y5 + c y3 * c y4 = 0 := by
    have hst := congrArg star P3
    simp only [star_add, star_mul, star_star, star_zero] at hst
    linear_combination hst
  have Q4 : c y0 * c y7 + c y1 * c y6 = 0 := by
    have hst := congrArg star P4
    simp only [star_add, star_mul, star_star, star_zero] at hst
    linear_combination hst
  have E1 : Complex.normSq (c y0) * Complex.normSq (c y3)
      = Complex.normSq (c y1) * Complex.normSq (c y2) := by
    have hne : c y0 * c y3 = -(c y1 * c y2) := by linear_combination Q1
    have hsq := congrArg Complex.normSq hne
    simpa [Complex.normSq_mul] using hsq
  have E2 : Complex.normSq (c y0) * Complex.normSq (c y5)
      = Complex.normSq (c y1) * Complex.normSq (c y4) := by
    have hne : c y0 * c y5 = -(c y1 * c y4) := by linear_combination Q2
    have hsq := congrArg Complex.normSq hne
    simpa [Complex.normSq_mul] using hsq
  have E3 : Complex.normSq (c y0) * Complex.normSq (c y7)
      = Complex.normSq (c y1) * Complex.normSq (c y6) := by
    have hne : c y0 * c y7 = -(c y1 * c y6) := by linear_combination Q4
    have hsq := congrArg Complex.normSq hne
    simpa [Complex.normSq_mul] using hsq
  obtain ⟨g1, g2, g4⟩ := hm.pinned E1 E2 E3
  exact SixQubit.Triangle.pair_contradiction_of_normSq Q2 Q3 Q1
    (by rw [g1]; norm_num) (by rw [g2]; norm_num) (by rw [g4]; norm_num)

end

end SixQubit.Orbit49
