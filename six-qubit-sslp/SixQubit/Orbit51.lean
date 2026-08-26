import Mathlib

import SS.FullKL
import SixQubit.Common
import SixQubit.Triangle

/-!
# Six-qubit no-go for moment orbit 51

Orbit 51 of `six_qubit_sslp.tex`: q = 6, angle vector a = (1, 1, 2, 3, 3, 4),
residues 0 and 2.  The two fibers are complementary, so the top fiber is
indexed by bitwise complement of the bottom one.

The weight-one masks `X_3` and `X_6` each have four incidences and rank three,
so each pins its incidence vector to a one-dimensional kernel spanned by
`(1, -1, -1, 1)`.  Taking `normSq` of the two resulting relations gives the two
moment equations `p1 r8 = p0 r9` and `p3 r8 = p2 r9`, which collapse the
three-dimensional polytope to `p0 = p1 = p2 = p3 = 1/12`, `p8 = p9 = 1/6`.

The paper then divides by amplitudes to synchronize the phase ratios of the two
anchors.  This module never divides.  The masks `e1+e4` and `e1+e5` give four
reciprocal relations on the pair `{6, 7}`, and eliminating between them gives
identically

```
d z6 * (star (c y8) * d z9 - star (c y9) * d z8) = 0 ,
d z7 * (star (c y8) * d z9 - star (c y9) * d z8) = 0 ;
```

the moment system forces `normSq (d z6) + normSq (d z7) = 1/6`, so one of the
two factors is nonzero and the synchronisation `star (c y8) * d z9 = star (c y9) * d z8`
holds outright.  With it, the two kernel relations and the rank-one mask
`e1+e2` become the three pure quadrics `c0 c9 + c1 c8 = 0`, `c2 c9 + c3 c8 = 0`,
`c0 c3 + c1 c2 = 0`, and
`SixQubit.Triangle.pair_contradiction_of_normSq` closes the mixed pair triangle.

Everything computational is decided by the Lean kernel; `native_decide`
is not used.
-/

namespace SixQubit.Orbit51

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

/-! ## The two fibers -/

def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]

def y0 : SS.BitString 6 := bs false false false false false false  -- 000000
def y1 : SS.BitString 6 := bs false false false true  true  false  -- 000110
def y2 : SS.BitString 6 := bs false false true  false false true   -- 001001
def y3 : SS.BitString 6 := bs false false true  true  true  true   -- 001111
def y4 : SS.BitString 6 := bs false true  true  false true  false  -- 011010
def y5 : SS.BitString 6 := bs false true  true  true  false false  -- 011100
def y6 : SS.BitString 6 := bs true  false true  false true  false  -- 101010
def y7 : SS.BitString 6 := bs true  false true  true  false false  -- 101100
def y8 : SS.BitString 6 := bs true  true  false false false true   -- 110001
def y9 : SS.BitString 6 := bs true  true  false true  true  true   -- 110111

def z0 : SS.BitString 6 := bs true  true  true  true  true  true   -- 111111
def z1 : SS.BitString 6 := bs true  true  true  false false true   -- 111001
def z2 : SS.BitString 6 := bs true  true  false true  true  false  -- 110110
def z3 : SS.BitString 6 := bs true  true  false false false false  -- 110000
def z4 : SS.BitString 6 := bs true  false false true  false true   -- 100101
def z5 : SS.BitString 6 := bs true  false false false true  true   -- 100011
def z6 : SS.BitString 6 := bs false true  false true  false true   -- 010101
def z7 : SS.BitString 6 := bs false true  false false true  true   -- 010011
def z8 : SS.BitString 6 := bs false false true  true  true  false  -- 001110
def z9 : SS.BitString 6 := bs false false true  false false false  -- 001000

def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9}
def S1 : Finset (SS.BitString 6) := {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9}

def av : Fin 6 -> ZMod 6 := ![1, 1, 2, 3, 3, 4]

theorem S0_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 0) = S0 := by
  decide

theorem S1_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 2) = S1 := by
  decide

/-! ## Flip masks, dressings, incidences and signs -/

def ef0 : SS.BitString 6 := bs false false true  false false false  -- 001000
def ef1 : SS.BitString 6 := bs false false false false false true   -- 000001
def ef2 : SS.BitString 6 := bs true  true  false false false false  -- 110000
def ef3 : SS.BitString 6 := bs true  false false true  false false  -- 100100
def ef4 : SS.BitString 6 := bs true  false false false true  false  -- 100010

def w0 : SS.BitString 6 := bs false false false false false false  -- 000000
def w1 : SS.BitString 6 := bs true  false false false false false  -- 100000
def w2 : SS.BitString 6 := bs false false false true  false false  -- 000100
def w3 : SS.BitString 6 := bs false false false false true  false  -- 000010

theorem incidence_ef0 :
    S1.filter (fun y => SS.bxor y ef0 ∈ S0) = {z0, z1, z8, z9} := by decide
theorem flip_ef0_z0 : SS.bxor z0 ef0 = y9 := by decide
theorem flip_ef0_z1 : SS.bxor z1 ef0 = y8 := by decide
theorem flip_ef0_z8 : SS.bxor z8 ef0 = y1 := by decide
theorem flip_ef0_z9 : SS.bxor z9 ef0 = y0 := by decide
theorem incidence_ef1 :
    S1.filter (fun y => SS.bxor y ef1 ∈ S0) = {z2, z3, z8, z9} := by decide
theorem flip_ef1_z2 : SS.bxor z2 ef1 = y9 := by decide
theorem flip_ef1_z3 : SS.bxor z3 ef1 = y8 := by decide
theorem flip_ef1_z8 : SS.bxor z8 ef1 = y3 := by decide
theorem flip_ef1_z9 : SS.bxor z9 ef1 = y2 := by decide
theorem incidence_ef2 :
    S1.filter (fun y => SS.bxor y ef2 ∈ S0) = {z0, z1, z2, z3} := by decide
theorem flip_ef2_z0 : SS.bxor z0 ef2 = y3 := by decide
theorem flip_ef2_z1 : SS.bxor z1 ef2 = y2 := by decide
theorem flip_ef2_z2 : SS.bxor z2 ef2 = y1 := by decide
theorem flip_ef2_z3 : SS.bxor z3 ef2 = y0 := by decide
theorem incidence_ef3 :
    S1.filter (fun y => SS.bxor y ef3 ∈ S0) = {z6, z7, z8, z9} := by decide
theorem flip_ef3_z6 : SS.bxor z6 ef3 = y8 := by decide
theorem flip_ef3_z7 : SS.bxor z7 ef3 = y9 := by decide
theorem flip_ef3_z8 : SS.bxor z8 ef3 = y6 := by decide
theorem flip_ef3_z9 : SS.bxor z9 ef3 = y7 := by decide
theorem incidence_ef4 :
    S1.filter (fun y => SS.bxor y ef4 ∈ S0) = {z6, z7, z8, z9} := by decide
theorem flip_ef4_z6 : SS.bxor z6 ef4 = y9 := by decide
theorem flip_ef4_z7 : SS.bxor z7 ef4 = y8 := by decide
theorem flip_ef4_z8 : SS.bxor z8 ef4 = y7 := by decide
theorem flip_ef4_z9 : SS.bxor z9 ef4 = y6 := by decide

theorem sg_w0_z0 : SS.bdot w0 z0 = false := by decide
theorem sg_w0_z1 : SS.bdot w0 z1 = false := by decide
theorem sg_w0_z8 : SS.bdot w0 z8 = false := by decide
theorem sg_w0_z9 : SS.bdot w0 z9 = false := by decide
theorem sg_w1_z0 : SS.bdot w1 z0 = true := by decide
theorem sg_w1_z1 : SS.bdot w1 z1 = true := by decide
theorem sg_w1_z8 : SS.bdot w1 z8 = false := by decide
theorem sg_w1_z9 : SS.bdot w1 z9 = false := by decide
theorem sg_w2_z0 : SS.bdot w2 z0 = true := by decide
theorem sg_w2_z1 : SS.bdot w2 z1 = false := by decide
theorem sg_w2_z8 : SS.bdot w2 z8 = true := by decide
theorem sg_w2_z9 : SS.bdot w2 z9 = false := by decide
theorem sg_w0_z2 : SS.bdot w0 z2 = false := by decide
theorem sg_w0_z3 : SS.bdot w0 z3 = false := by decide
theorem sg_w1_z2 : SS.bdot w1 z2 = true := by decide
theorem sg_w1_z3 : SS.bdot w1 z3 = true := by decide
theorem sg_w2_z2 : SS.bdot w2 z2 = true := by decide
theorem sg_w2_z3 : SS.bdot w2 z3 = false := by decide
theorem sg_w0_z6 : SS.bdot w0 z6 = false := by decide
theorem sg_w0_z7 : SS.bdot w0 z7 = false := by decide
theorem sg_w2_z6 : SS.bdot w2 z6 = true := by decide
theorem sg_w2_z7 : SS.bdot w2 z7 = false := by decide
theorem sg_w3_z6 : SS.bdot w3 z6 = false := by decide
theorem sg_w3_z7 : SS.bdot w3 z7 = true := by decide
theorem sg_w3_z8 : SS.bdot w3 z8 = true := by decide
theorem sg_w3_z9 : SS.bdot w3 z9 = false := by decide

/-! ## The moment system -/

/-- The two normalizations, the twenty-one moment equalities, and the
nonnegativity of every probability. -/
structure MomentSystem (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Real) : Prop where
  n0 : q0 + q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 + q9 = 1
  n1 : r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 = 1
  m1 : q6 + q7 + q8 + q9 = r0 + r1 + r2 + r3 + r4 + r5
  m2 : q4 + q5 + q8 + q9 = r0 + r1 + r2 + r3 + r6 + r7
  m3 : q2 + q3 + q4 + q5 + q6 + q7 = r0 + r1 + r8 + r9
  m4 : q1 + q3 + q5 + q7 + q9 = r0 + r2 + r4 + r6 + r8
  m5 : q1 + q3 + q4 + q6 + q9 = r0 + r2 + r5 + r7 + r8
  m6 : q2 + q3 + q8 + q9 = r0 + r1 + r4 + r5 + r6 + r7
  m12 : q8 + q9 = r0 + r1 + r2 + r3
  m13 : q6 + q7 = r0 + r1
  m14 : q7 + q9 = r0 + r2 + r4
  m15 : q6 + q9 = r0 + r2 + r5
  m16 : q8 + q9 = r0 + r1 + r4 + r5
  m23 : q4 + q5 = r0 + r1
  m24 : q5 + q9 = r0 + r2 + r6
  m25 : q4 + q9 = r0 + r2 + r7
  m26 : q8 + q9 = r0 + r1 + r6 + r7
  m34 : q3 + q5 + q7 = r0 + r8
  m35 : q3 + q4 + q6 = r0 + r8
  m36 : q2 + q3 = r0 + r1
  m45 : q1 + q3 + q9 = r0 + r2 + r8
  m46 : q3 + q9 = r0 + r4 + r6
  m56 : q3 + q9 = r0 + r5 + r7

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

/-- The two weight-one kernel relations pin the polytope: four of the ten
bottom probabilities become `1/12` and the anchor pair becomes `1/6`. -/
theorem MomentSystem.pinned {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Real}
    (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9)
    (e1 : q1 * r8 = q0 * r9)
    (e2 : q3 * r8 = q2 * r9) :
    q1 = 1/12 ∧ q2 = 1/12 ∧ q8 = 1/6 ∧ r8 = 1/6 ∧ r9 = 1/6
      ∧ r6 + r7 = 1/6 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, m12, m13, m14, m15, m16, m23, m24, m25, m26, m34, m35, m36, m45, m46, m56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9⟩ := h
  have hq1 : q1 = 1/6 - q0 := by linarith
  have hq3 : q3 = 1/6 - q2 := by linarith
  have h8 : r8 = 1/3 - q0 - q2 := by linarith
  have h9 : r9 = q0 + q2 := by linarith
  rw [hq1, h8, h9] at e1
  rw [hq3, h8, h9] at e2
  have t1 : 9 * q0 + 3 * q2 = 1 := by linear_combination (-18 : Real) * e1
  have t2 : 3 * q0 + 9 * q2 = 1 := by linear_combination (-18 : Real) * e2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-! ## The Walsh expansions -/

def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),
      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

theorem ex_ef0_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w0 = star (c y9) * d z0 + star (c y8) * d z1 + star (c y1) * d z8 + star (c y0) * d z9 := by
  unfold offSum
  rw [incidence_ef0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef0_z0, flip_ef0_z1, flip_ef0_z8, flip_ef0_z9]
  simp only [sg_w0_z0, sg_w0_z1, sg_w0_z8, sg_w0_z9, SixQubit.signMul_false]
  try ring

theorem ex_ef0_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w1 = - star (c y9) * d z0 - star (c y8) * d z1 + star (c y1) * d z8 + star (c y0) * d z9 := by
  unfold offSum
  rw [incidence_ef0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef0_z0, flip_ef0_z1, flip_ef0_z8, flip_ef0_z9]
  simp only [sg_w1_z0, sg_w1_z1, sg_w1_z8, sg_w1_z9, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef0_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w2 = - star (c y9) * d z0 + star (c y8) * d z1 - star (c y1) * d z8 + star (c y0) * d z9 := by
  unfold offSum
  rw [incidence_ef0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef0_z0, flip_ef0_z1, flip_ef0_z8, flip_ef0_z9]
  simp only [sg_w2_z0, sg_w2_z1, sg_w2_z8, sg_w2_z9, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef1_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w0 = star (c y9) * d z2 + star (c y8) * d z3 + star (c y3) * d z8 + star (c y2) * d z9 := by
  unfold offSum
  rw [incidence_ef1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef1_z2, flip_ef1_z3, flip_ef1_z8, flip_ef1_z9]
  simp only [sg_w0_z2, sg_w0_z3, sg_w0_z8, sg_w0_z9, SixQubit.signMul_false]
  try ring

theorem ex_ef1_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w1 = - star (c y9) * d z2 - star (c y8) * d z3 + star (c y3) * d z8 + star (c y2) * d z9 := by
  unfold offSum
  rw [incidence_ef1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef1_z2, flip_ef1_z3, flip_ef1_z8, flip_ef1_z9]
  simp only [sg_w1_z2, sg_w1_z3, sg_w1_z8, sg_w1_z9, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef1_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w2 = - star (c y9) * d z2 + star (c y8) * d z3 - star (c y3) * d z8 + star (c y2) * d z9 := by
  unfold offSum
  rw [incidence_ef1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef1_z2, flip_ef1_z3, flip_ef1_z8, flip_ef1_z9]
  simp only [sg_w2_z2, sg_w2_z3, sg_w2_z8, sg_w2_z9, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef2_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w0 = star (c y3) * d z0 + star (c y2) * d z1 + star (c y1) * d z2 + star (c y0) * d z3 := by
  unfold offSum
  rw [incidence_ef2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef2_z0, flip_ef2_z1, flip_ef2_z2, flip_ef2_z3]
  simp only [sg_w0_z0, sg_w0_z1, sg_w0_z2, sg_w0_z3, SixQubit.signMul_false]
  try ring

theorem ex_ef3_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w0 = star (c y8) * d z6 + star (c y9) * d z7 + star (c y6) * d z8 + star (c y7) * d z9 := by
  unfold offSum
  rw [incidence_ef3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef3_z6, flip_ef3_z7, flip_ef3_z8, flip_ef3_z9]
  simp only [sg_w0_z6, sg_w0_z7, sg_w0_z8, sg_w0_z9, SixQubit.signMul_false]
  try ring

theorem ex_ef3_w2 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w2 = - star (c y8) * d z6 + star (c y9) * d z7 - star (c y6) * d z8 + star (c y7) * d z9 := by
  unfold offSum
  rw [incidence_ef3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef3_z6, flip_ef3_z7, flip_ef3_z8, flip_ef3_z9]
  simp only [sg_w2_z6, sg_w2_z7, sg_w2_z8, sg_w2_z9, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef4_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w0 = star (c y9) * d z6 + star (c y8) * d z7 + star (c y7) * d z8 + star (c y6) * d z9 := by
  unfold offSum
  rw [incidence_ef4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef4_z6, flip_ef4_z7, flip_ef4_z8, flip_ef4_z9]
  simp only [sg_w0_z6, sg_w0_z7, sg_w0_z8, sg_w0_z9, SixQubit.signMul_false]
  try ring

theorem ex_ef4_w3 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w3 = star (c y9) * d z6 - star (c y8) * d z7 - star (c y7) * d z8 + star (c y6) * d z9 := by
  unfold offSum
  rw [incidence_ef4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef4_z6, flip_ef4_z7, flip_ef4_z8, flip_ef4_z9]
  simp only [sg_w3_z6, sg_w3_z7, sg_w3_z8, sg_w3_z9, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

/-! ## The no-go -/

/-- **Orbit 51 is impossible.** -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)))
    (h0 : offSum c d ef0 w0 = 0)
    (h1 : offSum c d ef0 w1 = 0)
    (h2 : offSum c d ef0 w2 = 0)
    (h3 : offSum c d ef1 w0 = 0)
    (h4 : offSum c d ef1 w1 = 0)
    (h5 : offSum c d ef1 w2 = 0)
    (h6 : offSum c d ef2 w0 = 0)
    (h7 : offSum c d ef3 w0 = 0)
    (h8 : offSum c d ef3 w2 = 0)
    (h9 : offSum c d ef4 w0 = 0)
    (h10 : offSum c d ef4 w3 = 0)
    : False := by
  rw [ex_ef0_w0] at h0
  rw [ex_ef0_w1] at h1
  rw [ex_ef0_w2] at h2
  rw [ex_ef1_w0] at h3
  rw [ex_ef1_w1] at h4
  rw [ex_ef1_w2] at h5
  rw [ex_ef2_w0] at h6
  rw [ex_ef3_w0] at h7
  rw [ex_ef3_w2] at h8
  rw [ex_ef4_w0] at h9
  rw [ex_ef4_w3] at h10
  have rA1 : star (c y9) * d z0 - star (c y0) * d z9 = 0 := by
    linear_combination (-1/2 : ℂ) * h1 + (-1/2 : ℂ) * h2
  have rA2 : star (c y8) * d z1 + star (c y0) * d z9 = 0 := by
    linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h2
  have rA3 : star (c y1) * d z8 + star (c y0) * d z9 = 0 := by
    linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1
  have rB1 : star (c y9) * d z2 - star (c y2) * d z9 = 0 := by
    linear_combination (-1/2 : ℂ) * h4 + (-1/2 : ℂ) * h5
  have rB2 : star (c y8) * d z3 + star (c y2) * d z9 = 0 := by
    linear_combination (1/2 : ℂ) * h3 + (1/2 : ℂ) * h5
  have rB3 : star (c y3) * d z8 + star (c y2) * d z9 = 0 := by
    linear_combination (1/2 : ℂ) * h3 + (1/2 : ℂ) * h4
  have rM : star (c y3) * d z0 + star (c y2) * d z1 + star (c y1) * d z2 + star (c y0) * d z3 = 0 := by
    linear_combination (1 : ℂ) * h6
  have rC1 : star (c y8) * d z6 + star (c y6) * d z8 = 0 := by
    linear_combination (1/2 : ℂ) * h7 + (-1/2 : ℂ) * h8
  have rC2 : star (c y9) * d z7 + star (c y7) * d z9 = 0 := by
    linear_combination (1/2 : ℂ) * h7 + (1/2 : ℂ) * h8
  have rD1 : star (c y9) * d z6 + star (c y6) * d z9 = 0 := by
    linear_combination (1/2 : ℂ) * h9 + (1/2 : ℂ) * h10
  have rD2 : star (c y8) * d z7 + star (c y7) * d z8 = 0 := by
    linear_combination (1/2 : ℂ) * h9 + (-1/2 : ℂ) * h10
  have E1 : Complex.normSq (c y1) * Complex.normSq (d z8)
      = Complex.normSq (c y0) * Complex.normSq (d z9) := by
    have hne : star (c y1) * d z8 = -(star (c y0) * d z9) := by
      linear_combination rA3
    have hsq := congrArg Complex.normSq hne
    simpa [Complex.normSq_mul] using hsq
  have E2 : Complex.normSq (c y3) * Complex.normSq (d z8)
      = Complex.normSq (c y2) * Complex.normSq (d z9) := by
    have hne : star (c y3) * d z8 = -(star (c y2) * d z9) := by
      linear_combination rB3
    have hsq := congrArg Complex.normSq hne
    simpa [Complex.normSq_mul] using hsq
  obtain ⟨g1, g2, g8, gr8, gr9, g67⟩ := hm.pinned E1 E2
  have hz8 : d z8 ≠ 0 := Complex.normSq_pos.mp (by rw [gr8]; norm_num)
  have hz9 : d z9 ≠ 0 := Complex.normSq_pos.mp (by rw [gr9]; norm_num)
  have hc8 : star (c y8) ≠ 0 :=
    star_ne_zero.mpr (Complex.normSq_pos.mp (by rw [g8]; norm_num))
  have kw6 : d z6 * (star (c y8) * d z9 - star (c y9) * d z8) = 0 := by
    linear_combination (d z9) * rC1 - (d z8) * rD1
  have kw7 : d z7 * (star (c y8) * d z9 - star (c y9) * d z8) = 0 := by
    linear_combination (d z9) * rD2 - (d z8) * rC2
  have hW : star (c y8) * d z9 - star (c y9) * d z8 = 0 := by
    rcases eq_or_ne (d z6) 0 with h6 | h6
    · have h7 : d z7 ≠ 0 := by
        refine Complex.normSq_pos.mp ?_
        have hz6 : Complex.normSq (d z6) = 0 := by rw [h6]; simp
        have hnn := Complex.normSq_nonneg (d z7)
        linarith
      exact (mul_eq_zero.mp kw7).resolve_left h7
    · exact (mul_eq_zero.mp kw6).resolve_left h6
  have G1 : star (c y0) * star (c y9) + star (c y1) * star (c y8) = 0 := by
    have key : (star (c y0) * star (c y9) + star (c y1) * star (c y8))
        * d z8 = 0 := by
      linear_combination (star (c y8)) * rA3 - (star (c y0)) * hW
    exact (mul_eq_zero.mp key).resolve_right hz8
  have G2 : star (c y2) * star (c y9) + star (c y3) * star (c y8) = 0 := by
    have key : (star (c y2) * star (c y9) + star (c y3) * star (c y8))
        * d z8 = 0 := by
      linear_combination (star (c y8)) * rB3 - (star (c y2)) * hW
    exact (mul_eq_zero.mp key).resolve_right hz8
  have G3 : star (c y0) * star (c y3) + star (c y1) * star (c y2) = 0 := by
    have key : (star (c y0) * star (c y3) + star (c y1) * star (c y2))
        * (star (c y8) * d z9) = 0 := by
      linear_combination (star (c y8) * star (c y9) / 2) * rM
        - (star (c y8) * star (c y3) / 2) * rA1
        - (star (c y9) * star (c y2) / 2) * rA2
        + (star (c y9) * star (c y2) / 2) * rA3
        - (star (c y8) * star (c y1) / 2) * rB1
        - (star (c y9) * star (c y0) / 2) * rB2
        + (star (c y9) * star (c y0) / 2) * rB3
        + ((star (c y0) * star (c y3) + star (c y1) * star (c y2)) / 2) * hW
    exact (mul_eq_zero.mp key).resolve_right (mul_ne_zero hc8 hz9)
  have H1 : c y0 * c y9 + c y1 * c y8 = 0 := by
    have hst := congrArg star G1
    simp only [star_add, star_mul, star_star, star_zero] at hst
    linear_combination hst
  have H2 : c y2 * c y9 + c y3 * c y8 = 0 := by
    have hst := congrArg star G2
    simp only [star_add, star_mul, star_star, star_zero] at hst
    linear_combination hst
  have H3 : c y0 * c y3 + c y1 * c y2 = 0 := by
    have hst := congrArg star G3
    simp only [star_add, star_mul, star_star, star_zero] at hst
    linear_combination hst
  exact SixQubit.Triangle.pair_contradiction_of_normSq H1 H2 H3
    (by rw [g1]; norm_num) (by rw [g2]; norm_num) (by rw [g8]; norm_num)

end

end SixQubit.Orbit51
