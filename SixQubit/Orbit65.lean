import Mathlib

import SS.FullKL
import SixQubit.Common
import SixQubit.Triangle

/-!
# Six-qubit no-go for moment orbit 65

Orbit 65 of `six_qubit_sslp.tex`: q = 8, angle vector
a = (1, 2, 2, 3, 4, 5).  The projective order is m = 8, so the residue that has to be
excluded is delta = q/m = 1: `S0` is the residue-0 fiber and `S1` the
residue-1 fiber, and the two are complementary.

The moment polytope is positive dimensional here, so the probabilities
are not individually pinned.  What the exact linear program does give is
a uniform positive lower bound on three of them,
  q2 >= 1/16,   q4 >= 3/16,   q5 >= 1/8,
valid at every point of the polytope; `linarith` reproves each bound from
the moment rows and nonnegativity.  Each of the three pairs carries a
reciprocal flip relation, so
`SixQubit.Triangle.contradiction_of_normSq` closes the odd triangle
without any division.

Everything computational is decided by the Lean kernel; `native_decide`
is not used.
-/

namespace SixQubit.Orbit65

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

/-! ## The two fibers -/

def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]

def y0 : SS.BitString 6 := bs false false false false false false  -- 000000
def y1 : SS.BitString 6 := bs false false false true  false true   -- 000101
def y2 : SS.BitString 6 := bs false true  true  false true  false  -- 011010
def y3 : SS.BitString 6 := bs false true  true  true  true  true   -- 011111
def y4 : SS.BitString 6 := bs true  false false true  true  false  -- 100110
def y5 : SS.BitString 6 := bs true  false true  false false true   -- 101001
def y6 : SS.BitString 6 := bs true  true  false false false true   -- 110001
def y7 : SS.BitString 6 := bs true  true  true  true  false false  -- 111100

def z0 : SS.BitString 6 := bs false false false false true  true   -- 000011
def z1 : SS.BitString 6 := bs false false true  true  true  false  -- 001110
def z2 : SS.BitString 6 := bs false true  false true  true  false  -- 010110
def z3 : SS.BitString 6 := bs false true  true  false false true   -- 011001
def z4 : SS.BitString 6 := bs true  false false false false false  -- 100000
def z5 : SS.BitString 6 := bs true  false false true  false true   -- 100101
def z6 : SS.BitString 6 := bs true  true  true  false true  false  -- 111010
def z7 : SS.BitString 6 := bs true  true  true  true  true  true   -- 111111

def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6, y7}
def S1 : Finset (SS.BitString 6) := {z0, z1, z2, z3, z4, z5, z6, z7}

def av : Fin 6 -> ZMod 8 := ![1, 2, 2, 3, 4, 5]

theorem S0_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 0) = S0 := by
  decide

theorem S1_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 1) = S1 := by
  decide

/-! ## Flip masks, incidences and signs -/

def ef0 : SS.BitString 6 := bs false false false false true  true   -- 000011
def ef1 : SS.BitString 6 := bs false false true  true  false false  -- 001100
def ef2 : SS.BitString 6 := bs true  true  false false false false  -- 110000
def w0 : SS.BitString 6 := bs false false false false false false  -- 000000
def w1 : SS.BitString 6 := bs false false false false true  false  -- 000010

theorem incidence_ef0 :
    S1.filter (fun y => SS.bxor y ef0 ∈ S0) = {z0, z3, z5, z7} := by decide
theorem flip_ef0_0 : SS.bxor z0 ef0 = y0 := by decide
theorem flip_ef0_3 : SS.bxor z3 ef0 = y2 := by decide
theorem flip_ef0_5 : SS.bxor z5 ef0 = y4 := by decide
theorem flip_ef0_7 : SS.bxor z7 ef0 = y7 := by decide
theorem sg_ef0_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg_ef0_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg_ef0_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg_ef0_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg_ef0_w1_0 : SS.bdot w1 z0 = true := by decide
theorem sg_ef0_w1_3 : SS.bdot w1 z3 = false := by decide
theorem sg_ef0_w1_5 : SS.bdot w1 z5 = false := by decide
theorem sg_ef0_w1_7 : SS.bdot w1 z7 = true := by decide

theorem incidence_ef1 :
    S1.filter (fun y => SS.bxor y ef1 ∈ S0) = {z2, z5} := by decide
theorem flip_ef1_2 : SS.bxor z2 ef1 = y2 := by decide
theorem flip_ef1_5 : SS.bxor z5 ef1 = y5 := by decide
theorem sg_ef1_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg_ef1_w0_5 : SS.bdot w0 z5 = false := by decide

theorem incidence_ef2 :
    S1.filter (fun y => SS.bxor y ef2 ∈ S0) = {z2, z3} := by decide
theorem flip_ef2_2 : SS.bxor z2 ef2 = y4 := by decide
theorem flip_ef2_3 : SS.bxor z3 ef2 = y5 := by decide
theorem sg_ef2_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg_ef2_w0_3 : SS.bdot w0 z3 = false := by decide

/-! ## The moment system -/

/-- The two normalizations, the twenty-one moment equalities, and the
nonnegativity of every probability. -/
structure MomentSystem (q0 q1 q2 q3 q4 q5 q6 q7 r0 r1 r2 r3 r4 r5 r6 r7 : Real) : Prop where
  n0 : q0 + q1 + q2 + q3 + q4 + q5 + q6 + q7 = 1
  n1 : r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 = 1
  m1 : q4 + q5 + q6 + q7 = r4 + r5 + r6 + r7
  m2 : q2 + q3 + q6 + q7 = r2 + r3 + r6 + r7
  m3 : q2 + q3 + q5 + q7 = r1 + r3 + r6 + r7
  m4 : q1 + q3 + q4 + q7 = r1 + r2 + r5 + r7
  m5 : q2 + q3 + q4 = r0 + r1 + r2 + r6 + r7
  m6 : q1 + q3 + q5 + q6 = r0 + r3 + r5 + r7
  m12 : q6 + q7 = r6 + r7
  m13 : q5 + q7 = r6 + r7
  m14 : q4 + q7 = r5 + r7
  m15 : q4 = r6 + r7
  m16 : q5 + q6 = r5 + r7
  m23 : q2 + q3 + q7 = r3 + r6 + r7
  m24 : q3 + q7 = r2 + r7
  m25 : q2 + q3 = r2 + r6 + r7
  m26 : q3 + q6 = r3 + r7
  m34 : q3 + q7 = r1 + r7
  m35 : q2 + q3 = r1 + r6 + r7
  m36 : q3 + q5 = r3 + r7
  m45 : q3 + q4 = r1 + r2 + r7
  m46 : q1 + q3 = r5 + r7
  m56 : q3 = r0 + r7

  nq0 : 0 ≤ q0
  nq1 : 0 ≤ q1
  nq2 : 0 ≤ q2
  nq3 : 0 ≤ q3
  nq4 : 0 ≤ q4
  nq5 : 0 ≤ q5
  nq6 : 0 ≤ q6
  nq7 : 0 ≤ q7
  nr0 : 0 ≤ r0
  nr1 : 0 ≤ r1
  nr2 : 0 ≤ r2
  nr3 : 0 ≤ r3
  nr4 : 0 ≤ r4
  nr5 : 0 ≤ r5
  nr6 : 0 ≤ r6
  nr7 : 0 ≤ r7

/-- Each triangle vertex is bounded away from zero over the whole moment
polytope, and the top probability at the complementary string matches. -/
theorem MomentSystem.facts {q0 q1 q2 q3 q4 q5 q6 q7 r0 r1 r2 r3 r4 r5 r6 r7 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 r0 r1 r2 r3 r4 r5 r6 r7) :
    (1/16 : Real) ≤ q2 ∧ (3/16 : Real) ≤ q4 ∧ (1/8 : Real) ≤ q5 ∧ q2 = r5 ∧ q4 = r3 ∧ q5 = r2 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, m12, m13, m14, m15, m16, m23, m24, m25, m26, m34, m35, m36, m45, m46, m56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- The three triangle probabilities, bounded below by the linear program. -/
theorem MomentSystem.endpoints {q0 q1 q2 q3 q4 q5 q6 q7 r0 r1 r2 r3 r4 r5 r6 r7 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 r0 r1 r2 r3 r4 r5 r6 r7) :
    (1/16 : Real) ≤ q2 ∧ (3/16 : Real) ≤ q4 ∧ (1/8 : Real) ≤ q5 := by
  obtain ⟨e2, e4, e5, _, _, _⟩ := h.facts
  exact ⟨e2, e4, e5⟩

/-- Hence all three are strictly positive. -/
theorem MomentSystem.endpoints_pos {q0 q1 q2 q3 q4 q5 q6 q7 r0 r1 r2 r3 r4 r5 r6 r7 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 r0 r1 r2 r3 r4 r5 r6 r7) :
    0 < q2 ∧ 0 < q4 ∧ 0 < q5 := by
  obtain ⟨e2, e4, e5⟩ := h.endpoints
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-! ## The reciprocal relations -/

def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),
      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

theorem ex_ef0_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w0 = star (c y0) * d z0 + star (c y2) * d z3 + star (c y4) * d z5 + star (c y7) * d z7 := by
  unfold offSum
  rw [incidence_ef0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef0_0, flip_ef0_3, flip_ef0_5, flip_ef0_7]
  simp only [sg_ef0_w0_0, sg_ef0_w0_3, sg_ef0_w0_5, sg_ef0_w0_7, SixQubit.signMul_false]
  try ring

theorem ex_ef0_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w1 = - star (c y0) * d z0 + star (c y2) * d z3 + star (c y4) * d z5 - star (c y7) * d z7 := by
  unfold offSum
  rw [incidence_ef0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef0_0, flip_ef0_3, flip_ef0_5, flip_ef0_7]
  simp only [sg_ef0_w1_0, sg_ef0_w1_3, sg_ef0_w1_5, sg_ef0_w1_7, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef1_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w0 = star (c y2) * d z2 + star (c y5) * d z5 := by
  unfold offSum
  rw [incidence_ef1]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef1_2, flip_ef1_5]
  simp only [sg_ef1_w0_2, sg_ef1_w0_5, SixQubit.signMul_false]
  try ring

theorem ex_ef2_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w0 = star (c y4) * d z2 + star (c y5) * d z3 := by
  unfold offSum
  rw [incidence_ef2]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef2_2, flip_ef2_3]
  simp only [sg_ef2_w0_2, sg_ef2_w0_3, SixQubit.signMul_false]
  try ring

/-! ## The no-go -/

/-- The odd triangle eliminates to a single product, with no division and
no nonvanishing side condition on the way in. -/
theorem target_zero (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef0 w0 = 0)
    (h1 : offSum c d ef0 w1 = 0)
    (h2 : offSum c d ef1 w0 = 0)
    (h3 : offSum c d ef2 w0 = 0) :
    star (c y5) * d z5 * d z3 = 0 := by
  rw [ex_ef0_w0] at h0
  rw [ex_ef0_w1] at h1
  rw [ex_ef1_w0] at h2
  rw [ex_ef2_w0] at h3
  have relo_2_4 : star (c y2) * d z3 + star (c y4) * d z5 = 0 := by
    linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1
  have relo_2_5 : star (c y2) * d z2 + star (c y5) * d z5 = 0 := by
    linear_combination (1 : ℂ) * h2
  have relo_4_5 : star (c y4) * d z2 + star (c y5) * d z3 = 0 := by
    linear_combination (1 : ℂ) * h3
  exact SixQubit.Triangle.prod_eq_zero relo_2_4 relo_2_5 relo_4_5

/-- **Orbit 65 is impossible.** -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)))
    (h0 : offSum c d ef0 w0 = 0)
    (h1 : offSum c d ef0 w1 = 0)
    (h2 : offSum c d ef1 w0 = 0)
    (h3 : offSum c d ef2 w0 = 0)
    : False := by
  have key := target_zero c d h0 h1 h2 h3
  obtain ⟨_b2, _b4, _b5, mt2, mt4, _mt5⟩ := hm.facts
  obtain ⟨pos2, pos4, pos5⟩ := hm.endpoints_pos
  have post2 : 0 < Complex.normSq (d z5) := by rw [← mt2]; exact pos2
  have post4 : 0 < Complex.normSq (d z3) := by rw [← mt4]; exact pos4
  rcases mul_eq_zero.mp key with hx | hx
  · rcases mul_eq_zero.mp hx with hy | hy
    · have hk : c y5 = 0 := by simpa using congrArg star hy
      rw [hk, Complex.normSq_zero] at pos5
      norm_num at pos5
    · rw [hy, Complex.normSq_zero] at post2
      norm_num at post2
  · rw [hx, Complex.normSq_zero] at post4
    norm_num at post4

end

end SixQubit.Orbit65
