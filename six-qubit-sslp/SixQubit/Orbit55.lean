import Mathlib

import SS.FullKL
import SixQubit.Common
import SixQubit.Triangle

/-!
# Six-qubit no-go for moment orbit 55

Orbit 55 of `six_qubit_sslp.tex`: q = 6, angle vector
a = (1, 1, 2, 2, 3, 4).  The projective order is m = 6, so the residue that has to
be excluded is delta = q/m = 1: `S0` is the residue-0 fiber, `S1` the
residue-1 fiber, and the two are complementary.

The moment polytope is positive dimensional and no monomial is isolable,
so the argument runs in two stages.

* Index 9 is joined to 3, 4, 5, 6, 7, 8 by two-incidence flip masks; each gives a
  reciprocal relation pairing that leaf with the centre.
* Three further masks carry a four-edge relation supported on two
  reciprocal pairs of leaves.  Multiplying by `star (c y9)` and
  substituting the star relations collapses each one, without dividing,
  to a binomial times `d z1`, and `d z1` is nonzero because the moment
  polytope forces `1/6 <= r1`.

The three binomials are the hypotheses of
`SixQubit.Triangle.pair_contradiction`; the two magnitude consequences
and five exact LP bounds rule out every boundary escape in which one of
the three amplitudes it needs would vanish.

Everything computational is decided by the Lean kernel; `native_decide`
is not used.
-/

namespace SixQubit.Orbit55

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

/-! ## The two fibers -/

def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]

def y0 : SS.BitString 6 := bs false false false false false false  -- 000000
def y1 : SS.BitString 6 := bs false false false true  false true   -- 000101
def y2 : SS.BitString 6 := bs false false true  false false true   -- 001001
def y3 : SS.BitString 6 := bs false true  false true  true  false  -- 010110
def y4 : SS.BitString 6 := bs false true  true  false true  false  -- 011010
def y5 : SS.BitString 6 := bs false true  true  true  true  true   -- 011111
def y6 : SS.BitString 6 := bs true  false false true  true  false  -- 100110
def y7 : SS.BitString 6 := bs true  false true  false true  false  -- 101010
def y8 : SS.BitString 6 := bs true  false true  true  true  true   -- 101111
def y9 : SS.BitString 6 := bs true  true  false false false true   -- 110001
def y10 : SS.BitString 6 := bs true  true  true  true  false false  -- 111100

def z0 : SS.BitString 6 := bs false false false false true  true   -- 000011
def z1 : SS.BitString 6 := bs false false true  true  true  false  -- 001110
def z2 : SS.BitString 6 := bs false true  false false false false  -- 010000
def z3 : SS.BitString 6 := bs false true  false true  false true   -- 010101
def z4 : SS.BitString 6 := bs false true  true  false false true   -- 011001
def z5 : SS.BitString 6 := bs true  false false false false false  -- 100000
def z6 : SS.BitString 6 := bs true  false false true  false true   -- 100101
def z7 : SS.BitString 6 := bs true  false true  false false true   -- 101001
def z8 : SS.BitString 6 := bs true  true  false true  true  false  -- 110110
def z9 : SS.BitString 6 := bs true  true  true  false true  false  -- 111010
def z10 : SS.BitString 6 := bs true  true  true  true  true  true   -- 111111

def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10}
def S1 : Finset (SS.BitString 6) := {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10}

def av : Fin 6 -> ZMod 6 := ![1, 1, 2, 2, 3, 4]

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
def ef1 : SS.BitString 6 := bs false false false true  true  false  -- 000110
def ef2 : SS.BitString 6 := bs false false true  false true  false  -- 001010
def ef3 : SS.BitString 6 := bs false true  false false false true   -- 010001
def ef4 : SS.BitString 6 := bs false true  false true  false false  -- 010100
def ef5 : SS.BitString 6 := bs false true  true  false false false  -- 011000
def ef6 : SS.BitString 6 := bs true  false false false false true   -- 100001
def ef7 : SS.BitString 6 := bs true  false false true  false false  -- 100100
def ef8 : SS.BitString 6 := bs true  false true  false false false  -- 101000
def w0 : SS.BitString 6 := bs false false false false false false  -- 000000
def w1 : SS.BitString 6 := bs false false false false true  false  -- 000010

theorem incidence_ef0 :
    S1.filter (fun y => SS.bxor y ef0 ∈ S0) = {z0, z3, z4, z6, z7, z10} := by decide
theorem flip_ef0_0 : SS.bxor z0 ef0 = y0 := by decide
theorem flip_ef0_3 : SS.bxor z3 ef0 = y3 := by decide
theorem flip_ef0_4 : SS.bxor z4 ef0 = y4 := by decide
theorem flip_ef0_6 : SS.bxor z6 ef0 = y6 := by decide
theorem flip_ef0_7 : SS.bxor z7 ef0 = y7 := by decide
theorem flip_ef0_10 : SS.bxor z10 ef0 = y10 := by decide
theorem sg_ef0_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg_ef0_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg_ef0_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg_ef0_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg_ef0_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg_ef0_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg_ef0_w1_0 : SS.bdot w1 z0 = true := by decide
theorem sg_ef0_w1_3 : SS.bdot w1 z3 = false := by decide
theorem sg_ef0_w1_4 : SS.bdot w1 z4 = false := by decide
theorem sg_ef0_w1_6 : SS.bdot w1 z6 = false := by decide
theorem sg_ef0_w1_7 : SS.bdot w1 z7 = false := by decide
theorem sg_ef0_w1_10 : SS.bdot w1 z10 = true := by decide

theorem incidence_ef1 :
    S1.filter (fun y => SS.bxor y ef1 ∈ S0) = {z0, z2, z4, z5, z7, z9} := by decide
theorem flip_ef1_0 : SS.bxor z0 ef1 = y1 := by decide
theorem flip_ef1_2 : SS.bxor z2 ef1 = y3 := by decide
theorem flip_ef1_4 : SS.bxor z4 ef1 = y5 := by decide
theorem flip_ef1_5 : SS.bxor z5 ef1 = y6 := by decide
theorem flip_ef1_7 : SS.bxor z7 ef1 = y8 := by decide
theorem flip_ef1_9 : SS.bxor z9 ef1 = y10 := by decide
theorem sg_ef1_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg_ef1_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg_ef1_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg_ef1_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg_ef1_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg_ef1_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg_ef1_w1_0 : SS.bdot w1 z0 = true := by decide
theorem sg_ef1_w1_2 : SS.bdot w1 z2 = false := by decide
theorem sg_ef1_w1_4 : SS.bdot w1 z4 = false := by decide
theorem sg_ef1_w1_5 : SS.bdot w1 z5 = false := by decide
theorem sg_ef1_w1_7 : SS.bdot w1 z7 = false := by decide
theorem sg_ef1_w1_9 : SS.bdot w1 z9 = true := by decide

theorem incidence_ef2 :
    S1.filter (fun y => SS.bxor y ef2 ∈ S0) = {z0, z2, z3, z5, z6, z8} := by decide
theorem flip_ef2_0 : SS.bxor z0 ef2 = y2 := by decide
theorem flip_ef2_2 : SS.bxor z2 ef2 = y4 := by decide
theorem flip_ef2_3 : SS.bxor z3 ef2 = y5 := by decide
theorem flip_ef2_5 : SS.bxor z5 ef2 = y7 := by decide
theorem flip_ef2_6 : SS.bxor z6 ef2 = y8 := by decide
theorem flip_ef2_8 : SS.bxor z8 ef2 = y10 := by decide
theorem sg_ef2_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg_ef2_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg_ef2_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg_ef2_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg_ef2_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg_ef2_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg_ef2_w1_0 : SS.bdot w1 z0 = true := by decide
theorem sg_ef2_w1_2 : SS.bdot w1 z2 = false := by decide
theorem sg_ef2_w1_3 : SS.bdot w1 z3 = false := by decide
theorem sg_ef2_w1_5 : SS.bdot w1 z5 = false := by decide
theorem sg_ef2_w1_6 : SS.bdot w1 z6 = false := by decide
theorem sg_ef2_w1_8 : SS.bdot w1 z8 = true := by decide

theorem incidence_ef3 :
    S1.filter (fun y => SS.bxor y ef3 ∈ S0) = {z1, z5} := by decide
theorem flip_ef3_1 : SS.bxor z1 ef3 = y5 := by decide
theorem flip_ef3_5 : SS.bxor z5 ef3 = y9 := by decide
theorem sg_ef3_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg_ef3_w0_5 : SS.bdot w0 z5 = false := by decide

theorem incidence_ef4 :
    S1.filter (fun y => SS.bxor y ef4 ∈ S0) = {z1, z6} := by decide
theorem flip_ef4_1 : SS.bxor z1 ef4 = y4 := by decide
theorem flip_ef4_6 : SS.bxor z6 ef4 = y9 := by decide
theorem sg_ef4_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg_ef4_w0_6 : SS.bdot w0 z6 = false := by decide

theorem incidence_ef5 :
    S1.filter (fun y => SS.bxor y ef5 ∈ S0) = {z1, z7} := by decide
theorem flip_ef5_1 : SS.bxor z1 ef5 = y3 := by decide
theorem flip_ef5_7 : SS.bxor z7 ef5 = y9 := by decide
theorem sg_ef5_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg_ef5_w0_7 : SS.bdot w0 z7 = false := by decide

theorem incidence_ef6 :
    S1.filter (fun y => SS.bxor y ef6 ∈ S0) = {z1, z2} := by decide
theorem flip_ef6_1 : SS.bxor z1 ef6 = y8 := by decide
theorem flip_ef6_2 : SS.bxor z2 ef6 = y9 := by decide
theorem sg_ef6_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg_ef6_w0_2 : SS.bdot w0 z2 = false := by decide

theorem incidence_ef7 :
    S1.filter (fun y => SS.bxor y ef7 ∈ S0) = {z1, z3} := by decide
theorem flip_ef7_1 : SS.bxor z1 ef7 = y7 := by decide
theorem flip_ef7_3 : SS.bxor z3 ef7 = y9 := by decide
theorem sg_ef7_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg_ef7_w0_3 : SS.bdot w0 z3 = false := by decide

theorem incidence_ef8 :
    S1.filter (fun y => SS.bxor y ef8 ∈ S0) = {z1, z4} := by decide
theorem flip_ef8_1 : SS.bxor z1 ef8 = y6 := by decide
theorem flip_ef8_4 : SS.bxor z4 ef8 = y9 := by decide
theorem sg_ef8_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg_ef8_w0_4 : SS.bdot w0 z4 = false := by decide

/-! ## The moment system -/

/-- The two normalizations, the twenty-one moment equalities, and the
nonnegativity of every probability. -/
structure MomentSystem (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 : Real) : Prop where
  n0 : q0 + q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 + q9 + q10 = 1
  n1 : r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 = 1
  m1 : q6 + q7 + q8 + q9 + q10 = r5 + r6 + r7 + r8 + r9 + r10
  m2 : q3 + q4 + q5 + q9 + q10 = r2 + r3 + r4 + r8 + r9 + r10
  m3 : q2 + q4 + q5 + q7 + q8 + q10 = r1 + r4 + r7 + r9 + r10
  m4 : q1 + q3 + q5 + q6 + q8 + q10 = r1 + r3 + r6 + r8 + r10
  m5 : q3 + q4 + q5 + q6 + q7 + q8 = r0 + r1 + r8 + r9 + r10
  m6 : q1 + q2 + q5 + q8 + q9 = r0 + r3 + r4 + r6 + r7 + r10
  m12 : q9 + q10 = r8 + r9 + r10
  m13 : q7 + q8 + q10 = r7 + r9 + r10
  m14 : q6 + q8 + q10 = r6 + r8 + r10
  m15 : q6 + q7 + q8 = r8 + r9 + r10
  m16 : q8 + q9 = r6 + r7 + r10
  m23 : q4 + q5 + q10 = r4 + r9 + r10
  m24 : q3 + q5 + q10 = r3 + r8 + r10
  m25 : q3 + q4 + q5 = r8 + r9 + r10
  m26 : q5 + q9 = r3 + r4 + r10
  m34 : q5 + q8 + q10 = r1 + r10
  m35 : q4 + q5 + q7 + q8 = r1 + r9 + r10
  m36 : q2 + q5 + q8 = r4 + r7 + r10
  m45 : q3 + q5 + q6 + q8 = r1 + r8 + r10
  m46 : q1 + q5 + q8 = r3 + r6 + r10
  m56 : q5 + q8 = r0 + r10

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

/-- The exact linear program bounds the six sums below away from zero,
uniformly over the moment polytope. -/
theorem MomentSystem.facts {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) :
    (1/6 : Real) ≤ r1 ∧ (1/12 : Real) ≤ q3 + q6 ∧ (1/12 : Real) ≤ q4 + q7 ∧ (1/12 : Real) ≤ q5 + q8 ∧ (1/4 : Real) ≤ q3 + q4 + q5 ∧ (1/4 : Real) ≤ q6 + q7 + q8 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, m12, m13, m14, m15, m16, m23, m24, m25, m26, m34, m35, m36, m45, m46, m56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- The five pair and triple sums the boundary analysis needs, each bounded
below by the exact linear program. -/
theorem MomentSystem.endpoints {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) :
    (1/12 : Real) ≤ q3 + q6 ∧ (1/12 : Real) ≤ q4 + q7 ∧ (1/12 : Real) ≤ q5 + q8 ∧ (1/4 : Real) ≤ q3 + q4 + q5 ∧ (1/4 : Real) ≤ q6 + q7 + q8 := by
  obtain ⟨_, c1, c2, c3, c4, c5⟩ := h.facts
  exact ⟨c1, c2, c3, c4, c5⟩

/-- The top probability at the complement of the star centre is positive,
which is what makes the collapsed binomials cancellable. -/
theorem MomentSystem.endpoints_pos {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) :
    0 < r1 := by
  obtain ⟨bK, _, _, _, _, _⟩ := h.facts
  linarith

/-! ## The boundary analysis -/

/-- With the two magnitude relations and the five polytope bounds, none of
the three amplitudes the pair triangle needs can vanish. -/
theorem positivity {qa qb qc qd qe qf : Real}
    (ha : 0 ≤ qa) (hb : 0 ≤ qb) (hc : 0 ≤ qc) (_hd : 0 ≤ qd)
    (he : 0 ≤ qe) (_hf : 0 ≤ qf)
    (L1 : (1/12 : Real) ≤ qa + qb)
    (L2 : (1/12 : Real) ≤ qc + qd)
    (L3 : (1/12 : Real) ≤ qe + qf)
    (L4 : (1/4 : Real) ≤ qa + qc + qe)
    (L5 : (1/4 : Real) ≤ qb + qd + qf)
    (mag1 : qa * qf = qb * qe)
    (mag2 : qa * qd = qb * qc) :
    0 < qb ∧ 0 < qc ∧ 0 < qe := by
  have hA : 0 < qa := by
    by_contra hcon
    push_neg at hcon
    have h0 : qa = 0 := le_antisymm hcon ha
    have hbp : 0 < qb := by linarith
    have h1 : qe = 0 := by
      have hz : qb * qe = 0 := by rw [← mag1, h0]; ring
      rcases mul_eq_zero.mp hz with hx | hx
      · linarith
      · exact hx
    have h2 : qc = 0 := by
      have hz : qb * qc = 0 := by rw [← mag2, h0]; ring
      rcases mul_eq_zero.mp hz with hx | hx
      · linarith
      · exact hx
    linarith
  refine ⟨?_, ?_, ?_⟩
  · by_contra hcon
    push_neg at hcon
    have h0 : qb = 0 := le_antisymm hcon hb
    have h1 : qf = 0 := by
      have hz : qa * qf = 0 := by rw [mag1, h0]; ring
      rcases mul_eq_zero.mp hz with hx | hx
      · linarith
      · exact hx
    have h2 : qd = 0 := by
      have hz : qa * qd = 0 := by rw [mag2, h0]; ring
      rcases mul_eq_zero.mp hz with hx | hx
      · linarith
      · exact hx
    linarith
  · by_contra hcon
    push_neg at hcon
    have h0 : qc = 0 := le_antisymm hcon hc
    have h1 : 0 < qd := by linarith
    have hz : qa * qd = 0 := by rw [mag2, h0]; ring
    rcases mul_eq_zero.mp hz with hx | hx
    · linarith
    · linarith
  · by_contra hcon
    push_neg at hcon
    have h0 : qe = 0 := le_antisymm hcon he
    have h1 : 0 < qf := by linarith
    have hz : qa * qf = 0 := by rw [mag1, h0]; ring
    rcases mul_eq_zero.mp hz with hx | hx
    · linarith
    · linarith

/-! ## The Walsh expansions -/

def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),
      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

theorem ex_ef0_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w0 = star (c y0) * d z0 + star (c y3) * d z3 + star (c y4) * d z4 + star (c y6) * d z6 + star (c y7) * d z7 + star (c y10) * d z10 := by
  unfold offSum
  rw [incidence_ef0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef0_0, flip_ef0_3, flip_ef0_4, flip_ef0_6, flip_ef0_7, flip_ef0_10]
  simp only [sg_ef0_w0_0, sg_ef0_w0_3, sg_ef0_w0_4, sg_ef0_w0_6, sg_ef0_w0_7, sg_ef0_w0_10, SixQubit.signMul_false]
  try ring

theorem ex_ef0_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef0 w1 = - star (c y0) * d z0 + star (c y3) * d z3 + star (c y4) * d z4 + star (c y6) * d z6 + star (c y7) * d z7 - star (c y10) * d z10 := by
  unfold offSum
  rw [incidence_ef0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef0_0, flip_ef0_3, flip_ef0_4, flip_ef0_6, flip_ef0_7, flip_ef0_10]
  simp only [sg_ef0_w1_0, sg_ef0_w1_3, sg_ef0_w1_4, sg_ef0_w1_6, sg_ef0_w1_7, sg_ef0_w1_10, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef1_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w0 = star (c y1) * d z0 + star (c y3) * d z2 + star (c y5) * d z4 + star (c y6) * d z5 + star (c y8) * d z7 + star (c y10) * d z9 := by
  unfold offSum
  rw [incidence_ef1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef1_0, flip_ef1_2, flip_ef1_4, flip_ef1_5, flip_ef1_7, flip_ef1_9]
  simp only [sg_ef1_w0_0, sg_ef1_w0_2, sg_ef1_w0_4, sg_ef1_w0_5, sg_ef1_w0_7, sg_ef1_w0_9, SixQubit.signMul_false]
  try ring

theorem ex_ef1_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w1 = - star (c y1) * d z0 + star (c y3) * d z2 + star (c y5) * d z4 + star (c y6) * d z5 + star (c y8) * d z7 - star (c y10) * d z9 := by
  unfold offSum
  rw [incidence_ef1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef1_0, flip_ef1_2, flip_ef1_4, flip_ef1_5, flip_ef1_7, flip_ef1_9]
  simp only [sg_ef1_w1_0, sg_ef1_w1_2, sg_ef1_w1_4, sg_ef1_w1_5, sg_ef1_w1_7, sg_ef1_w1_9, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef2_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w0 = star (c y2) * d z0 + star (c y4) * d z2 + star (c y5) * d z3 + star (c y7) * d z5 + star (c y8) * d z6 + star (c y10) * d z8 := by
  unfold offSum
  rw [incidence_ef2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef2_0, flip_ef2_2, flip_ef2_3, flip_ef2_5, flip_ef2_6, flip_ef2_8]
  simp only [sg_ef2_w0_0, sg_ef2_w0_2, sg_ef2_w0_3, sg_ef2_w0_5, sg_ef2_w0_6, sg_ef2_w0_8, SixQubit.signMul_false]
  try ring

theorem ex_ef2_w1 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w1 = - star (c y2) * d z0 + star (c y4) * d z2 + star (c y5) * d z3 + star (c y7) * d z5 + star (c y8) * d z6 - star (c y10) * d z8 := by
  unfold offSum
  rw [incidence_ef2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef2_0, flip_ef2_2, flip_ef2_3, flip_ef2_5, flip_ef2_6, flip_ef2_8]
  simp only [sg_ef2_w1_0, sg_ef2_w1_2, sg_ef2_w1_3, sg_ef2_w1_5, sg_ef2_w1_6, sg_ef2_w1_8, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex_ef3_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w0 = star (c y5) * d z1 + star (c y9) * d z5 := by
  unfold offSum
  rw [incidence_ef3]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef3_1, flip_ef3_5]
  simp only [sg_ef3_w0_1, sg_ef3_w0_5, SixQubit.signMul_false]
  try ring

theorem ex_ef4_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w0 = star (c y4) * d z1 + star (c y9) * d z6 := by
  unfold offSum
  rw [incidence_ef4]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef4_1, flip_ef4_6]
  simp only [sg_ef4_w0_1, sg_ef4_w0_6, SixQubit.signMul_false]
  try ring

theorem ex_ef5_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef5 w0 = star (c y3) * d z1 + star (c y9) * d z7 := by
  unfold offSum
  rw [incidence_ef5]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef5_1, flip_ef5_7]
  simp only [sg_ef5_w0_1, sg_ef5_w0_7, SixQubit.signMul_false]
  try ring

theorem ex_ef6_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w0 = star (c y8) * d z1 + star (c y9) * d z2 := by
  unfold offSum
  rw [incidence_ef6]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef6_1, flip_ef6_2]
  simp only [sg_ef6_w0_1, sg_ef6_w0_2, SixQubit.signMul_false]
  try ring

theorem ex_ef7_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef7 w0 = star (c y7) * d z1 + star (c y9) * d z3 := by
  unfold offSum
  rw [incidence_ef7]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef7_1, flip_ef7_3]
  simp only [sg_ef7_w0_1, sg_ef7_w0_3, SixQubit.signMul_false]
  try ring

theorem ex_ef8_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef8 w0 = star (c y6) * d z1 + star (c y9) * d z4 := by
  unfold offSum
  rw [incidence_ef8]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ef8_1, flip_ef8_4]
  simp only [sg_ef8_w0_1, sg_ef8_w0_4, SixQubit.signMul_false]
  try ring

/-! ## The collapsed binomials -/

/-- Multiplying each four-edge relation by `star (c y9)` and substituting
the star relations collapses it to a binomial times `d z1`. -/
theorem target_zero (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef0 w0 = 0)
    (h1 : offSum c d ef0 w1 = 0)
    (h2 : offSum c d ef1 w0 = 0)
    (h3 : offSum c d ef1 w1 = 0)
    (h4 : offSum c d ef2 w0 = 0)
    (h5 : offSum c d ef2 w1 = 0)
    (h6 : offSum c d ef3 w0 = 0)
    (h7 : offSum c d ef4 w0 = 0)
    (h8 : offSum c d ef5 w0 = 0)
    (h9 : offSum c d ef6 w0 = 0)
    (h10 : offSum c d ef7 w0 = 0)
    (h11 : offSum c d ef8 w0 = 0) :
    (star (c y3) * star (c y8) + star (c y5) * star (c y6)) * d z1 = 0
      ∧ (star (c y4) * star (c y8) + star (c y5) * star (c y7)) * d z1 = 0
      ∧ (star (c y3) * star (c y7) + star (c y4) * star (c y6)) * d z1 = 0 := by
  rw [ex_ef0_w0] at h0
  rw [ex_ef0_w1] at h1
  rw [ex_ef1_w0] at h2
  rw [ex_ef1_w1] at h3
  rw [ex_ef2_w0] at h4
  rw [ex_ef2_w1] at h5
  rw [ex_ef3_w0] at h6
  rw [ex_ef4_w0] at h7
  rw [ex_ef5_w0] at h8
  rw [ex_ef6_w0] at h9
  rw [ex_ef7_w0] at h10
  rw [ex_ef8_w0] at h11
  have s3 : star (c y3) * d z1 + star (c y9) * d z7 = 0 := by
    linear_combination (1 : ℂ) * h8
  have s4 : star (c y4) * d z1 + star (c y9) * d z6 = 0 := by
    linear_combination (1 : ℂ) * h7
  have s5 : star (c y5) * d z1 + star (c y9) * d z5 = 0 := by
    linear_combination (1 : ℂ) * h6
  have s6 : star (c y6) * d z1 + star (c y9) * d z4 = 0 := by
    linear_combination (1 : ℂ) * h11
  have s7 : star (c y7) * d z1 + star (c y9) * d z3 = 0 := by
    linear_combination (1 : ℂ) * h10
  have s8 : star (c y8) * d z1 + star (c y9) * d z2 = 0 := by
    linear_combination (1 : ℂ) * h9
  have R0 : star (c y3) * d z2 + star (c y8) * d z7 + star (c y5) * d z4 + star (c y6) * d z5 = 0 := by
    linear_combination (1/2 : ℂ) * h2 + (1/2 : ℂ) * h3
  have g0 : (star (c y3) * star (c y8) + star (c y5) * star (c y6)) * d z1 = 0 := by
    linear_combination (star (c y3) / 2 : ℂ) * s8 + (star (c y8) / 2 : ℂ) * s3 + (star (c y5) / 2 : ℂ) * s6 + (star (c y6) / 2 : ℂ) * s5 - (star (c y9) / 2 : ℂ) * R0
  have R1 : star (c y4) * d z2 + star (c y8) * d z6 + star (c y5) * d z3 + star (c y7) * d z5 = 0 := by
    linear_combination (1/2 : ℂ) * h4 + (1/2 : ℂ) * h5
  have g1 : (star (c y4) * star (c y8) + star (c y5) * star (c y7)) * d z1 = 0 := by
    linear_combination (star (c y4) / 2 : ℂ) * s8 + (star (c y8) / 2 : ℂ) * s4 + (star (c y5) / 2 : ℂ) * s7 + (star (c y7) / 2 : ℂ) * s5 - (star (c y9) / 2 : ℂ) * R1
  have R2 : star (c y3) * d z3 + star (c y7) * d z7 + star (c y4) * d z4 + star (c y6) * d z6 = 0 := by
    linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1
  have g2 : (star (c y3) * star (c y7) + star (c y4) * star (c y6)) * d z1 = 0 := by
    linear_combination (star (c y3) / 2 : ℂ) * s7 + (star (c y7) / 2 : ℂ) * s3 + (star (c y4) / 2 : ℂ) * s6 + (star (c y6) / 2 : ℂ) * s4 - (star (c y9) / 2 : ℂ) * R2
  exact ⟨g0, g1, g2⟩

/-! ## The no-go -/

/-- **Orbit 55 is impossible.** -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)))
    (h0 : offSum c d ef0 w0 = 0)
    (h1 : offSum c d ef0 w1 = 0)
    (h2 : offSum c d ef1 w0 = 0)
    (h3 : offSum c d ef1 w1 = 0)
    (h4 : offSum c d ef2 w0 = 0)
    (h5 : offSum c d ef2 w1 = 0)
    (h6 : offSum c d ef3 w0 = 0)
    (h7 : offSum c d ef4 w0 = 0)
    (h8 : offSum c d ef5 w0 = 0)
    (h9 : offSum c d ef6 w0 = 0)
    (h10 : offSum c d ef7 w0 = 0)
    (h11 : offSum c d ef8 w0 = 0)
    : False := by
  obtain ⟨g0, g1, g2⟩ := target_zero c d h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  obtain ⟨bK, c1, c2, c3, c4, c5⟩ := hm.facts
  have hzK : d z1 ≠ 0 := by
    intro hzero
    rw [hzero] at bK
    simp only [Complex.normSq_zero] at bK
    linarith
  have b0 : star (c y3) * star (c y8) + star (c y6) * star (c y5) = 0 := by
    rcases mul_eq_zero.mp g0 with hx | hx
    · linear_combination hx
    · exact absurd hx hzK
  have b1 : star (c y4) * star (c y8) + star (c y7) * star (c y5) = 0 := by
    rcases mul_eq_zero.mp g1 with hx | hx
    · linear_combination hx
    · exact absurd hx hzK
  have b2 : star (c y3) * star (c y7) + star (c y6) * star (c y4) = 0 := by
    rcases mul_eq_zero.mp g2 with hx | hx
    · linear_combination hx
    · exact absurd hx hzK
  have mag1 : Complex.normSq (c y3) * Complex.normSq (c y8)
      = Complex.normSq (c y6) * Complex.normSq (c y5) := by
    have hx : star (c y3) * star (c y8) = -(star (c y6) * star (c y5)) := by linear_combination b0
    have hy := congrArg Complex.normSq hx
    simpa [Complex.normSq_mul] using hy
  have mag2 : Complex.normSq (c y3) * Complex.normSq (c y7)
      = Complex.normSq (c y6) * Complex.normSq (c y4) := by
    have hx : star (c y3) * star (c y7) = -(star (c y6) * star (c y4)) := by linear_combination b2
    have hy := congrArg Complex.normSq hx
    simpa [Complex.normSq_mul] using hy
  obtain ⟨pb, pc, pe⟩ := positivity (Complex.normSq_nonneg (c y3))
    (Complex.normSq_nonneg (c y6)) (Complex.normSq_nonneg (c y4))
    (Complex.normSq_nonneg (c y7)) (Complex.normSq_nonneg (c y5))
    (Complex.normSq_nonneg (c y8)) c1 c2 c3 c4 c5 mag1 mag2
  have nb : star (c y6) ≠ 0 := by
    intro hzero
    have hk : c y6 = 0 := by simpa using congrArg star hzero
    rw [hk] at pb
    simp at pb
  have nc : star (c y4) ≠ 0 := by
    intro hzero
    have hk : c y4 = 0 := by simpa using congrArg star hzero
    rw [hk] at pc
    simp at pc
  have ne : star (c y5) ≠ 0 := by
    intro hzero
    have hk : c y5 = 0 := by simpa using congrArg star hzero
    rw [hk] at pe
    simp at pe
  exact SixQubit.Triangle.pair_contradiction b0 b1 b2 nb nc ne

end

end SixQubit.Orbit55
