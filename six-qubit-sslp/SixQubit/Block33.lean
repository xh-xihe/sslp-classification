import Mathlib

/-!
# The block algebra behind the orbit 33 no-go

Orbit 33 has a qubit of angle zero, so both fibers are closed under flipping it
and break into six blocks of two amplitudes.  Writing each block as a vector in
`ℂ²`, the Knill-Laflamme conditions become statements about `2 x 2` outer
products, and this file carries the resulting algebra.

Nothing here mentions bit strings: the input is twenty-four complex numbers
together with the block norms, the reflection identities
`c_i c_i^dagger + d_i d_i^dagger = 2 R_i rho`, and the cross relations.  The
conclusion is that no such configuration exists.  Every step is polynomial --
there is no division and no case analysis beyond `mul_eq_zero` against an
explicit nonzero rational.
-/

namespace SixQubit.Block33

open scoped ComplexConjugate


/-! ## Two-dimensional helpers -/

/-- Four entries of a vanishing sum of rank-one matrices force the determinant of
the left pair to vanish, provided the other pair is not the zero vector. -/
theorem det_zero (p0 q0 p1 q1 s0 t0 s1 t1 n : ℂ)
    (a00 : s1 * star p0 + s0 * star p1 = 0)
    (a01 : s1 * star q0 + s0 * star q1 = 0)
    (a10 : t1 * star p0 + t0 * star p1 = 0)
    (a11 : t1 * star q0 + t0 * star q1 = 0)
    (hn : s0 * star s0 + t0 * star t0 = n) (hne : n ≠ 0)
    : p0 * q1 - q0 * p1 = 0 := by
  have hs : s0 * (star p0 * star q1 - star q0 * star p1) = 0 := by
    linear_combination (star p0) * a01 - (star q0) * a00
  have ht : t0 * (star p0 * star q1 - star q0 * star p1) = 0 := by
    linear_combination (star p0) * a11 - (star q0) * a10
  have key : n * (star p0 * star q1 - star q0 * star p1) = 0 := by
    linear_combination (star s0) * hs + (star t0) * ht
      - (star p0 * star q1 - star q0 * star p1) * hn
  have hSW : star p0 * star q1 - star q0 * star p1 = 0 := by
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h hne
    · exact h
  have := congrArg star hSW
  simpa using this

/-- A vanishing determinant scales one vector onto the other. -/
theorem scale (p0 q0 p1 q1 n0 : ℂ)
    (h0 : p0 * star p0 + q0 * star q0 = n0)
    (hd : p0 * q1 - q0 * p1 = 0)
    : n0 * p1 = (star p0 * p1 + star q0 * q1) * p0
    ∧ n0 * q1 = (star p0 * p1 + star q0 * q1) * q0 := by
  constructor
  · linear_combination (-p1) * h0 - (star q0) * hd
  · linear_combination (-q1) * h0 + (star p0) * hd

/-- Collinear vectors have proportional outer products. -/
theorem prop_outer (p0 q0 p1 q1 n0 n1 : ℂ)
    (h0 : p0 * star p0 + q0 * star q0 = n0)
    (h1 : p1 * star p1 + q1 * star q1 = n1)
    (hd : p0 * q1 - q0 * p1 = 0)
    : n0 * (p1 * star p1) = n1 * (p0 * star p0)
    ∧ n0 * (p1 * star q1) = n1 * (p0 * star q0)
    ∧ n0 * (q1 * star q1) = n1 * (q0 * star q0) := by
  have shd : star p0 * star q1 - star q0 * star p1 = 0 := by
    have := congrArg star hd; simpa using this
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (-(p1 * star p1)) * h0 + (p0 * star p0) * h1
      - (star q0 * star p1) * hd - (p0 * q1) * shd
  · linear_combination (-(p1 * star q1)) * h0 + (p0 * star q0) * h1
      + (p0 * p1) * shd - (star q0 * star q1) * hd
  · linear_combination (-(q1 * star q1)) * h0 + (q0 * star q0) * h1
      + (p0 * q1) * shd + (star q0 * star p1) * hd

/-- Orthogonality in `ℂ²`: the outer product of one vector is determined by the
other.  Stated with the norms written out, so no division is needed. -/
theorem ortho2 (x0 x1 y0 y1 : ℂ) (h : star x0 * y0 + star x1 * y1 = 0)
    : (y0 * star y0 + y1 * star y1) * (x0 * star x0)
        = (x0 * star x0 + x1 * star x1) * (y1 * star y1)
    ∧ (y0 * star y0 + y1 * star y1) * (x0 * star x1)
        = -((x0 * star x0 + x1 * star x1) * (y0 * star y1))
    ∧ (y0 * star y0 + y1 * star y1) * (x1 * star x1)
        = (x0 * star x0 + x1 * star x1) * (y0 * star y0) := by
  have hs : x0 * star y0 + x1 * star y1 = 0 := by
    have := congrArg star h; simpa using this
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (x0 * star y0) * h - (star x1 * y1) * hs
  · linear_combination (star x1 * y0) * hs + (x0 * star y1) * h
  · linear_combination (star x1 * y1) * hs - (x0 * star y0) * h


/-! ## Conjugation helpers -/

theorem conj_pair (a b c d : ℂ) (h : a * star b + c * star d = 0)
    : d * star c + b * star a = 0 := by
  have h2 := congrArg star h
  simp only [star_add, star_mul', star_star, star_zero] at h2
  linear_combination h2

theorem conj_inner (a b c d : ℂ) (h : star a * b + star c * d = 0)
    : star b * a + star d * c = 0 := by
  have h2 := congrArg star h
  simp only [star_add, star_mul', star_star, star_zero] at h2
  linear_combination h2

theorem conj_scale (a b z r : ℂ) (hr : star r = r) (h : r * a = z * b)
    : r * star a = star z * star b := by
  have h2 := congrArg star h
  simp only [star_mul', hr] at h2
  linear_combination h2

/-- The scaling relation together with its conjugate. -/
theorem scale' (p0 q0 p1 q1 n0 : ℂ) (hstar : star n0 = n0)
    (h0 : p0 * star p0 + q0 * star q0 = n0)
    (hd : p0 * q1 - q0 * p1 = 0)
    : ∃ z, n0 * p1 = z * p0 ∧ n0 * q1 = z * q0
        ∧ n0 * star p1 = star z * star p0 ∧ n0 * star q1 = star z * star q0 := by
  obtain ⟨h1, h2⟩ := scale p0 q0 p1 q1 n0 h0 hd
  exact ⟨_, h1, h2, conj_scale p1 p0 _ n0 hstar h1, conj_scale q1 q0 _ n0 hstar h2⟩


/-! ## The block contradiction -/

/-- The blocks of orbit 33 cannot satisfy the reflection identities together with
the cross relations.  Everything here is polynomial: no division, no case split
beyond `mul_eq_zero` against explicit nonzero rationals. -/
theorem block_contradiction
    (p0 p1 p2 p3 p4 p5 q0 q1 q2 q3 q4 q5 : ℂ)
    (s0 s1 s2 s3 s4 s5 t0 t1 t2 t3 t4 t5 : ℂ)
    (nc0 : p0 * star p0 + q0 * star q0 = 3/10)
    (nc1 : p1 * star p1 + q1 * star q1 = 1/5)
    (nc2 : p2 * star p2 + q2 * star q2 = 1/5)
    (nc3 : p3 * star p3 + q3 * star q3 = 1/10)
    (nc4 : p4 * star p4 + q4 * star q4 = 1/10)
    (nc5 : p5 * star p5 + q5 * star q5 = 1/10)
    (nd0 : s0 * star s0 + t0 * star t0 = 3/10)
    (nd3 : s3 * star s3 + t3 * star t3 = 1/10)
    (r00_0 : p0 * star p0 + s0 * star s0
        = (3/5) * (p0 * star p0 + p1 * star p1 + p2 * star p2 + p3 * star p3 + p4 * star p4 + p5 * star p5))
    (r01_0 : p0 * star q0 + s0 * star t0
        = (3/5) * (p0 * star q0 + p1 * star q1 + p2 * star q2 + p3 * star q3 + p4 * star q4 + p5 * star q5))
    (r11_0 : q0 * star q0 + t0 * star t0
        = (3/5) * (q0 * star q0 + q1 * star q1 + q2 * star q2 + q3 * star q3 + q4 * star q4 + q5 * star q5))
    (r00_3 : p3 * star p3 + s3 * star s3
        = (1/5) * (p0 * star p0 + p1 * star p1 + p2 * star p2 + p3 * star p3 + p4 * star p4 + p5 * star p5))
    (r01_3 : p3 * star q3 + s3 * star t3
        = (1/5) * (p0 * star q0 + p1 * star q1 + p2 * star q2 + p3 * star q3 + p4 * star q4 + p5 * star q5))
    (x1_00 : s1 * star p0 + s0 * star p1 = 0)
    (x1_10 : t1 * star p0 + t0 * star p1 = 0)
    (x1_01 : s1 * star q0 + s0 * star q1 = 0)
    (x1_11 : t1 * star q0 + t0 * star q1 = 0)
    (x2_00 : s2 * star p0 + s0 * star p2 = 0)
    (x2_10 : t2 * star p0 + t0 * star p2 = 0)
    (x2_01 : s2 * star q0 + s0 * star q2 = 0)
    (x2_11 : t2 * star q0 + t0 * star q2 = 0)
    (y0_3 : star p3 * s0 + star q3 * t0 + (star p0 * s3 + star q0 * t3) = 0)
    (y1_3 : star p3 * s1 + star q3 * t1 + (star p1 * s3 + star q1 * t3) = 0)
    (y0_4 : star p4 * s0 + star q4 * t0 + (star p0 * s4 + star q0 * t4) = 0)
    (y1_4 : star p4 * s1 + star q4 * t1 + (star p1 * s4 + star q1 * t4) = 0)
    (y0_5 : star p5 * s0 + star q5 * t0 + (star p0 * s5 + star q0 * t5) = 0)
    (y1_5 : star p5 * s1 + star q5 * t1 + (star p1 * s5 + star q1 * t5) = 0)
    : False := by
  -- blocks 1 and 2 are collinear with block 0 on the bottom fiber
  have hd1 : p0 * q1 - q0 * p1 = 0 :=
    det_zero p0 q0 p1 q1 s0 t0 s1 t1 (3/10) x1_00 x1_01 x1_10 x1_11 nd0
      (by norm_num)
  have hd2 : p0 * q2 - q0 * p2 = 0 :=
    det_zero p0 q0 p2 q2 s0 t0 s2 t2 (3/10) x2_00 x2_01 x2_10 x2_11 nd0
      (by norm_num)
  -- and on the top fiber, after conjugating the four entries
  have cx1_00 : p1 * star s0 + p0 * star s1 = 0 :=
    conj_pair s1 p0 s0 p1 x1_00
  have cx1_10 : p1 * star t0 + p0 * star t1 = 0 :=
    conj_pair t1 p0 t0 p1 x1_10
  have cx1_01 : q1 * star s0 + q0 * star s1 = 0 :=
    conj_pair s1 q0 s0 q1 x1_01
  have cx1_11 : q1 * star t0 + q0 * star t1 = 0 :=
    conj_pair t1 q0 t0 q1 x1_11
  have hv1 : s0 * t1 - t0 * s1 = 0 :=
    det_zero s0 t0 s1 t1 p0 q0 p1 q1 (3/10) cx1_00 cx1_10 cx1_01 cx1_11 nc0
      (by norm_num)
  obtain ⟨lam, hp1, hq1, hp1s, hq1s⟩ :=
    scale' p0 q0 p1 q1 (3/10) (by simp) nc0 hd1
  obtain ⟨mu, hs1, ht1, _hs1s, _ht1s⟩ :=
    scale' s0 t0 s1 t1 (3/10) (by simp) nd0 hv1
  -- the two multipliers are conjugate-opposite
  have e1 : (s0 * star p0) * (mu + star lam) = 0 := by
    linear_combination (3/10 : ℂ) * x1_00 - (star p0) * hs1 - s0 * hp1s
  have e2 : (s0 * star q0) * (mu + star lam) = 0 := by
    linear_combination (3/10 : ℂ) * x1_01 - (star q0) * hs1 - s0 * hq1s
  have e3 : (t0 * star p0) * (mu + star lam) = 0 := by
    linear_combination (3/10 : ℂ) * x1_10 - (star p0) * ht1 - t0 * hp1s
  have e4 : (t0 * star q0) * (mu + star lam) = 0 := by
    linear_combination (3/10 : ℂ) * x1_11 - (star q0) * ht1 - t0 * hq1s
  have hmu : mu + star lam = 0 := by
    have key : (9/100 : ℂ) * (mu + star lam) = 0 := by
      linear_combination (star s0 * p0) * e1 + (star s0 * q0) * e2
        + (star t0 * p0) * e3 + (star t0 * q0) * e4
        - (mu + star lam) * (p0 * star p0 + q0 * star q0) * nd0
        - (3/10 : ℂ) * (mu + star lam) * nc0
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h (by norm_num)
    · exact h
  have hlam : lam * star lam = (3/50 : ℂ) := by
    have key : (3/10 : ℂ) * (lam * star lam - 3/50) = 0 := by
      linear_combination -((3/10 : ℂ) * star p1) * hp1 - (lam * p0) * hp1s
        - ((3/10 : ℂ) * star q1) * hq1 - (lam * q0) * hq1s
        + (9/100 : ℂ) * nc1 - (lam * star lam) * nc0
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h (by norm_num)
    · linear_combination h
  have hlne : star lam ≠ 0 := by
    intro h
    rw [h, mul_zero] at hlam
    norm_num at hlam
  -- the three far blocks are orthogonal to block 0 on the opposite fiber
  have hA3 : star p3 * s0 + star q3 * t0 = 0 := by
    have key : (-2 : ℂ) * (star lam * (star p3 * s0 + star q3 * t0)) = 0 := by
      linear_combination (3/10 : ℂ) * y1_3 - (star p3) * hs1 - (star q3) * ht1
        - s3 * hp1s - t3 * hq1s - (star lam) * y0_3
        - (star p3 * s0 + star q3 * t0) * hmu
    have h2 : star lam * (star p3 * s0 + star q3 * t0) = 0 := by
      rcases mul_eq_zero.mp key with h | h
      · exact absurd h (by norm_num)
      · exact h
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h hlne
    · exact h
  have hA4 : star p4 * s0 + star q4 * t0 = 0 := by
    have key : (-2 : ℂ) * (star lam * (star p4 * s0 + star q4 * t0)) = 0 := by
      linear_combination (3/10 : ℂ) * y1_4 - (star p4) * hs1 - (star q4) * ht1
        - s4 * hp1s - t4 * hq1s - (star lam) * y0_4
        - (star p4 * s0 + star q4 * t0) * hmu
    have h2 : star lam * (star p4 * s0 + star q4 * t0) = 0 := by
      rcases mul_eq_zero.mp key with h | h
      · exact absurd h (by norm_num)
      · exact h
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h hlne
    · exact h
  have hA5 : star p5 * s0 + star q5 * t0 = 0 := by
    have key : (-2 : ℂ) * (star lam * (star p5 * s0 + star q5 * t0)) = 0 := by
      linear_combination (3/10 : ℂ) * y1_5 - (star p5) * hs1 - (star q5) * ht1
        - s5 * hp1s - t5 * hq1s - (star lam) * y0_5
        - (star p5 * s0 + star q5 * t0) * hmu
    have h2 : star lam * (star p5 * s0 + star q5 * t0) = 0 := by
      rcases mul_eq_zero.mp key with h | h
      · exact absurd h (by norm_num)
      · exact h
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h hlne
    · exact h
  have hB3 : star p0 * s3 + star q0 * t3 = 0 := by linear_combination y0_3 - hA3
  have hB3' : star s3 * p0 + star t3 * q0 = 0 := conj_inner p0 s3 q0 t3 hB3
  -- the resulting outer products
  obtain ⟨w3a, w3b, w3c⟩ := ortho2 p3 q3 s0 t0 hA3
  have c3a : (3/10 : ℂ) * (p3 * star p3) = (1/10 : ℂ) * (t0 * star t0) := by
    linear_combination w3a - (p3 * star p3) * nd0 + (t0 * star t0) * nc3
  have c3b : (3/10 : ℂ) * (p3 * star q3) = -((1/10 : ℂ) * (s0 * star t0)) := by
    linear_combination w3b - (p3 * star q3) * nd0 - (s0 * star t0) * nc3
  have c3c : (3/10 : ℂ) * (q3 * star q3) = (1/10 : ℂ) * (s0 * star s0) := by
    linear_combination w3c - (q3 * star q3) * nd0 + (s0 * star s0) * nc3
  obtain ⟨w4a, w4b, w4c⟩ := ortho2 p4 q4 s0 t0 hA4
  have c4a : (3/10 : ℂ) * (p4 * star p4) = (1/10 : ℂ) * (t0 * star t0) := by
    linear_combination w4a - (p4 * star p4) * nd0 + (t0 * star t0) * nc4
  have c4b : (3/10 : ℂ) * (p4 * star q4) = -((1/10 : ℂ) * (s0 * star t0)) := by
    linear_combination w4b - (p4 * star q4) * nd0 - (s0 * star t0) * nc4
  have c4c : (3/10 : ℂ) * (q4 * star q4) = (1/10 : ℂ) * (s0 * star s0) := by
    linear_combination w4c - (q4 * star q4) * nd0 + (s0 * star s0) * nc4
  obtain ⟨w5a, w5b, w5c⟩ := ortho2 p5 q5 s0 t0 hA5
  have c5a : (3/10 : ℂ) * (p5 * star p5) = (1/10 : ℂ) * (t0 * star t0) := by
    linear_combination w5a - (p5 * star p5) * nd0 + (t0 * star t0) * nc5
  have c5b : (3/10 : ℂ) * (p5 * star q5) = -((1/10 : ℂ) * (s0 * star t0)) := by
    linear_combination w5b - (p5 * star q5) * nd0 - (s0 * star t0) * nc5
  have c5c : (3/10 : ℂ) * (q5 * star q5) = (1/10 : ℂ) * (s0 * star s0) := by
    linear_combination w5c - (q5 * star q5) * nd0 + (s0 * star s0) * nc5
  obtain ⟨v3a, v3b, _v3c⟩ := ortho2 s3 t3 p0 q0 hB3'
  have d3a : (3/10 : ℂ) * (s3 * star s3) = (1/10 : ℂ) * (q0 * star q0) := by
    linear_combination v3a - (s3 * star s3) * nc0 + (q0 * star q0) * nd3
  have d3b : (3/10 : ℂ) * (s3 * star t3) = -((1/10 : ℂ) * (p0 * star q0)) := by
    linear_combination v3b - (s3 * star t3) * nc0 - (p0 * star q0) * nd3
  -- blocks 1 and 2 carry proportional outer products
  obtain ⟨po1a, po1b, po1c⟩ :=
    prop_outer p0 q0 p1 q1 (3/10) (1/5) nc0 nc1 hd1
  obtain ⟨po2a, po2b, po2c⟩ :=
    prop_outer p0 q0 p2 q2 (3/10) (1/5) nc0 nc2 hd2
  -- the reduced state is half the identity
  have hRR : (3/50 : ℂ) * ((p0 * star p0 + p1 * star p1 + p2 * star p2 + p3 * star p3 + p4 * star p4 + p5 * star p5) - (q0 * star q0 + q1 * star q1 + q2 * star q2 + q3 * star q3 + q4 * star q4 + q5 * star q5)) = 0 := by
    linear_combination c3a + d3a - (3/10 : ℂ) * r00_3 + (1/10 : ℂ) * r11_0
  have htrace : (p0 * star p0 + p1 * star p1 + p2 * star p2 + p3 * star p3 + p4 * star p4 + p5 * star p5) + (q0 * star q0 + q1 * star q1 + q2 * star q2 + q3 * star q3 + q4 * star q4 + q5 * star q5) = 1 := by
    linear_combination nc0 + nc1 + nc2 + nc3 + nc4 + nc5
  have h00 : (p0 * star p0 + p1 * star p1 + p2 * star p2 + p3 * star p3 + p4 * star p4 + p5 * star p5) = 1/2 := by
    have key : (3/25 : ℂ) * ((p0 * star p0 + p1 * star p1 + p2 * star p2 + p3 * star p3 + p4 * star p4 + p5 * star p5) - 1/2) = 0 := by
      linear_combination hRR + (3/50 : ℂ) * htrace
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h (by norm_num)
    · linear_combination h
  have h11 : (q0 * star q0 + q1 * star q1 + q2 * star q2 + q3 * star q3 + q4 * star q4 + q5 * star q5) = 1/2 := by linear_combination htrace - h00
  have h01 : (p0 * star q0 + p1 * star q1 + p2 * star q2 + p3 * star q3 + p4 * star q4 + p5 * star q5) = 0 := by
    have key : (3/25 : ℂ) * (p0 * star q0 + p1 * star q1 + p2 * star q2 + p3 * star q3 + p4 * star q4 + p5 * star q5) = 0 := by
      linear_combination c3b + d3b - (3/10 : ℂ) * r01_3 - (1/10 : ℂ) * r01_0
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h (by norm_num)
    · exact h
  -- block 0 is forced to be a multiple of the identity, which is impossible
  have hpt : p0 * star p0 = t0 * star t0 := by
    linear_combination r00_0 - nd0 + (3/5 : ℂ) * h00
  have hqs : q0 * star q0 = s0 * star s0 := by
    linear_combination r11_0 - nd0 + (3/5 : ℂ) * h11
  have hst : s0 * star t0 = -(p0 * star q0) := by
    linear_combination r01_0 + (3/5 : ℂ) * h01
  have hp0 : p0 * star p0 = 3/20 := by
    linear_combination (3/10 : ℂ) * h00 - po1a - po2a - c3a - c4a - c5a
      + (3/10 : ℂ) * hpt
  have hq0 : q0 * star q0 = 3/20 := by
    linear_combination (3/10 : ℂ) * h11 - po1c - po2c - c3c - c4c - c5c
      + (3/10 : ℂ) * hqs
  have hpq : p0 * star q0 = 0 := by
    linear_combination (3/10 : ℂ) * h01 - po1b - po2b - c3b - c4b - c5b
      + (3/10 : ℂ) * hst
  have hcon : (9/400 : ℂ) = 0 := by
    linear_combination (q0 * star p0) * hpq - (q0 * star q0) * hp0 - (3/20 : ℂ) * hq0
  norm_num at hcon

end SixQubit.Block33
