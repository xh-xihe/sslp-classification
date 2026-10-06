import Mathlib

/-!
# The pair algebra behind the orbit 29 no-go

Orbit 29 (`a = (1,1,1,1,2,2)`, `q = 4`) has both fibers closed under `X_5 X_6`,
so each splits into eight pairs.  Reading a pair as a vector in `ℂ²`, every
two-term Knill-Laflamme relation becomes an orthogonality `C_m^† D_n = 0`, and
after the support collapse the surviving twelve relations realise exactly the
six edges of `K_4` on the four top pairs that carry them.

This module carries the resulting `ℂ²` algebra, free of any bit strings:

* `perp_det` -- a vector orthogonal to two others kills their determinant,
  weighted by its own squared norm.  This is the uniform replacement for
  "a nonzero bottom pair makes its two top neighbours parallel";
* `det_trans`, `perp_par`, `par_of_perp` -- the propagation steps;
* `par_edge` -- any two top pairs are parallel.  Either the bottom pair on their
  common edge has positive probability, or the two remaining probabilities are
  forced to their maximum `1/4` and one hop through either of them suffices;
* `endgame` -- at one top pair, the four Walsh combinations force each component
  of that pair to be killed by the matching component of the common bottom
  direction.

The headline is `pair_contradiction`: the pair data of orbit 29 cannot satisfy
the twelve orthogonality relations together with the sixteen Walsh combinations
and the recorded probabilities.

`SixQubit.Orbit29` supplies these hypotheses from the Knill-Laflamme conditions
and the moment system.
-/

namespace SixQubit.Pair29

open scoped ComplexConjugate


/-- `z * star z` is the squared modulus. -/
theorem sq (z : ℂ) : z * star z = (Complex.normSq z : ℂ) := by
  rw [mul_comm, Complex.normSq_eq_conj_mul_self]; rfl

/-- A vanishing squared norm kills both components. -/
theorem zero_of_norm (x y : ℂ) (h : x * star x + y * star y = 0) : x = 0 ∧ y = 0 := by
  rw [sq, sq] at h
  have hr : Complex.normSq x + Complex.normSq y = 0 := by exact_mod_cast h
  have h1 : Complex.normSq x = 0 := by
    nlinarith [Complex.normSq_nonneg x, Complex.normSq_nonneg y]
  have h2 : Complex.normSq y = 0 := by
    nlinarith [Complex.normSq_nonneg x, Complex.normSq_nonneg y]
  exact ⟨Complex.normSq_eq_zero.mp h1, Complex.normSq_eq_zero.mp h2⟩

/-- A vector orthogonal to two others kills their determinant, weighted by its
own squared norm.  This is the uniform substitute for "if `C` is nonzero its two
neighbours are parallel". -/
theorem perp_det (c0 c1 a0 a1 b0 b1 : ℂ)
    (ha : star c0 * a0 + star c1 * a1 = 0)
    (hb : star c0 * b0 + star c1 * b1 = 0)
    : (c0 * star c0 + c1 * star c1) * (a0 * b1 - b0 * a1) = 0 := by
  have h0 : star c0 * (a0 * b1 - b0 * a1) = 0 := by
    linear_combination b1 * ha - a1 * hb
  have h1 : star c1 * (a0 * b1 - b0 * a1) = 0 := by
    linear_combination a0 * hb - b0 * ha
  linear_combination c0 * h0 + c1 * h1

/-- Parallelism is transitive through a nonzero vector. -/
theorem det_trans (a0 a1 b0 b1 e0 e1 n : ℂ)
    (hab : a0 * b1 - b0 * a1 = 0)
    (hbe : b0 * e1 - e0 * b1 = 0)
    (hn : b0 * star b0 + b1 * star b1 = n) (hne : n ≠ 0)
    : a0 * e1 - e0 * a1 = 0 := by
  have h0 : b0 * (a0 * e1 - e0 * a1) = 0 := by
    linear_combination a0 * hbe + e0 * hab
  have h1 : b1 * (a0 * e1 - e0 * a1) = 0 := by
    linear_combination e1 * hab + a1 * hbe
  have key : n * (a0 * e1 - e0 * a1) = 0 := by
    linear_combination (star b0) * h0 + (star b1) * h1
      - (a0 * e1 - e0 * a1) * hn
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h hne
  · exact h

/-- Orthogonality transfers along a parallel pair. -/
theorem perp_par (c0 c1 a0 a1 b0 b1 n : ℂ)
    (hp : star c0 * a0 + star c1 * a1 = 0)
    (hab : a0 * b1 - b0 * a1 = 0)
    (hn : a0 * star a0 + a1 * star a1 = n) (hne : n ≠ 0)
    : star c0 * b0 + star c1 * b1 = 0 := by
  have h0 : a0 * (star c0 * b0 + star c1 * b1) = 0 := by
    linear_combination b0 * hp + (star c1) * hab
  have h1 : a1 * (star c0 * b0 + star c1 * b1) = 0 := by
    linear_combination b1 * hp - (star c0) * hab
  have key : n * (star c0 * b0 + star c1 * b1) = 0 := by
    linear_combination (star a0) * h0 + (star a1) * h1
      - (star c0 * b0 + star c1 * b1) * hn
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h hne
  · exact h

/-- Two vectors orthogonal to the same nonzero vector are parallel. -/
theorem par_of_perp (c0 c1 e0 e1 v0 v1 n : ℂ)
    (hc : star c0 * v0 + star c1 * v1 = 0)
    (he : star e0 * v0 + star e1 * v1 = 0)
    (hn : v0 * star v0 + v1 * star v1 = n) (hne : n ≠ 0)
    : c0 * e1 - e0 * c1 = 0 := by
  have h0 : v0 * (star c0 * star e1 - star e0 * star c1) = 0 := by
    linear_combination (star e1) * hc - (star c1) * he
  have h1 : v1 * (star c0 * star e1 - star e0 * star c1) = 0 := by
    linear_combination (star c0) * he - (star e0) * hc
  have key : n * (star c0 * star e1 - star e0 * star c1) = 0 := by
    linear_combination (star v0) * h0 + (star v1) * h1
      - (star c0 * star e1 - star e0 * star c1) * hn
  have hz : star c0 * star e1 - star e0 * star c1 = 0 := by
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h hne
    · exact h
  have := congrArg star hz
  simpa using this

/-- Two top pairs are parallel.  Either their common bottom pair carries positive
probability, or the two remaining probabilities are both maximal and one hop
through either of them does it. -/
theorem par_edge (Qn Qm Qa Qb : Real) (n0 n1 m0 m1 a0 a1 : ℂ)
    (hsum : Qn + Qm + Qa + Qb = 3/4)
    (hb : Qb ≤ 1/4) (hna : Qa ≤ 1/4) (hQn : 0 ≤ Qn) (hQm : 0 ≤ Qm)
    (nn : n0 * star n0 + n1 * star n1 = (Qn : ℂ))
    (nm : m0 * star m0 + m1 * star m1 = (Qm : ℂ))
    (na : a0 * star a0 + a1 * star a1 = (Qa : ℂ))
    (enm : ((Qn + Qm - 1/4 : Real) : ℂ) * (n0 * m1 - m0 * n1) = 0)
    (ena : ((Qn + Qa - 1/4 : Real) : ℂ) * (n0 * a1 - a0 * n1) = 0)
    (ema : ((Qm + Qa - 1/4 : Real) : ℂ) * (m0 * a1 - a0 * m1) = 0)
    : n0 * m1 - m0 * n1 = 0 := by
  by_cases hP : Qn + Qm - 1/4 = 0
  · -- the common bottom pair is empty, so the other two are maximal
    have hab : Qa + Qb = 1/2 := by linarith
    have hA : Qa = 1/4 := by linarith
    by_cases hn : Qn = 0
    · -- the first top pair is empty
      have h0 : n0 * star n0 + n1 * star n1 = 0 := by rw [nn, hn]; norm_num
      obtain ⟨z0, z1⟩ := zero_of_norm n0 n1 h0
      rw [z0, z1]; ring
    · by_cases hm : Qm = 0
      · have h0 : m0 * star m0 + m1 * star m1 = 0 := by rw [nm, hm]; norm_num
        obtain ⟨z0, z1⟩ := zero_of_norm m0 m1 h0
        rw [z0, z1]; ring
      · -- both hop through the maximal third pair
        have h1 : n0 * a1 - a0 * n1 = 0 := by
          rcases mul_eq_zero.mp ena with h | h
          · exact absurd h (by
              simp only [Complex.ofReal_eq_zero]; intro hc; apply hn; linarith)
          · exact h
        have h2 : m0 * a1 - a0 * m1 = 0 := by
          rcases mul_eq_zero.mp ema with h | h
          · exact absurd h (by
              simp only [Complex.ofReal_eq_zero]; intro hc; apply hm; linarith)
          · exact h
        have hane : ((Qa : Real) : ℂ) ≠ 0 := by
          simp only [ne_eq, Complex.ofReal_eq_zero]; rw [hA]; norm_num
        have h2' : a0 * m1 - m0 * a1 = 0 := by linear_combination -h2
        exact det_trans n0 n1 a0 a1 m0 m1 _ h1 h2' na hane
  · rcases mul_eq_zero.mp enm with h | h
    · exact absurd h (by simp only [Complex.ofReal_eq_zero]; exact hP)
    · exact h

/-- The endgame at one top pair.

The three bottom pairs entering the two masks are collinear with `u`, the pinned
pair has squared norm `1/4`, and `u` is orthogonal to the target top pair.  The
four Walsh combinations then force each component of the target to be killed by
the matching component of `u`. -/
theorem endgame (u0 u1 a1 b1 a2 b2 a3 b3 a7 b7 : ℂ)
    (s1 t1 s2 t2 s3 t3 s t : ℂ)
    (c1 : a1 * u1 - u0 * b1 = 0) (c2 : a2 * u1 - u0 * b2 = 0)
    (c3 : a3 * u1 - u0 * b3 = 0)
    (n7 : a7 * star a7 + b7 * star b7 = 1/4)
    (perp : star u0 * s + star u1 * t = 0)
    (P1 : star a1 * s1 + star a2 * s2 + star a3 * s3 + star b7 * t = 0)
    (P2 : star b1 * t1 + star b2 * t2 + star b3 * t3 + star a7 * s = 0)
    (P3 : star b1 * s1 + star b2 * s2 + star b3 * s3 + star b7 * s = 0)
    (P4 : star a1 * t1 + star a2 * t2 + star a3 * t3 + star a7 * t = 0)
    : star u0 * s = 0 ∧ star u1 * t = 0 := by
  have d1 : star a1 * star u1 - star u0 * star b1 = 0 := by
    have := congrArg star c1
    simp only [star_sub, star_mul', star_zero] at this
    linear_combination this
  have d2 : star a2 * star u1 - star u0 * star b2 = 0 := by
    have := congrArg star c2
    simp only [star_sub, star_mul', star_zero] at this
    linear_combination this
  have d3 : star a3 * star u1 - star u0 * star b3 = 0 := by
    have := congrArg star c3
    simp only [star_sub, star_mul', star_zero] at this
    linear_combination this
  have hb : star b7 * (star u1 * t - star u0 * s) = 0 := by
    linear_combination (star u1) * P1 - (star u0) * P3
      - s1 * d1 - s2 * d2 - s3 * d3
  have ha : star a7 * (star u0 * s - star u1 * t) = 0 := by
    linear_combination (star u0) * P2 - (star u1) * P4
      + t1 * d1 + t2 * d2 + t3 * d3
  have key : (1/4 : ℂ) * (star u0 * s - star u1 * t) = 0 := by
    linear_combination a7 * ha - b7 * hb
      - (star u0 * s - star u1 * t) * n7
  have hk : star u0 * s - star u1 * t = 0 := by
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h (by norm_num)
    · exact h
  constructor
  · linear_combination (1/2 : ℂ) * perp + (1/2 : ℂ) * hk
  · linear_combination (1/2 : ℂ) * perp - (1/2 : ℂ) * hk

/-- Every bottom pair is orthogonal to the anchor direction.  Its two top
neighbours have probabilities summing to at least `1/4`, so at least one of
them is nonzero and carries the transfer. -/
theorem perp_v (c0 c1 a0 a1 b0 b1 v0 v1 : ℂ) (Qa Qb : Real)
    (hQ : 1/4 ≤ Qa + Qb)
    (na : a0 * star a0 + a1 * star a1 = (Qa : ℂ))
    (nb : b0 * star b0 + b1 * star b1 = (Qb : ℂ))
    (pa : star c0 * a0 + star c1 * a1 = 0)
    (pb : star c0 * b0 + star c1 * b1 = 0)
    (da : a0 * v1 - v0 * a1 = 0) (db : b0 * v1 - v0 * b1 = 0)
    : star c0 * v0 + star c1 * v1 = 0 := by
  by_cases hA : Qa = 0
  · have hB : Qb ≠ 0 := by intro h; rw [hA, h] at hQ; norm_num at hQ
    exact perp_par c0 c1 b0 b1 v0 v1 _ pb db nb (by simpa using hB)
  · exact perp_par c0 c1 a0 a1 v0 v1 _ pa da na (by simpa using hA)

/-- The closing argument, once an anchor top pair `v` is in hand. -/
theorem finish (v0 v1 : ℂ) (Qv : Real)
    (hv : v0 * star v0 + v1 * star v1 = (Qv : ℂ)) (hQv : Qv ≠ 0)
    (a1 b1 : ℂ)
    (a2 b2 : ℂ)
    (a3 b3 : ℂ)
    (a4 b4 : ℂ)
    (a5 b5 : ℂ)
    (a6 b6 : ℂ)
    (a7 b7 : ℂ)
    (S3 T3 : ℂ) (Q3 : Real)
    (S5 T5 : ℂ) (Q5 : Real)
    (S6 T6 : ℂ) (Q6 : Real)
    (S7 T7 : ℂ) (Q7 : Real)
    (s0 t0 : ℂ)
    (s1 t1 : ℂ)
    (s2 t2 : ℂ)
    (s4 t4 : ℂ)
    (n7 : a7 * star a7 + b7 * star b7 = 1/4)
    (nq3 : S3 * star S3 + T3 * star T3 = (Q3 : ℂ))
    (nq5 : S5 * star S5 + T5 * star T5 = (Q5 : ℂ))
    (nq6 : S6 * star S6 + T6 * star T6 = (Q6 : ℂ))
    (nq7 : S7 * star S7 + T7 * star T7 = (Q7 : ℂ))
    (qsum : Q3 + Q5 + Q6 + Q7 = 3/4)
    (esum : (S3 * star S3 - T3 * star T3) + (S5 * star S5 - T5 * star T5)
      + (S6 * star S6 - T6 * star T6) + (S7 * star S7 - T7 * star T7) = 0)
    (d3 : S3 * v1 - v0 * T3 = 0)
    (d5 : S5 * v1 - v0 * T5 = 0)
    (d6 : S6 * v1 - v0 * T6 = 0)
    (d7 : S7 * v1 - v0 * T7 = 0)
    (p1 : star a1 * v0 + star b1 * v1 = 0)
    (p2 : star a2 * v0 + star b2 * v1 = 0)
    (p3 : star a3 * v0 + star b3 * v1 = 0)
    (p4 : star a4 * v0 + star b4 * v1 = 0)
    (p5 : star a5 * v0 + star b5 * v1 = 0)
    (p6 : star a6 * v0 + star b6 * v1 = 0)
    (E3A : star a4 * s0 + star a5 * s1 + star a6 * s2 + star b7 * T3 = 0)
    (E3B : star b4 * t0 + star b5 * t1 + star b6 * t2 + star a7 * S3 = 0)
    (E3C : star b4 * s0 + star b5 * s1 + star b6 * s2 + star b7 * S3 = 0)
    (E3D : star a4 * t0 + star a5 * t1 + star a6 * t2 + star a7 * T3 = 0)
    (E5A : star a2 * s0 + star a3 * s1 + star a6 * s4 + star b7 * T5 = 0)
    (E5B : star b2 * t0 + star b3 * t1 + star b6 * t4 + star a7 * S5 = 0)
    (E5C : star b2 * s0 + star b3 * s1 + star b6 * s4 + star b7 * S5 = 0)
    (E5D : star a2 * t0 + star a3 * t1 + star a6 * t4 + star a7 * T5 = 0)
    (E6A : star a1 * s0 + star a3 * s2 + star a5 * s4 + star b7 * T6 = 0)
    (E6B : star b1 * t0 + star b3 * t2 + star b5 * t4 + star a7 * S6 = 0)
    (E6C : star b1 * s0 + star b3 * s2 + star b5 * s4 + star b7 * S6 = 0)
    (E6D : star a1 * t0 + star a3 * t2 + star a5 * t4 + star a7 * T6 = 0)
    (E7A : star a1 * s1 + star a2 * s2 + star a4 * s4 + star b7 * T7 = 0)
    (E7B : star b1 * t1 + star b2 * t2 + star b4 * t4 + star a7 * S7 = 0)
    (E7C : star b1 * s1 + star b2 * s2 + star b4 * s4 + star b7 * S7 = 0)
    (E7D : star a1 * t1 + star a2 * t2 + star a4 * t4 + star a7 * T7 = 0)
    : False := by
  have hQvC : ((Qv : Real) : ℂ) ≠ 0 := by simpa using hQv
  have hu : star (-star v1) * v0 + star (star v0) * v1 = 0 := by
    simp only [star_neg, star_star]; ring
  have cu1 : a1 * (star v0) - (-star v1) * b1 = 0 :=
    par_of_perp a1 b1 (-star v1) (star v0) v0 v1 _ p1 hu hv hQvC
  have cu2 : a2 * (star v0) - (-star v1) * b2 = 0 :=
    par_of_perp a2 b2 (-star v1) (star v0) v0 v1 _ p2 hu hv hQvC
  have cu3 : a3 * (star v0) - (-star v1) * b3 = 0 :=
    par_of_perp a3 b3 (-star v1) (star v0) v0 v1 _ p3 hu hv hQvC
  have cu4 : a4 * (star v0) - (-star v1) * b4 = 0 :=
    par_of_perp a4 b4 (-star v1) (star v0) v0 v1 _ p4 hu hv hQvC
  have cu5 : a5 * (star v0) - (-star v1) * b5 = 0 :=
    par_of_perp a5 b5 (-star v1) (star v0) v0 v1 _ p5 hu hv hQvC
  have cu6 : a6 * (star v0) - (-star v1) * b6 = 0 :=
    par_of_perp a6 b6 (-star v1) (star v0) v0 v1 _ p6 hu hv hQvC
  have pv3 : star (-star v1) * S3 + star (star v0) * T3 = 0 := by
    simp only [star_neg, star_star]; linear_combination -d3
  obtain ⟨k3S, k3T⟩ := endgame (-star v1) (star v0)
    a4 b4 a5 b5 a6 b6 a7 b7
    s0 t0 s1 t1 s2 t2 S3 T3
    cu4 cu5 cu6 n7 pv3 E3A E3B E3C E3D
  have pv5 : star (-star v1) * S5 + star (star v0) * T5 = 0 := by
    simp only [star_neg, star_star]; linear_combination -d5
  obtain ⟨k5S, k5T⟩ := endgame (-star v1) (star v0)
    a2 b2 a3 b3 a6 b6 a7 b7
    s0 t0 s1 t1 s4 t4 S5 T5
    cu2 cu3 cu6 n7 pv5 E5A E5B E5C E5D
  have pv6 : star (-star v1) * S6 + star (star v0) * T6 = 0 := by
    simp only [star_neg, star_star]; linear_combination -d6
  obtain ⟨k6S, k6T⟩ := endgame (-star v1) (star v0)
    a1 b1 a3 b3 a5 b5 a7 b7
    s0 t0 s2 t2 s4 t4 S6 T6
    cu1 cu3 cu5 n7 pv6 E6A E6B E6C E6D
  have pv7 : star (-star v1) * S7 + star (star v0) * T7 = 0 := by
    simp only [star_neg, star_star]; linear_combination -d7
  obtain ⟨k7S, k7T⟩ := endgame (-star v1) (star v0)
    a1 b1 a2 b2 a4 b4 a7 b7
    s1 t1 s2 t2 s4 t4 S7 T7
    cu1 cu2 cu4 n7 pv7 E7A E7B E7C E7D
  by_cases hv1 : v1 = 0
  · have hv0 : v0 ≠ 0 := by
      intro h
      apply hQv
      have hz : ((Qv : Real) : ℂ) = 0 := by rw [← hv, h, hv1]; ring
      exact_mod_cast hz
    have z3 : T3 = 0 := by
      have hk := k3T
      simp only [star_star] at hk
      rcases mul_eq_zero.mp hk with h | h
      · exact absurd h hv0
      · exact h
    have z5 : T5 = 0 := by
      have hk := k5T
      simp only [star_star] at hk
      rcases mul_eq_zero.mp hk with h | h
      · exact absurd h hv0
      · exact h
    have z6 : T6 = 0 := by
      have hk := k6T
      simp only [star_star] at hk
      rcases mul_eq_zero.mp hk with h | h
      · exact absurd h hv0
      · exact h
    have z7 : T7 = 0 := by
      have hk := k7T
      simp only [star_star] at hk
      rcases mul_eq_zero.mp hk with h | h
      · exact absurd h hv0
      · exact h
    have hbad : ((3/4 : Real) : ℂ) = 0 := by
      rw [← qsum]; push_cast
      linear_combination esum - nq3 - nq5 - nq6 - nq7
        + (2 * star T3) * z3 + (2 * star T5) * z5
        + (2 * star T6) * z6 + (2 * star T7) * z7
    norm_num at hbad
  · have z3 : S3 = 0 := by
      have hk := k3S
      simp only [star_neg, star_star] at hk
      rcases mul_eq_zero.mp hk with h | h
      · exact absurd (neg_eq_zero.mp h) hv1
      · exact h
    have z5 : S5 = 0 := by
      have hk := k5S
      simp only [star_neg, star_star] at hk
      rcases mul_eq_zero.mp hk with h | h
      · exact absurd (neg_eq_zero.mp h) hv1
      · exact h
    have z6 : S6 = 0 := by
      have hk := k6S
      simp only [star_neg, star_star] at hk
      rcases mul_eq_zero.mp hk with h | h
      · exact absurd (neg_eq_zero.mp h) hv1
      · exact h
    have z7 : S7 = 0 := by
      have hk := k7S
      simp only [star_neg, star_star] at hk
      rcases mul_eq_zero.mp hk with h | h
      · exact absurd (neg_eq_zero.mp h) hv1
      · exact h
    have hbad : ((3/4 : Real) : ℂ) = 0 := by
      rw [← qsum]; push_cast
      linear_combination -esum - nq3 - nq5 - nq6 - nq7
        + (2 * star S3) * z3 + (2 * star S5) * z5
        + (2 * star S6) * z6 + (2 * star S7) * z7
    norm_num at hbad

/-- A vanishing pair of squared norms bounds the recorded probability below. -/
theorem nonneg_of_norm (x y : ℂ) (r : Real)
    (h : x * star x + y * star y = (r : ℂ)) : 0 ≤ r := by
  rw [sq, sq] at h
  have hr : Complex.normSq x + Complex.normSq y = r := by exact_mod_cast h
  nlinarith [Complex.normSq_nonneg x, Complex.normSq_nonneg y]

/-- With an anchor direction in hand, every bottom pair is orthogonal to it and
the closing argument applies. -/
theorem anchored (v0 v1 : ℂ) (Qv : Real)
    (hv : v0 * star v0 + v1 * star v1 = (Qv : ℂ)) (hQv : Qv ≠ 0)
    (a1 b1 : ℂ)
    (a2 b2 : ℂ)
    (a3 b3 : ℂ)
    (a4 b4 : ℂ)
    (a5 b5 : ℂ)
    (a6 b6 : ℂ)
    (a7 b7 : ℂ)
    (S3 T3 : ℂ) (Q3 : Real)
    (S5 T5 : ℂ) (Q5 : Real)
    (S6 T6 : ℂ) (Q6 : Real)
    (S7 T7 : ℂ) (Q7 : Real)
    (s0 t0 : ℂ)
    (s1 t1 : ℂ)
    (s2 t2 : ℂ)
    (s4 t4 : ℂ)
    (n7 : a7 * star a7 + b7 * star b7 = 1/4)
    (nq3 : S3 * star S3 + T3 * star T3 = (Q3 : ℂ))
    (nq5 : S5 * star S5 + T5 * star T5 = (Q5 : ℂ))
    (nq6 : S6 * star S6 + T6 * star T6 = (Q6 : ℂ))
    (nq7 : S7 * star S7 + T7 * star T7 = (Q7 : ℂ))
    (nc1 : a1 * star a1 + b1 * star b1 = ((Q3 + Q5 - 1/4 : Real) : ℂ))
    (nc2 : a2 * star a2 + b2 * star b2 = ((Q3 + Q6 - 1/4 : Real) : ℂ))
    (nc3 : a3 * star a3 + b3 * star b3 = ((Q3 + Q7 - 1/4 : Real) : ℂ))
    (nc4 : a4 * star a4 + b4 * star b4 = ((Q5 + Q6 - 1/4 : Real) : ℂ))
    (nc5 : a5 * star a5 + b5 * star b5 = ((Q5 + Q7 - 1/4 : Real) : ℂ))
    (nc6 : a6 * star a6 + b6 * star b6 = ((Q6 + Q7 - 1/4 : Real) : ℂ))
    (qsum : Q3 + Q5 + Q6 + Q7 = 3/4)
    (esum : (S3 * star S3 - T3 * star T3) + (S5 * star S5 - T5 * star T5)
      + (S6 * star S6 - T6 * star T6) + (S7 * star S7 - T7 * star T7) = 0)
    (o13 : star a1 * S3 + star b1 * T3 = 0)
    (o15 : star a1 * S5 + star b1 * T5 = 0)
    (o23 : star a2 * S3 + star b2 * T3 = 0)
    (o26 : star a2 * S6 + star b2 * T6 = 0)
    (o33 : star a3 * S3 + star b3 * T3 = 0)
    (o37 : star a3 * S7 + star b3 * T7 = 0)
    (o45 : star a4 * S5 + star b4 * T5 = 0)
    (o46 : star a4 * S6 + star b4 * T6 = 0)
    (o55 : star a5 * S5 + star b5 * T5 = 0)
    (o57 : star a5 * S7 + star b5 * T7 = 0)
    (o66 : star a6 * S6 + star b6 * T6 = 0)
    (o67 : star a6 * S7 + star b6 * T7 = 0)
    (E3A : star a4 * s0 + star a5 * s1 + star a6 * s2 + star b7 * T3 = 0)
    (E3B : star b4 * t0 + star b5 * t1 + star b6 * t2 + star a7 * S3 = 0)
    (E3C : star b4 * s0 + star b5 * s1 + star b6 * s2 + star b7 * S3 = 0)
    (E3D : star a4 * t0 + star a5 * t1 + star a6 * t2 + star a7 * T3 = 0)
    (E5A : star a2 * s0 + star a3 * s1 + star a6 * s4 + star b7 * T5 = 0)
    (E5B : star b2 * t0 + star b3 * t1 + star b6 * t4 + star a7 * S5 = 0)
    (E5C : star b2 * s0 + star b3 * s1 + star b6 * s4 + star b7 * S5 = 0)
    (E5D : star a2 * t0 + star a3 * t1 + star a6 * t4 + star a7 * T5 = 0)
    (E6A : star a1 * s0 + star a3 * s2 + star a5 * s4 + star b7 * T6 = 0)
    (E6B : star b1 * t0 + star b3 * t2 + star b5 * t4 + star a7 * S6 = 0)
    (E6C : star b1 * s0 + star b3 * s2 + star b5 * s4 + star b7 * S6 = 0)
    (E6D : star a1 * t0 + star a3 * t2 + star a5 * t4 + star a7 * T6 = 0)
    (E7A : star a1 * s1 + star a2 * s2 + star a4 * s4 + star b7 * T7 = 0)
    (E7B : star b1 * t1 + star b2 * t2 + star b4 * t4 + star a7 * S7 = 0)
    (E7C : star b1 * s1 + star b2 * s2 + star b4 * s4 + star b7 * S7 = 0)
    (E7D : star a1 * t1 + star a2 * t2 + star a4 * t4 + star a7 * T7 = 0)
    (dd3 : S3 * v1 - v0 * T3 = 0)
    (dd5 : S5 * v1 - v0 * T5 = 0)
    (dd6 : S6 * v1 - v0 * T6 = 0)
    (dd7 : S7 * v1 - v0 * T7 = 0)
    : False := by
  have hb1 : (1/4 : Real) ≤ Q3 + Q5 := by
    have := nonneg_of_norm a1 b1 _ nc1; linarith
  have p1 : star a1 * v0 + star b1 * v1 = 0 :=
    perp_v a1 b1 S3 T3 S5 T5 v0 v1 Q3 Q5 hb1 nq3 nq5 o13 o15 dd3 dd5
  have hb2 : (1/4 : Real) ≤ Q3 + Q6 := by
    have := nonneg_of_norm a2 b2 _ nc2; linarith
  have p2 : star a2 * v0 + star b2 * v1 = 0 :=
    perp_v a2 b2 S3 T3 S6 T6 v0 v1 Q3 Q6 hb2 nq3 nq6 o23 o26 dd3 dd6
  have hb3 : (1/4 : Real) ≤ Q3 + Q7 := by
    have := nonneg_of_norm a3 b3 _ nc3; linarith
  have p3 : star a3 * v0 + star b3 * v1 = 0 :=
    perp_v a3 b3 S3 T3 S7 T7 v0 v1 Q3 Q7 hb3 nq3 nq7 o33 o37 dd3 dd7
  have hb4 : (1/4 : Real) ≤ Q5 + Q6 := by
    have := nonneg_of_norm a4 b4 _ nc4; linarith
  have p4 : star a4 * v0 + star b4 * v1 = 0 :=
    perp_v a4 b4 S5 T5 S6 T6 v0 v1 Q5 Q6 hb4 nq5 nq6 o45 o46 dd5 dd6
  have hb5 : (1/4 : Real) ≤ Q5 + Q7 := by
    have := nonneg_of_norm a5 b5 _ nc5; linarith
  have p5 : star a5 * v0 + star b5 * v1 = 0 :=
    perp_v a5 b5 S5 T5 S7 T7 v0 v1 Q5 Q7 hb5 nq5 nq7 o55 o57 dd5 dd7
  have hb6 : (1/4 : Real) ≤ Q6 + Q7 := by
    have := nonneg_of_norm a6 b6 _ nc6; linarith
  have p6 : star a6 * v0 + star b6 * v1 = 0 :=
    perp_v a6 b6 S6 T6 S7 T7 v0 v1 Q6 Q7 hb6 nq6 nq7 o66 o67 dd6 dd7
  exact finish v0 v1 Qv hv hQv
    a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 a7 b7
    S3 T3 Q3 S5 T5 Q5 S6 T6 Q6 S7 T7 Q7
    s0 t0 s1 t1 s2 t2 s4 t4
    n7 nq3 nq5 nq6 nq7 qsum esum
    dd3 dd5 dd6 dd7
    p1 p2 p3 p4 p5 p6
    E3A E3B E3C E3D
    E5A E5B E5C E5D
    E6A E6B E6C E6D
    E7A E7B E7C E7D

/-- Orbit 29 has no exact code: the pair algebra alone is contradictory. -/
theorem pair_contradiction
    (a1 b1 : ℂ)
    (a2 b2 : ℂ)
    (a3 b3 : ℂ)
    (a4 b4 : ℂ)
    (a5 b5 : ℂ)
    (a6 b6 : ℂ)
    (a7 b7 : ℂ)
    (S3 T3 : ℂ) (Q3 : Real)
    (S5 T5 : ℂ) (Q5 : Real)
    (S6 T6 : ℂ) (Q6 : Real)
    (S7 T7 : ℂ) (Q7 : Real)
    (s0 t0 : ℂ)
    (s1 t1 : ℂ)
    (s2 t2 : ℂ)
    (s4 t4 : ℂ)
    (n7 : a7 * star a7 + b7 * star b7 = 1/4)
    (nq3 : S3 * star S3 + T3 * star T3 = (Q3 : ℂ))
    (nq5 : S5 * star S5 + T5 * star T5 = (Q5 : ℂ))
    (nq6 : S6 * star S6 + T6 * star T6 = (Q6 : ℂ))
    (nq7 : S7 * star S7 + T7 * star T7 = (Q7 : ℂ))
    (nc1 : a1 * star a1 + b1 * star b1 = ((Q3 + Q5 - 1/4 : Real) : ℂ))
    (nc2 : a2 * star a2 + b2 * star b2 = ((Q3 + Q6 - 1/4 : Real) : ℂ))
    (nc3 : a3 * star a3 + b3 * star b3 = ((Q3 + Q7 - 1/4 : Real) : ℂ))
    (nc4 : a4 * star a4 + b4 * star b4 = ((Q5 + Q6 - 1/4 : Real) : ℂ))
    (nc5 : a5 * star a5 + b5 * star b5 = ((Q5 + Q7 - 1/4 : Real) : ℂ))
    (nc6 : a6 * star a6 + b6 * star b6 = ((Q6 + Q7 - 1/4 : Real) : ℂ))
    (qsum : Q3 + Q5 + Q6 + Q7 = 3/4)
    (esum : (S3 * star S3 - T3 * star T3) + (S5 * star S5 - T5 * star T5)
      + (S6 * star S6 - T6 * star T6) + (S7 * star S7 - T7 * star T7) = 0)
    (o13 : star a1 * S3 + star b1 * T3 = 0)
    (o15 : star a1 * S5 + star b1 * T5 = 0)
    (o23 : star a2 * S3 + star b2 * T3 = 0)
    (o26 : star a2 * S6 + star b2 * T6 = 0)
    (o33 : star a3 * S3 + star b3 * T3 = 0)
    (o37 : star a3 * S7 + star b3 * T7 = 0)
    (o45 : star a4 * S5 + star b4 * T5 = 0)
    (o46 : star a4 * S6 + star b4 * T6 = 0)
    (o55 : star a5 * S5 + star b5 * T5 = 0)
    (o57 : star a5 * S7 + star b5 * T7 = 0)
    (o66 : star a6 * S6 + star b6 * T6 = 0)
    (o67 : star a6 * S7 + star b6 * T7 = 0)
    (E3A : star a4 * s0 + star a5 * s1 + star a6 * s2 + star b7 * T3 = 0)
    (E3B : star b4 * t0 + star b5 * t1 + star b6 * t2 + star a7 * S3 = 0)
    (E3C : star b4 * s0 + star b5 * s1 + star b6 * s2 + star b7 * S3 = 0)
    (E3D : star a4 * t0 + star a5 * t1 + star a6 * t2 + star a7 * T3 = 0)
    (E5A : star a2 * s0 + star a3 * s1 + star a6 * s4 + star b7 * T5 = 0)
    (E5B : star b2 * t0 + star b3 * t1 + star b6 * t4 + star a7 * S5 = 0)
    (E5C : star b2 * s0 + star b3 * s1 + star b6 * s4 + star b7 * S5 = 0)
    (E5D : star a2 * t0 + star a3 * t1 + star a6 * t4 + star a7 * T5 = 0)
    (E6A : star a1 * s0 + star a3 * s2 + star a5 * s4 + star b7 * T6 = 0)
    (E6B : star b1 * t0 + star b3 * t2 + star b5 * t4 + star a7 * S6 = 0)
    (E6C : star b1 * s0 + star b3 * s2 + star b5 * s4 + star b7 * S6 = 0)
    (E6D : star a1 * t0 + star a3 * t2 + star a5 * t4 + star a7 * T6 = 0)
    (E7A : star a1 * s1 + star a2 * s2 + star a4 * s4 + star b7 * T7 = 0)
    (E7B : star b1 * t1 + star b2 * t2 + star b4 * t4 + star a7 * S7 = 0)
    (E7C : star b1 * s1 + star b2 * s2 + star b4 * s4 + star b7 * S7 = 0)
    (E7D : star a1 * t1 + star a2 * t2 + star a4 * t4 + star a7 * T7 = 0)
    (qle3 : Q3 ≤ 1/4)
    (qle5 : Q5 ≤ 1/4)
    (qle6 : Q6 ≤ 1/4)
    (qle7 : Q7 ≤ 1/4)
    : False := by
  have g1 : ((Q3 + Q5 - 1/4 : Real) : ℂ) * (S3 * T5 - S5 * T3) = 0 := by
    rw [← nc1]
    exact perp_det a1 b1 S3 T3 S5 T5 o13 o15
  have g2 : ((Q3 + Q6 - 1/4 : Real) : ℂ) * (S3 * T6 - S6 * T3) = 0 := by
    rw [← nc2]
    exact perp_det a2 b2 S3 T3 S6 T6 o23 o26
  have g3 : ((Q3 + Q7 - 1/4 : Real) : ℂ) * (S3 * T7 - S7 * T3) = 0 := by
    rw [← nc3]
    exact perp_det a3 b3 S3 T3 S7 T7 o33 o37
  have g4 : ((Q5 + Q6 - 1/4 : Real) : ℂ) * (S5 * T6 - S6 * T5) = 0 := by
    rw [← nc4]
    exact perp_det a4 b4 S5 T5 S6 T6 o45 o46
  have g5 : ((Q5 + Q7 - 1/4 : Real) : ℂ) * (S5 * T7 - S7 * T5) = 0 := by
    rw [← nc5]
    exact perp_det a5 b5 S5 T5 S7 T7 o55 o57
  have g6 : ((Q6 + Q7 - 1/4 : Real) : ℂ) * (S6 * T7 - S7 * T6) = 0 := by
    rw [← nc6]
    exact perp_det a6 b6 S6 T6 S7 T7 o66 o67
  have nn3 : (0 : Real) ≤ Q3 := nonneg_of_norm S3 T3 _ nq3
  have nn5 : (0 : Real) ≤ Q5 := nonneg_of_norm S5 T5 _ nq5
  have nn6 : (0 : Real) ≤ Q6 := nonneg_of_norm S6 T6 _ nq6
  have nn7 : (0 : Real) ≤ Q7 := nonneg_of_norm S7 T7 _ nq7
  have k1 : S3 * T5 - S5 * T3 = 0 :=
    par_edge Q3 Q5 Q6 Q7 S3 T3 S5 T5 S6 T6
      (by linarith) qle7 qle6 nn3 nn5 nq3 nq5 nq6
      g1 g2 g4
  have k2 : S3 * T6 - S6 * T3 = 0 :=
    par_edge Q3 Q6 Q5 Q7 S3 T3 S6 T6 S5 T5
      (by linarith) qle7 qle5 nn3 nn6 nq3 nq6 nq5
      g2 g1 (by push_cast at g4 ⊢; linear_combination -g4)
  have k3 : S3 * T7 - S7 * T3 = 0 :=
    par_edge Q3 Q7 Q5 Q6 S3 T3 S7 T7 S5 T5
      (by linarith) qle6 qle5 nn3 nn7 nq3 nq7 nq5
      g3 g1 (by push_cast at g5 ⊢; linear_combination -g5)
  have k4 : S5 * T6 - S6 * T5 = 0 :=
    par_edge Q5 Q6 Q3 Q7 S5 T5 S6 T6 S3 T3
      (by linarith) qle7 qle3 nn5 nn6 nq5 nq6 nq3
      g4 (by push_cast at g1 ⊢; linear_combination -g1) (by push_cast at g2 ⊢; linear_combination -g2)
  have k5 : S5 * T7 - S7 * T5 = 0 :=
    par_edge Q5 Q7 Q3 Q6 S5 T5 S7 T7 S3 T3
      (by linarith) qle6 qle3 nn5 nn7 nq5 nq7 nq3
      g5 (by push_cast at g1 ⊢; linear_combination -g1) (by push_cast at g3 ⊢; linear_combination -g3)
  have k6 : S6 * T7 - S7 * T6 = 0 :=
    par_edge Q6 Q7 Q3 Q5 S6 T6 S7 T7 S3 T3
      (by linarith) qle5 qle3 nn6 nn7 nq6 nq7 nq3
      g6 (by push_cast at g2 ⊢; linear_combination -g2) (by push_cast at g3 ⊢; linear_combination -g3)
  by_cases h3 : Q3 = 0
  · have h5 : Q5 ≠ 0 := by intro h; linarith
    exact anchored S5 T5 Q5 nq5 h5
      a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 a7 b7
      S3 T3 Q3 S5 T5 Q5 S6 T6 Q6 S7 T7 Q7
      s0 t0 s1 t1 s2 t2 s4 t4
      n7 nq3 nq5 nq6 nq7 nc1 nc2 nc3 nc4 nc5 nc6 qsum esum
      o13 o15 o23 o26 o33 o37 o45 o46 o55 o57 o66 o67
      E3A E3B E3C E3D
      E5A E5B E5C E5D
      E6A E6B E6C E6D
      E7A E7B E7C E7D
      (by linear_combination k1)
      (by ring)
      (by linear_combination -k4)
      (by linear_combination -k5)
  · 
    exact anchored S3 T3 Q3 nq3 h3
      a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 a7 b7
      S3 T3 Q3 S5 T5 Q5 S6 T6 Q6 S7 T7 Q7
      s0 t0 s1 t1 s2 t2 s4 t4
      n7 nq3 nq5 nq6 nq7 nc1 nc2 nc3 nc4 nc5 nc6 qsum esum
      o13 o15 o23 o26 o33 o37 o45 o46 o55 o57 o66 o67
      E3A E3B E3C E3D
      E5A E5B E5C E5D
      E6A E6B E6C E6D
      E7A E7B E7C E7D
      (by ring)
      (by linear_combination -k1)
      (by linear_combination -k2)
      (by linear_combination -k3)

end SixQubit.Pair29
