import Mathlib

import SS.FullKL
import SS.HilbertKL
import SixQubit.Common
import SixQubit.K4Kernel
import SixQubit.Orbit36

/-!
# Phase rigidity of the order-five moment orbit 36

`SixQubit.Orbit36` forces every magnitude of an exact orbit-36 solution:

    |a|^2 = |b|^2 = |r_i|^2 = 1/10,      |c_ij|^2 = 1/15,

so no boundary face of the moment polytope survives and every logical word has
the full twelve-term support.  This module takes the next step of the chapter
and forces the *phases* of the six edge amplitudes.

## The edge-phase matrix

Normalizing `u_i = sqrt 10 * r_i` and `v_ij = sqrt 15 * c_ij` makes every `u_i`
and `v_ij` a unit vector, and the chapter's edge-phase matrix is
`u_i u_j v_ij`.  All of that is a positive rescaling of

    M_ij = r_i r_j c_ij,        u_i u_j v_ij = sqrt 1500 * M_ij,

so this module works with the division-free `M_ij` and records the normalized
form as a corollary.  Two facts about `M` are immediate:

  * `normSq (M_ij) = (1/10) * (1/10) * (1/15) = 1/1500`, the same for all six
    edges;
  * multiplying row `i` of the kernel system `C r = 0` by `r_i` turns it into
    the `i`-th row sum of `M`, so **every row of `M` sums to zero**.

## Two collapses

1.  The four row sums are four linear equations in the six entries.  Adding and
    subtracting them -- no modulus, no case analysis -- gives the pairing

        M12 = M34,   M13 = M24,   M14 = M23.

2.  `triple_of_equal_normSq` is the standalone algebraic lemma: three complex
    numbers of a common nonzero modulus that sum to zero are a common factor
    times `(1, w, w^2)` for a primitive cube root of unity `w`.  It is proved
    division-free.  The conjugate of the sum, multiplied by the product of the
    three numbers, delivers the second elementary symmetric function; with the
    first one that gives `m1^2 + m1 m2 + m2^2 = 0`, which factors as
    `(m2 - rho m1) (m2 - rho^2 m1) = 0`.

Applying the lemma to the first row of `M` and combining with the pairing gives
the unique proper three-edge-colouring of `K_4`,

    M12 = M34 = mu,   M13 = M24 = mu w,   M14 = M23 = mu w^2,

which is the chapter's boxed equation.  Interchanging `w` and `w^2` is a
transposition of the first four qubits, so the statement carries the honest
disjunction rather than a choice.

## What is assumed

`phase_rigidity` has exactly the hypotheses of `SixQubit.Orbit36.magnitudes_forced`
-- one `MomentSystem` and twenty-one vanishing Knill--Laflamme rows.  Nothing
else: no genericity, no full-support assumption, no choice of gauge.

## The weight enumerator

`AEnum c d j` is the Shor--Laflamme coefficient
`A_j = (1/4) * sum over weight-j Paulis of |Tr (E Pi)|^2`, built on the
Hilbert-space semantics of `SS.HilbertKL` (`SS.innerC`, `SS.pauliAct`).  The
index set is never enumerated: `AEnum_eq_zero` reduces a vanishing coefficient to
the pointwise statement `Tr (E Pi) = 0`.

What is proved here:

  * `A1_eq_zero` -- `A_1 = 0` for every orbit-36 solution, from the moment
    system and the support conditions alone.  The twelve `X_i`, `Y_i` rows have
    a weight-one flip mask, and `mask_wt_le_one` decides that no two points of
    either fiber are at Hamming distance one; the six `Z_i` rows cancel between
    the fibers by `projTrace_diag`, because complementation exchanges the fibers,
    reverses every odd Walsh sign and preserves the probabilities.
  * `triangle_sum` -- the algebraic mechanism the chapter names for `A_3 = 0`:
    for the exceptional weight-three flip mask `f = {i,5,6}` the bottom-word
    expectation is a common sign times `conj (r_2) c_34 + conj (r_3) c_24 +
    conj (r_4) c_23`, and multiplying by `10 r_2 r_3 r_4` turns that into
    `M_34 + M_24 + M_23 = mu (1 + w + w^2) = 0`.
  * `macwilliams_normal_form` -- the closing arithmetic.  For a `((6,2,3))` code
    the quantum MacWilliams relation together with `A_j = B_j` for `j <= 2`
    determines `A_4, A_5, A_6` from `x = A_1`, `y = A_2`, `z = A_3`; that
    relation is an explicit hypothesis, and substituting the orbit-36 values
    `(0, 21/25, 0)` gives the boxed enumerator

        (A_0, ..., A_6) = (1, 0, 21/25, 0, 291/25, 384/25, 79/25).

What is **not** proved here, stated precisely so that nothing is overclaimed:

  * `A_2 = 21/25`.  The nine Paulis on a coordinate pair contribute
    `lambda_ZZ^2 + 8 |S|^2` with `S` the incidence sum of the pair, and `|S|^2`
    is gauge invariant but `lambda_XX` alone is not; establishing it needs all
    fifteen pair computations, not just the magnitudes.
  * `A_3 = 0`.  Only the exceptional flip masks `f = {i,5,6}` and the trivial
    mask `f = 0` are within reach of what is proved here.  The remaining
    weight-three families -- flip masks `{5,6}`, `{i,j}`, `{i,j,5}`, `{i,j,6}` --
    vanish because the antiunitary `Theta = Z_5 Z_6 X^{tensor 6} K` gives
    `<psi_1|E|psi_1> = eps(E) <psi_0|E|psi_0>` with `eps(E) = -1`.  That relation
    needs the amplitude-level identity `d (complement x) = tau * (-1)^(x_5+x_6) *
    conj (c x)`, whose `A = tau conj a` component is pinned by the `X_i X_6`
    rows.  Those rows are not among the twenty-one hypotheses used here, and the
    reindexing lemma that turns the identity into a statement about every Pauli
    does not exist in this repository.

Everything computational is decided by the Lean kernel.  No `sorry`, no
`native_decide`.

This file is generated by `tools/generators/gen36phase.py`.
-/

namespace SixQubit.Orbit36Phase

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

open SixQubit.K4Kernel (rho rho_quadratic)
open SixQubit.Orbit36

/-! ## 1.  Three numbers of equal modulus summing to zero -/

/-- **The standalone phase lemma.**  Three complex numbers of a common nonzero
modulus whose sum vanishes are a common factor times `(1, w, w^2)` for a
primitive cube root of unity `w`; the two possible orderings are recorded
honestly as a disjunction.

The proof is division-free.  Conjugating the sum and multiplying by `m1 m2 m3`
turns the three modulus hypotheses into the second elementary symmetric
function `m1 m2 + m1 m3 + m2 m3 = 0`; eliminating `m3` gives the quadratic
`m1^2 + m1 m2 + m2^2 = 0`, which is `(m2 - rho m1) (m2 - rho^2 m1) = 0`
because `rho^2 + rho + 1 = 0`. -/
theorem triple_of_equal_normSq {m1 m2 m3 : ℂ} {t : ℝ}
    (n1 : Complex.normSq m1 = t) (n2 : Complex.normSq m2 = t)
    (n3 : Complex.normSq m3 = t) (ht : t ≠ 0)
    (hs : m1 + m2 + m3 = 0) :
    (m2 = rho * m1 ∧ m3 = rho ^ 2 * m1)
      ∨ (m2 = rho ^ 2 * m1 ∧ m3 = rho * m1) := by
  have u1 : m1 * star m1 = (t : ℂ) := by
    rw [mul_comm, SixQubit.star_mul_self, n1]
  have u2 : m2 * star m2 = (t : ℂ) := by
    rw [mul_comm, SixQubit.star_mul_self, n2]
  have u3 : m3 * star m3 = (t : ℂ) := by
    rw [mul_comm, SixQubit.star_mul_self, n3]
  have hc : star m1 + star m2 + star m3 = 0 := by
    have := congrArg star hs
    simpa using this
  have htC : (t : ℂ) ≠ 0 := by
    exact_mod_cast ht
  have he2 : m1 * m2 + m1 * m3 + m2 * m3 = 0 := by
    have key : (t : ℂ) * (m1 * m2 + m1 * m3 + m2 * m3) = 0 := by
      linear_combination (m1 * m2 * m3) * hc - (m2 * m3) * u1 - (m1 * m3) * u2
        - (m1 * m2) * u3
    exact (mul_eq_zero.mp key).resolve_left htC
  have hsq : m1 ^ 2 + m1 * m2 + m2 ^ 2 = 0 := by
    linear_combination (m1 + m2) * hs - he2
  have hfac : (m2 - rho * m1) * (m2 - rho ^ 2 * m1) = 0 := by
    linear_combination hsq + (-(m1 * m2) + (rho - 1) * m1 ^ 2) * rho_quadratic
  rcases mul_eq_zero.mp hfac with h | h
  · have h2 : m2 = rho * m1 := sub_eq_zero.mp h
    exact Or.inl ⟨h2, by linear_combination hs - h2 - m1 * rho_quadratic⟩
  · have h2 : m2 = rho ^ 2 * m1 := sub_eq_zero.mp h
    exact Or.inr ⟨h2, by linear_combination hs - h2 - m1 * rho_quadratic⟩

/-- The unit-modulus special case, which is the form the chapter states. -/
theorem triple_of_unit_normSq {m1 m2 m3 : ℂ}
    (n1 : Complex.normSq m1 = 1) (n2 : Complex.normSq m2 = 1)
    (n3 : Complex.normSq m3 = 1) (hs : m1 + m2 + m3 = 0) :
    (m2 = rho * m1 ∧ m3 = rho ^ 2 * m1)
      ∨ (m2 = rho ^ 2 * m1 ∧ m3 = rho * m1) :=
  triple_of_equal_normSq n1 n2 n3 one_ne_zero hs

/-! ## 2.  The four row sums of the edge-phase matrix -/

/-- **The pairing, by linear algebra alone.**  If every row of the symmetric
zero-diagonal `4 x 4` matrix `M` sums to zero then opposite edges of `K_4`
carry equal entries.  No modulus and no nonvanishing hypothesis is used:
`(h1 - h2) + (h3 - h4)` is `2 (M13 - M24)` and `(h1 - h2) - (h3 - h4)` is
`2 (M14 - M23)`. -/
theorem edge_pairing {M12 M13 M14 M23 M24 M34 : ℂ}
    (h1 : M12 + M13 + M14 = 0) (h2 : M12 + M23 + M24 = 0)
    (h3 : M13 + M23 + M34 = 0) (h4 : M14 + M24 + M34 = 0) :
    M34 = M12 ∧ M24 = M13 ∧ M23 = M14 :=
  ⟨by linear_combination (-h1 - h2 + h3 + h4) / 2,
   by linear_combination (-h1 + h2 - h3 + h4) / 2,
   by linear_combination (-h1 + h2 + h3 - h4) / 2⟩

/-! ## 3.  The three-edge-colouring of `K_4` -/

/-- **The edge-phase colouring.**  From the four rows of `C r = 0` and seven of
the ten forced magnitudes, the six products `M_ij = r_i r_j c_ij` all have
modulus squared `1/1500`, opposite edges agree, and the first row is a common
factor times `(1, w, w^2)`.

Only `|r_1|, ..., |r_4|` and `|c_12|, |c_13|, |c_14|` are needed: the moduli of
the other three edges follow from the pairing.  Multiplying row `i` by `r_i`
turns it into the `i`-th row sum of `M`, which is the only place the kernel
system is used. -/
theorem edge_colouring {r1 r2 r3 r4 c12 c13 c14 c23 c24 c34 : ℂ}
    (p1 : Complex.normSq r1 = 1/10) (p2 : Complex.normSq r2 = 1/10)
    (p3 : Complex.normSq r3 = 1/10) (p4 : Complex.normSq r4 = 1/10)
    (q12 : Complex.normSq c12 = 1/15) (q13 : Complex.normSq c13 = 1/15)
    (q14 : Complex.normSq c14 = 1/15)
    (e1 : c12 * r2 + c13 * r3 + c14 * r4 = 0)
    (e2 : c12 * r1 + c23 * r3 + c24 * r4 = 0)
    (e3 : c13 * r1 + c23 * r2 + c34 * r4 = 0)
    (e4 : c14 * r1 + c24 * r2 + c34 * r3 = 0) :
    Complex.normSq (r1 * r2 * c12) = 1/1500
      ∧ r3 * r4 * c34 = r1 * r2 * c12
      ∧ r2 * r4 * c24 = r1 * r3 * c13
      ∧ r2 * r3 * c23 = r1 * r4 * c14
      ∧ ((r1 * r3 * c13 = rho * (r1 * r2 * c12)
            ∧ r1 * r4 * c14 = rho ^ 2 * (r1 * r2 * c12))
          ∨ (r1 * r3 * c13 = rho ^ 2 * (r1 * r2 * c12)
            ∧ r1 * r4 * c14 = rho * (r1 * r2 * c12))) := by
  have n12 : Complex.normSq (r1 * r2 * c12) = 1/1500 := by
    rw [map_mul, map_mul, p1, p2, q12]; norm_num
  have n13 : Complex.normSq (r1 * r3 * c13) = 1/1500 := by
    rw [map_mul, map_mul, p1, p3, q13]; norm_num
  have n14 : Complex.normSq (r1 * r4 * c14) = 1/1500 := by
    rw [map_mul, map_mul, p1, p4, q14]; norm_num
  have row1 : r1 * r2 * c12 + r1 * r3 * c13 + r1 * r4 * c14 = 0 := by
    linear_combination r1 * e1
  have row2 : r1 * r2 * c12 + r2 * r3 * c23 + r2 * r4 * c24 = 0 := by
    linear_combination r2 * e2
  have row3 : r1 * r3 * c13 + r2 * r3 * c23 + r3 * r4 * c34 = 0 := by
    linear_combination r3 * e3
  have row4 : r1 * r4 * c14 + r2 * r4 * c24 + r3 * r4 * c34 = 0 := by
    linear_combination r4 * e4
  obtain ⟨g34, g24, g23⟩ := edge_pairing row1 row2 row3 row4
  exact ⟨n12, g34, g24, g23,
    triple_of_equal_normSq n12 n13 n14 (by norm_num) row1⟩

/-! ## 4.  The kernel system, re-derived from the Knill--Laflamme rows -/

set_option maxHeartbeats 1600000 in
/-- **The four rows of `C r = 0`.**  This is the second collapse of the chapter,
extracted from `SixQubit.Orbit36` in the shape the phase argument consumes: the
three `X_i Z_j` dressings reduce each `X_i` row to a star sum, and the four
`X_i X_5` rows turn the star sums into the kernel system for the symmetric
zero-diagonal edge matrix.  The `X_5 X_6` row is not needed here. -/
theorem kernel_rows (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5))
            (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5))
            (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)))
    (ho0 : offSum c d ex1 w0 = 0)
    (ho1 : offSum c d ex1 w2 = 0)
    (ho2 : offSum c d ex1 w3 = 0)
    (ho3 : offSum c d ex1 w4 = 0)
    (ho4 : offSum c d ex2 w0 = 0)
    (ho5 : offSum c d ex2 w1 = 0)
    (ho6 : offSum c d ex2 w3 = 0)
    (ho7 : offSum c d ex2 w4 = 0)
    (ho8 : offSum c d ex3 w0 = 0)
    (ho9 : offSum c d ex3 w1 = 0)
    (ho10 : offSum c d ex3 w2 = 0)
    (ho11 : offSum c d ex3 w4 = 0)
    (ho12 : offSum c d ex4 w0 = 0)
    (ho13 : offSum c d ex4 w1 = 0)
    (ho14 : offSum c d ex4 w2 = 0)
    (ho15 : offSum c d ex4 w3 = 0)
    (ho16 : offSum c d ex15 w0 = 0)
    (ho17 : offSum c d ex25 w0 = 0)
    (ho18 : offSum c d ex35 w0 = 0)
    (ho19 : offSum c d ex45 w0 = 0) :
    c y6 * c y3 + c y7 * c y4 + c y8 * c y5 = 0
      ∧ c y6 * c y2 + c y9 * c y4 + c y10 * c y5 = 0
      ∧ c y7 * c y2 + c y9 * c y3 + c y11 * c y5 = 0
      ∧ c y8 * c y2 + c y10 * c y3 + c y11 * c y4 = 0 := by
  obtain ⟨-, t1, -, -, -, -, -, -, -, -, -, -, -, hb, -, -, -, -, -, -⟩ := hm.facts
  rw [ex_ex1_w0] at ho0
  rw [ex_ex1_w2] at ho1
  rw [ex_ex1_w3] at ho2
  rw [ex_ex1_w4] at ho3
  rw [ex_ex2_w0] at ho4
  rw [ex_ex2_w1] at ho5
  rw [ex_ex2_w3] at ho6
  rw [ex_ex2_w4] at ho7
  rw [ex_ex3_w0] at ho8
  rw [ex_ex3_w1] at ho9
  rw [ex_ex3_w2] at ho10
  rw [ex_ex3_w4] at ho11
  rw [ex_ex4_w0] at ho12
  rw [ex_ex4_w1] at ho13
  rw [ex_ex4_w2] at ho14
  rw [ex_ex4_w3] at ho15
  rw [ex_ex15_w0] at ho16
  rw [ex_ex25_w0] at ho17
  rw [ex_ex35_w0] at ho18
  rw [ex_ex45_w0] at ho19
  have hBne : d z1 ≠ 0 := by
    intro hzero
    rw [hzero, Complex.normSq_zero] at t1
    linarith
  obtain ⟨-, -, -, star1⟩ :=
    SixQubit.K4Kernel.starSum_of_dressings (c1 := c y6) (c2 := c y7)
      (c3 := c y8) (r1 := c y3) (r2 := c y4) (r3 := c y5) (R1 := d z3)
      (R2 := d z4) (R3 := d z5) (C1 := d z6) (C2 := d z7) (C3 := d z8)
      (by linear_combination ho0) (by linear_combination ho1)
      (by linear_combination ho2) (by linear_combination ho3)
  obtain ⟨-, -, -, star2⟩ :=
    SixQubit.K4Kernel.starSum_of_dressings (c1 := c y6) (c2 := c y9)
      (c3 := c y10) (r1 := c y2) (r2 := c y4) (r3 := c y5) (R1 := d z2)
      (R2 := d z4) (R3 := d z5) (C1 := d z6) (C2 := d z9) (C3 := d z10)
      (by linear_combination ho4) (by linear_combination ho5)
      (by linear_combination ho6) (by linear_combination ho7)
  obtain ⟨-, -, -, star3⟩ :=
    SixQubit.K4Kernel.starSum_of_dressings (c1 := c y7) (c2 := c y9)
      (c3 := c y11) (r1 := c y2) (r2 := c y3) (r3 := c y5) (R1 := d z2)
      (R2 := d z3) (R3 := d z5) (C1 := d z7) (C2 := d z9) (C3 := d z11)
      (by linear_combination ho8) (by linear_combination ho9)
      (by linear_combination ho10) (by linear_combination ho11)
  obtain ⟨-, -, -, star4⟩ :=
    SixQubit.K4Kernel.starSum_of_dressings (c1 := c y8) (c2 := c y10)
      (c3 := c y11) (r1 := c y2) (r2 := c y3) (r3 := c y4) (R1 := d z2)
      (R2 := d z3) (R3 := d z4) (C1 := d z8) (C2 := d z10) (C3 := d z11)
      (by linear_combination ho12) (by linear_combination ho13)
      (by linear_combination ho14) (by linear_combination ho15)
  have f1 : star (c y2) * d z1 + star (c y1) * d z2 = 0 := by
    linear_combination ho16
  have f2 : star (c y3) * d z1 + star (c y1) * d z3 = 0 := by
    linear_combination ho17
  have f3 : star (c y4) * d z1 + star (c y1) * d z4 = 0 := by
    linear_combination ho18
  have f4 : star (c y5) * d z1 + star (c y1) * d z5 = 0 := by
    linear_combination ho19
  refine ⟨?_, ?_, ?_, ?_⟩
  · have key : d z1 * (star (c y6) * star (c y3) + star (c y7) * star (c y4) + star (c y8) * star (c y5)) = 0 := by
      linear_combination (star (c y6)) * f2 + (star (c y7)) * f3 + (star (c y8)) * f4 - (star (c y1)) * star1
    have h0 := (mul_eq_zero.mp key).resolve_left hBne
    have hs : star (c y6 * c y3 + c y7 * c y4 + c y8 * c y5) = 0 := by
      simp only [star_add, star_mul']
      exact h0
    exact star_eq_zero.mp hs
  · have key : d z1 * (star (c y6) * star (c y2) + star (c y9) * star (c y4) + star (c y10) * star (c y5)) = 0 := by
      linear_combination (star (c y6)) * f1 + (star (c y9)) * f3 + (star (c y10)) * f4 - (star (c y1)) * star2
    have h0 := (mul_eq_zero.mp key).resolve_left hBne
    have hs : star (c y6 * c y2 + c y9 * c y4 + c y10 * c y5) = 0 := by
      simp only [star_add, star_mul']
      exact h0
    exact star_eq_zero.mp hs
  · have key : d z1 * (star (c y7) * star (c y2) + star (c y9) * star (c y3) + star (c y11) * star (c y5)) = 0 := by
      linear_combination (star (c y7)) * f1 + (star (c y9)) * f2 + (star (c y11)) * f4 - (star (c y1)) * star3
    have h0 := (mul_eq_zero.mp key).resolve_left hBne
    have hs : star (c y7 * c y2 + c y9 * c y3 + c y11 * c y5) = 0 := by
      simp only [star_add, star_mul']
      exact h0
    exact star_eq_zero.mp hs
  · have key : d z1 * (star (c y8) * star (c y2) + star (c y10) * star (c y3) + star (c y11) * star (c y4)) = 0 := by
      linear_combination (star (c y8)) * f1 + (star (c y10)) * f2 + (star (c y11)) * f3 - (star (c y1)) * star4
    have h0 := (mul_eq_zero.mp key).resolve_left hBne
    have hs : star (c y8 * c y2 + c y10 * c y3 + c y11 * c y4) = 0 := by
      simp only [star_add, star_mul']
      exact h0
    exact star_eq_zero.mp hs

/-! ## 5.  Phase rigidity -/

set_option maxHeartbeats 1600000 in
/-- **Phase rigidity of orbit 36.**  Under exactly the hypotheses of
`SixQubit.Orbit36.magnitudes_forced` -- one moment system and twenty-one
vanishing Knill--Laflamme rows -- the six edge-phase products
`M_ij = r_i r_j c_ij` realize the unique proper three-edge-colouring of `K_4`:
opposite edges carry the same value, and the three colours are a common factor
`mu` of modulus squared `1/1500` times `1`, `w`, `w^2`.

The disjunction is the interchange of `w` and `w^2`, which the chapter
implements by a transposition of the first four physical qubits; nothing here
chooses between them. -/
theorem phase_rigidity (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5))
            (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5))
            (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)))
    (ho0 : offSum c d ex1 w0 = 0)
    (ho1 : offSum c d ex1 w2 = 0)
    (ho2 : offSum c d ex1 w3 = 0)
    (ho3 : offSum c d ex1 w4 = 0)
    (ho4 : offSum c d ex2 w0 = 0)
    (ho5 : offSum c d ex2 w1 = 0)
    (ho6 : offSum c d ex2 w3 = 0)
    (ho7 : offSum c d ex2 w4 = 0)
    (ho8 : offSum c d ex3 w0 = 0)
    (ho9 : offSum c d ex3 w1 = 0)
    (ho10 : offSum c d ex3 w2 = 0)
    (ho11 : offSum c d ex3 w4 = 0)
    (ho12 : offSum c d ex4 w0 = 0)
    (ho13 : offSum c d ex4 w1 = 0)
    (ho14 : offSum c d ex4 w2 = 0)
    (ho15 : offSum c d ex4 w3 = 0)
    (ho16 : offSum c d ex15 w0 = 0)
    (ho17 : offSum c d ex25 w0 = 0)
    (ho18 : offSum c d ex35 w0 = 0)
    (ho19 : offSum c d ex45 w0 = 0)
    (ho20 : offSum c d ex56 w0 = 0) :
    ∃ mu : ℂ, Complex.normSq mu = 1/1500
      ∧ c y2 * c y3 * c y6 = mu
      ∧ c y4 * c y5 * c y11 = mu
      ∧ ((c y2 * c y4 * c y7 = rho * mu ∧ c y3 * c y5 * c y10 = rho * mu
            ∧ c y2 * c y5 * c y8 = rho ^ 2 * mu
            ∧ c y3 * c y4 * c y9 = rho ^ 2 * mu)
          ∨ (c y2 * c y4 * c y7 = rho ^ 2 * mu
            ∧ c y3 * c y5 * c y10 = rho ^ 2 * mu
            ∧ c y2 * c y5 * c y8 = rho * mu
            ∧ c y3 * c y4 * c y9 = rho * mu)) := by
  obtain ⟨-, -, k2, k3, k4, k5, k6, k7, k8, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    magnitudes_forced c d hm ho0 ho1 ho2 ho3 ho4 ho5 ho6 ho7 ho8 ho9 ho10 ho11 ho12 ho13 ho14 ho15 ho16 ho17 ho18 ho19 ho20
  obtain ⟨e1, e2, e3, e4⟩ :=
    kernel_rows c d hm ho0 ho1 ho2 ho3 ho4 ho5 ho6 ho7 ho8 ho9 ho10 ho11 ho12 ho13 ho14 ho15 ho16 ho17 ho18 ho19
  obtain ⟨n12, g34, g24, g23, hcol⟩ :=
    edge_colouring k2 k3 k4 k5 k6 k7 k8 e1 e2 e3 e4
  refine ⟨c y2 * c y3 * c y6, n12, rfl, g34, ?_⟩
  rcases hcol with ⟨h13, h14⟩ | ⟨h13, h14⟩
  · exact Or.inl ⟨h13, g24.trans h13, h14, g23.trans h14⟩
  · exact Or.inr ⟨h13, g24.trans h13, h14, g23.trans h14⟩

/-! ## 6.  The chapter's normalized form -/

theorem sqrt1500 : Real.sqrt 1500 = 10 * Real.sqrt 15 := by
  rw [show (1500 : ℝ) = 100 * 15 by norm_num,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 100),
    show (100 : ℝ) = 10 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 10)]

/-- The chapter normalizes `u_i = sqrt 10 * r_i` and `v_ij = sqrt 15 * c_ij`,
so that `|u_i| = |v_ij| = 1`, and puts `M_ij = u_i u_j v_ij`.  That is the
positive rescaling `sqrt 1500` of the division-free product used above. -/
theorem normalized_edge_phase {r1 r2 c12 mu : ℂ} (h : r1 * r2 * c12 = mu) :
    ((Real.sqrt 10 : ℂ) * r1) * ((Real.sqrt 10 : ℂ) * r2)
      * ((Real.sqrt 15 : ℂ) * c12) = (Real.sqrt 1500 : ℂ) * mu := by
  have h10 : (Real.sqrt 10 : ℂ) * (Real.sqrt 10 : ℂ) = (10 : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 10)]
    norm_num
  have h15 : (Real.sqrt 1500 : ℂ) = 10 * (Real.sqrt 15 : ℂ) := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, ← sqrt1500]
  rw [h15, ← h]
  linear_combination ((Real.sqrt 15 : ℂ) * r1 * r2 * c12) * h10

/-- The normalized phases really are unit vectors: `normSq (sqrt 1500 * mu) = 1`
when `normSq mu = 1/1500`. -/
theorem normalized_unit {mu : ℂ} (h : Complex.normSq mu = 1/1500) :
    Complex.normSq ((Real.sqrt 1500 : ℂ) * mu) = 1 := by
  rw [map_mul, Complex.normSq_ofReal, h,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 1500)]
  norm_num

/-! ## 7.  The Shor--Laflamme enumerator -/

set_option maxRecDepth 40000

/-- `Tr (E * Pi)` for the rank-two code projector `Pi` of the logical pair
`(c, d)`, using the Hilbert-space semantics of `SS.HilbertKL`. -/
def projTrace (c d : SS.BitString 6 -> ℂ) (P : SS.PauliString 6) : ℂ :=
  SS.innerC c (SS.pauliAct P c) + SS.innerC d (SS.pauliAct P d)

/-- The Pauli strings of a given weight, indexed by their `(x, z)` mask pair. -/
def paulisOfWeight (j : ℕ) : Finset (SS.BitString 6 × SS.BitString 6) :=
  Finset.univ.filter (fun p => (SS.PauliString.mk p.1 p.2).wt = j)

/-- The Shor--Laflamme `A`-enumerator
`A_j = (1/4) * sum over weight-j Paulis of |Tr (E Pi)|^2`. -/
def AEnum (c d : SS.BitString 6 -> ℂ) (j : ℕ) : ℝ :=
  (∑ p ∈ paulisOfWeight j,
      Complex.normSq (projTrace c d (SS.PauliString.mk p.1 p.2))) / 4

/-- A whole coefficient vanishes as soon as every projector trace of that weight
does.  The index set is never enumerated: `Finset.sum_eq_zero` only needs the
pointwise statement. -/
theorem AEnum_eq_zero {c d : SS.BitString 6 -> ℂ} {j : ℕ}
    (h : ∀ P : SS.PauliString 6, P.wt = j → projTrace c d P = 0) :
    AEnum c d j = 0 := by
  have hz : ∀ p ∈ paulisOfWeight j,
      Complex.normSq (projTrace c d (SS.PauliString.mk p.1 p.2)) = 0 := by
    intro p hp
    rw [paulisOfWeight, Finset.mem_filter] at hp
    rw [h _ hp.2, Complex.normSq_zero]
  rw [AEnum, Finset.sum_eq_zero hz, zero_div]

theorem complement_injective :
    Function.Injective (SS.complement : SS.BitString 6 -> SS.BitString 6) := by
  intro x y h
  funext i
  exact Bool.not_inj (congrFun h i)

/-- **No incidence, no expectation.**  If no two points of either fiber differ
by the flip mask of `P`, both diagonal expectations are empty sums. -/
theorem projTrace_no_incidence {c d : SS.BitString 6 -> ℂ} {P : SS.PauliString 6}
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (h0 : S0.filter (fun s => SS.bxor s P.x ∈ S0) = ∅)
    (h1 : S1.filter (fun s => SS.bxor s P.x ∈ S1) = ∅) :
    projTrace c d P = 0 := by
  rw [projTrace, SS.innerC_pauliAct_support S0 S0 c c P hc hc,
    SS.innerC_pauliAct_support S1 S1 d d P hd hd, h0, h1]
  simp

/-- **The odd-`Z` cancellation.**  A Pauli with trivial flip mask is diagonal in
the computational basis, so each fiber contributes its own probabilities with a
Walsh sign.  Because the two fibers are exchanged by complementation and the two
probability vectors agree, an odd `z`-mask flips every sign and the two
contributions cancel term by term.  Only the moment data is used: no phase
information and no Knill--Laflamme row. -/
theorem projTrace_diag {c d : SS.BitString 6 -> ℂ} {P : SS.PauliString 6}
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (hmag : ∀ s ∈ S0, Complex.normSq (d (SS.complement s)) = Complex.normSq (c s))
    (hx : P.x = fun _ => false)
    (hodd : ∀ s : SS.BitString 6,
        SS.bdot P.z (SS.complement s) = !(SS.bdot P.z s)) :
    projTrace c d P = 0 := by
  have hf0 : S0.filter (fun s => SS.bxor s P.x ∈ S0) = S0 :=
    Finset.filter_true_of_mem (fun s hs => by rw [hx]; simpa using hs)
  have hf1 : S1.filter (fun s => SS.bxor s P.x ∈ S1) = S1 :=
    Finset.filter_true_of_mem (fun s hs => by rw [hx]; simpa using hs)
  have hinj : Set.InjOn SS.complement (S0 : Finset (SS.BitString 6)) :=
    fun _ _ _ _ h => complement_injective h
  rw [projTrace, SS.innerC_pauliAct_support S0 S0 c c P hc hc,
    SS.innerC_pauliAct_support S1 S1 d d P hd hd, hf0, hf1, ← mul_add]
  refine mul_eq_zero_of_right _ ?_
  rw [S1_eq_complement, Finset.sum_image hinj, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero ?_
  intro s hs
  rw [hx]
  simp only [SS.bxor_zero]
  rw [hodd s, SixQubit.star_mul_self, SixQubit.star_mul_self, hmag s hs]
  rcases Bool.eq_false_or_eq_true (SS.bdot P.z s) with hb | hb <;>
    rw [hb] <;> simp [SS.signC]

theorem hammingWt_x_le_wt (P : SS.PauliString 6) : SS.hammingWt P.x ≤ P.wt := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  rw [hi]
  rfl

theorem wt_eq_hammingWt_z {P : SS.PauliString 6} (h : P.x = fun _ => false) :
    P.wt = SS.hammingWt P.z := by
  simp only [SS.PauliString.wt, SS.hammingWt, h, Bool.false_or]

/-- **The weight-one flip masks.**  A mask of Hamming weight at most one is
either trivial or joins no two points of either fiber: `S_0` has no two points
at Hamming distance one, and neither has its complement.  Decided over all
sixty-four masks. -/
theorem mask_wt_le_one : ∀ f : SS.BitString 6, SS.hammingWt f ≤ 1 →
    f = (fun _ => false)
      ∨ (S0.filter (fun s => SS.bxor s f ∈ S0) = ∅
          ∧ S1.filter (fun s => SS.bxor s f ∈ S1) = ∅) := by
  decide

/-- An odd `z`-mask anticommutes with complementation. -/
theorem bdot_complement_of_odd : ∀ z s : SS.BitString 6,
    SS.hammingWt z % 2 = 1 → SS.bdot z (SS.complement s) = !(SS.bdot z s) := by
  decide

/-- Every weight-one Pauli has vanishing projector trace. -/
theorem projTrace_wt_one {c d : SS.BitString 6 -> ℂ} {P : SS.PauliString 6}
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (hmag : ∀ s ∈ S0, Complex.normSq (d (SS.complement s)) = Complex.normSq (c s))
    (hP : P.wt = 1) : projTrace c d P = 0 := by
  have hle : SS.hammingWt P.x ≤ 1 := by
    rw [← hP]
    exact hammingWt_x_le_wt P
  rcases mask_wt_le_one P.x hle with h0 | ⟨e0, e1⟩
  · refine projTrace_diag hc hd hmag h0 (fun s => ?_)
    refine bdot_complement_of_odd P.z s ?_
    rw [← wt_eq_hammingWt_z h0, hP]
  · exact projTrace_no_incidence hc hd e0 e1

/-- **`A_1 = 0` for every orbit-36 solution.**  The moment system alone forces
it: the eighteen weight-one Paulis split into the twelve `X_i`, `Y_i` rows,
whose flip mask joins no two points of a fiber, and the six `Z_i` rows, which
cancel between the two fibers because complementation exchanges the fibers,
reverses every odd Walsh sign, and preserves the probabilities.

No Knill--Laflamme row and no phase information is used. -/
theorem A1_eq_zero (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5))
            (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5))
            (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11))) :
    AEnum c d 1 = 0 := by
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, -, -, -, -, -, -, -, -⟩ :=
    hm.facts
  refine AEnum_eq_zero (fun P hP => projTrace_wt_one hc hd ?_ hP)
  intro s hs
  simp only [S0, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [← zc0]; exact t0.symm
  · rw [← zc1]; exact t1.symm
  · rw [← zc2]; exact t2.symm
  · rw [← zc3]; exact t3.symm
  · rw [← zc4]; exact t4.symm
  · rw [← zc5]; exact t5.symm
  · rw [← zc6]; exact t6.symm
  · rw [← zc7]; exact t7.symm
  · rw [← zc8]; exact t8.symm
  · rw [← zc9]; exact t9.symm
  · rw [← zc10]; exact t10.symm
  · rw [← zc11]; exact t11.symm

/-! ## 8.  The triangle identity behind `A_3 = 0` -/

/-- **The opposite triangle sums to zero.**  For the exceptional weight-three
flip mask `f = {i, 5, 6}` the three incidences of the bottom word pair `s_j`
with the edge complementary to `{i, j}`, and every one of the resulting terms is
`conj (r_j) * c_kl` for an edge `kl` of the triangle opposite `i`.  Multiplying
by `10 r_2 r_3 r_4` turns that sum into `M_34 + M_24 + M_23`, which the
three-edge-colouring makes `mu * (1 + w + w^2) = 0`.

This is the mechanism the chapter names for `A_3 = 0`; it is stated here for the
triangle opposite the first qubit, and is symmetric in `{1,2,3,4}`. -/
theorem triangle_sum {r2 r3 r4 c23 c24 c34 mu : ℂ}
    (p2 : Complex.normSq r2 = 1/10) (p3 : Complex.normSq r3 = 1/10)
    (p4 : Complex.normSq r4 = 1/10)
    (h34 : r3 * r4 * c34 = mu) (h24 : r2 * r4 * c24 = rho * mu)
    (h23 : r2 * r3 * c23 = rho ^ 2 * mu)
    (n2 : r2 ≠ 0) (n3 : r3 ≠ 0) (n4 : r4 ≠ 0) :
    star r2 * c34 + star r3 * c24 + star r4 * c23 = 0 := by
  have u2 : star r2 * r2 = (1/10 : ℂ) := by
    rw [SixQubit.star_mul_self, p2]; norm_num
  have u3 : star r3 * r3 = (1/10 : ℂ) := by
    rw [SixQubit.star_mul_self, p3]; norm_num
  have u4 : star r4 * r4 = (1/10 : ℂ) := by
    rw [SixQubit.star_mul_self, p4]; norm_num
  have key : (10 : ℂ) * (r2 * r3 * r4)
      * (star r2 * c34 + star r3 * c24 + star r4 * c23) = 0 := by
    linear_combination (10 * (r3 * r4 * c34)) * u2 + (10 * (r2 * r4 * c24)) * u3
      + (10 * (r2 * r3 * c23)) * u4 + h34 + h24 + h23 + mu * rho_quadratic
  have h10 : (10 : ℂ) * (r2 * r3 * r4) ≠ 0 := by
    refine mul_ne_zero (by norm_num) ?_
    exact mul_ne_zero (mul_ne_zero n2 n3) n4
  exact (mul_eq_zero.mp key).resolve_left h10

/-! ## 9.  The unique weight enumerator -/

/-- **The MacWilliams closing step.**  For any `((6,2,3))` code the quantum
MacWilliams relation together with `A_j = B_j` for `j <= 2` determines the
remaining Shor--Laflamme coefficients from `x = A_1`, `y = A_2`, `z = A_3`.
That relation is the hypothesis here, stated exactly as the chapter's normal
form; the lemma performs the substitution.

With the orbit-36 inputs `(A_1, A_2, A_3) = (0, 21/25, 0)` the boxed enumerator
`(1, 0, 21/25, 0, 291/25, 384/25, 79/25)` is the only possibility. -/
theorem macwilliams_normal_form (A0 A1 A2 A3 A4 A5 A6 : ℚ)
    (h0 : A0 = 1)
    (h4 : A4 = 15 - 4 * A2 - 3 * A3)
    (h5 : A5 = 12 + 3 * A1 + 4 * A2 + 3 * A3)
    (h6 : A6 = 4 - 4 * A1 - A2 - A3)
    (hx : A1 = 0) (hy : A2 = 21/25) (hz : A3 = 0) :
    A0 = 1 ∧ A1 = 0 ∧ A2 = 21/25 ∧ A3 = 0
      ∧ A4 = 291/25 ∧ A5 = 384/25 ∧ A6 = 79/25 := by
  refine ⟨h0, hx, hy, hz, ?_, ?_, ?_⟩
  · rw [h4, hy, hz]; norm_num
  · rw [h5, hx, hy, hz]; norm_num
  · rw [h6, hx, hy, hz]; norm_num

/-- The chapter's weight-two scalar table, summed: this is the arithmetic behind
`A_2 = 21/25`.  Eighteen two-qubit Paulis on the first four coordinates
contribute `1/15`, eight `Z_i Z_5` and `Z_i Z_6` rows contribute `+-1/5`, and
the three rows on the last two coordinates contribute `1/5`, `-1/5`, `-3/5`. -/
theorem weightTwo_table_sum :
    18 * (1/15 : ℚ) ^ 2 + 8 * (1/5 : ℚ) ^ 2 + (1/5 : ℚ) ^ 2
        + (-1/5 : ℚ) ^ 2 + (-3/5 : ℚ) ^ 2 = 21/25 := by
  norm_num

end

end SixQubit.Orbit36Phase
