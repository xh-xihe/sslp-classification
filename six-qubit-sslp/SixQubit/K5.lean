import Mathlib

import SS.FullKL
import SixQubit.Common
import SixQubit.Triangle

/-!
# The K_5 configuration behind orbit 30

Orbit 30 reduces to a configuration on `K_5`.  One string is distinguished
(`star`), five are *points* carrying amplitudes `b_i`, and ten are *edges*
carrying amplitudes `c_ij`.  The Walsh reduction of the ten admissible flip
masks produces, division free,

  * `star_i`  :  sum_{j != i} b_j c_ij = 0                     (`C b = 0`),
  * `kb`      :  b_p * k_ij = 0 for both endpoints p of ij,
                 where `k_ij` is the phase defect of the edge,
  * `hf_i`    :  a k-linear identity whose right-hand side is `2 s H_i`,
                 `H_i` the hafnian of the four-set `V \ {i}`,

together with the exact moment data
`sum_{j != i} |c_ij|^2 = |b_i|^2 + 1/8`, `sum |b_i|^2 = 3/8`,
`sum |c_ij|^2 = 1/2`.

The proof splits on which point amplitudes vanish.

  |A| = 0  the total point mass 3/8 is not zero;
  |A| = 1  every edge at the single active point is killed by `star`, and
           then its degree equation reads `0 = |b_a|^2 + 1/8`;
  |A| = 2  the edge between the two active points is killed by `star`, so the
           two weighted stars are edge disjoint and carry mass 5/8 > 1/2;
  |A| = 3  the moment data force the internal edge mass to be at least 1/4,
           and an internal edge propagates through `star` to the whole
           triangle, which is an odd triangle;
  |A| >= 4 every edge has an active endpoint, so every `k_ij` vanishes and
           `hf_i` collapses to `H_i = 0`.  The support graph then has minimum
           degree at least two, and `graph` closes every such support.

`graph` is a decision tree over the ten edge supports.  Its leaves use four
closing rules: a degree bound, a hafnian equation with a single surviving
monomial, an odd binomial cycle of three hafnian equations, and the
determinant identity

    det C + 32 c01 c02 c12 c34^2  =  Q0 H0 + Q1 H1 + Q2 H2 + Q3 H3

(and its ten vertex relabellings), which with `C b = 0` and `b != 0` forbids a
triangle whose complementary edge is also active.

`native_decide` is not used, and the module mentions no bit strings.
-/

namespace SixQubit.K5

open scoped ComplexConjugate

noncomputable section

/-! ## The support-graph decision tree -/

/-- **The support graph is impossible.**  A decision tree over the ten
edge supports; every leaf closes by a degree bound, by a hafnian
equation with one surviving monomial, by an odd binomial cycle, or by
the determinant identity. -/
theorem graph {c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 : ℂ}
    (haf0 : c12 * c34 + c13 * c24 + c14 * c23 = 0)
    (haf1 : c02 * c34 + c03 * c24 + c04 * c23 = 0)
    (haf2 : c01 * c34 + c03 * c14 + c04 * c13 = 0)
    (haf3 : c01 * c24 + c02 * c14 + c04 * c12 = 0)
    (haf4 : c01 * c23 + c02 * c13 + c03 * c12 = 0)
    (dg_0_1 : c02 = 0 → c03 = 0 → c04 = 0 → False)
    (dg_0_2 : c01 = 0 → c03 = 0 → c04 = 0 → False)
    (dg_0_3 : c01 = 0 → c02 = 0 → c04 = 0 → False)
    (dg_0_4 : c01 = 0 → c02 = 0 → c03 = 0 → False)
    (dg_1_0 : c12 = 0 → c13 = 0 → c14 = 0 → False)
    (dg_1_2 : c01 = 0 → c13 = 0 → c14 = 0 → False)
    (dg_1_3 : c01 = 0 → c12 = 0 → c14 = 0 → False)
    (dg_1_4 : c01 = 0 → c12 = 0 → c13 = 0 → False)
    (dg_2_0 : c12 = 0 → c23 = 0 → c24 = 0 → False)
    (dg_2_1 : c02 = 0 → c23 = 0 → c24 = 0 → False)
    (dg_2_3 : c02 = 0 → c12 = 0 → c24 = 0 → False)
    (dg_2_4 : c02 = 0 → c12 = 0 → c23 = 0 → False)
    (dg_3_0 : c13 = 0 → c23 = 0 → c34 = 0 → False)
    (dg_3_1 : c03 = 0 → c23 = 0 → c34 = 0 → False)
    (dg_3_2 : c03 = 0 → c13 = 0 → c34 = 0 → False)
    (dg_3_4 : c03 = 0 → c13 = 0 → c23 = 0 → False)
    (dg_4_0 : c14 = 0 → c24 = 0 → c34 = 0 → False)
    (dg_4_1 : c04 = 0 → c24 = 0 → c34 = 0 → False)
    (dg_4_2 : c04 = 0 → c14 = 0 → c34 = 0 → False)
    (dg_4_3 : c04 = 0 → c14 = 0 → c24 = 0 → False)
    (_det01 : c23 * c24 * c34 * c01 * c01 = 0)
    (_det02 : c13 * c14 * c34 * c02 * c02 = 0)
    (_det03 : c12 * c14 * c24 * c03 * c03 = 0)
    (det04 : c12 * c13 * c23 * c04 * c04 = 0)
    (_det12 : c03 * c04 * c34 * c12 * c12 = 0)
    (_det13 : c02 * c04 * c24 * c13 * c13 = 0)
    (det14 : c02 * c03 * c23 * c14 * c14 = 0)
    (det23 : c01 * c04 * c14 * c23 * c23 = 0)
    (det24 : c01 * c03 * c13 * c24 * c24 = 0)
    (_det34 : c01 * c02 * c12 * c34 * c34 = 0)
    : False := by
  rcases eq_or_ne c01 0 with q01 | q01
  · rcases eq_or_ne c02 0 with q02 | q02
    · rcases eq_or_ne c03 0 with q03 | q03
      · exact dg_0_4 q01 q02 q03
      · rcases eq_or_ne c04 0 with q04 | q04
        · exact dg_0_3 q01 q02 q04
        · rcases eq_or_ne c12 0 with q12 | q12
          · rcases eq_or_ne c13 0 with q13 | q13
            · exact dg_1_4 q01 q12 q13
            · rcases eq_or_ne c14 0 with q14 | q14
              · exact dg_1_3 q01 q12 q14
              · rcases eq_or_ne c23 0 with q23 | q23
                · exact dg_2_4 q02 q12 q23
                · rcases eq_or_ne c24 0 with q24 | q24
                  · exact dg_2_3 q02 q12 q24
                  · have hr0 : c13 * c24 + c14 * c23 = 0 := by
                      linear_combination haf0 - (c34 : ℂ) * q12
                    have hr1 : c04 * c23 + c03 * c24 = 0 := by
                      linear_combination haf1 - (c34 : ℂ) * q02
                    have hr2 : c03 * c14 + c04 * c13 = 0 := by
                      linear_combination haf2 - (c34 : ℂ) * q01
                    have key : (2 : ℂ) * ((c13 * c24) * (c04 * c23) * (c03 * c14)) = 0 := by
                      linear_combination ((c04 * c23) * (c03 * c14) : ℂ) * hr0 - ((c14 * c23) * (c03 * c14) : ℂ) * hr1
                        + ((c14 * c23) * (c03 * c24) : ℂ) * hr2
                    refine (mul_ne_zero (by norm_num : (2:ℂ) ≠ 0) (mul_ne_zero (mul_ne_zero (mul_ne_zero q13 q24) (mul_ne_zero q04 q23)) (mul_ne_zero q03 q14))) ?_
                    exact key
          · refine (mul_ne_zero q04 q12) ?_
            linear_combination haf3 - (c24 : ℂ) * q01 - (c14 : ℂ) * q02
    · rcases eq_or_ne c12 0 with q12 | q12
      · rcases eq_or_ne c13 0 with q13 | q13
        · exact dg_1_4 q01 q12 q13
        · refine (mul_ne_zero q02 q13) ?_
          linear_combination haf4 - (c23 : ℂ) * q01 - (c03 : ℂ) * q12
      · rcases eq_or_ne c03 0 with q03 | q03
        · rcases eq_or_ne c04 0 with q04 | q04
          · exact dg_0_2 q01 q03 q04
          · rcases eq_or_ne c13 0 with q13 | q13
            · rcases eq_or_ne c14 0 with q14 | q14
              · exact dg_1_2 q01 q13 q14
              · rcases eq_or_ne c23 0 with q23 | q23
                · exact dg_3_4 q03 q13 q23
                · rcases eq_or_ne c34 0 with q34 | q34
                  · exact dg_3_2 q03 q13 q34
                  · have hr0 : c12 * c34 + c14 * c23 = 0 := by
                      linear_combination haf0 - (c24 : ℂ) * q13
                    have hr1 : c04 * c23 + c02 * c34 = 0 := by
                      linear_combination haf1 - (c24 : ℂ) * q03
                    have hr2 : c02 * c14 + c04 * c12 = 0 := by
                      linear_combination haf3 - (c24 : ℂ) * q01
                    have key : (2 : ℂ) * ((c12 * c34) * (c04 * c23) * (c02 * c14)) = 0 := by
                      linear_combination ((c04 * c23) * (c02 * c14) : ℂ) * hr0 - ((c14 * c23) * (c02 * c14) : ℂ) * hr1
                        + ((c14 * c23) * (c02 * c34) : ℂ) * hr2
                    refine (mul_ne_zero (by norm_num : (2:ℂ) ≠ 0) (mul_ne_zero (mul_ne_zero (mul_ne_zero q12 q34) (mul_ne_zero q04 q23)) (mul_ne_zero q02 q14))) ?_
                    exact key
            · refine (mul_ne_zero q04 q13) ?_
              linear_combination haf2 - (c34 : ℂ) * q01 - (c14 : ℂ) * q03
        · rcases eq_or_ne c13 0 with q13 | q13
          · refine (mul_ne_zero q03 q12) ?_
            linear_combination haf4 - (c23 : ℂ) * q01 - (c02 : ℂ) * q13
          · rcases eq_or_ne c04 0 with q04 | q04
            · rcases eq_or_ne c14 0 with q14 | q14
              · rcases eq_or_ne c24 0 with q24 | q24
                · exact dg_4_3 q04 q14 q24
                · rcases eq_or_ne c34 0 with q34 | q34
                  · exact dg_4_2 q04 q14 q34
                  · have hr0 : c12 * c34 + c13 * c24 = 0 := by
                      linear_combination haf0 - (c23 : ℂ) * q14
                    have hr1 : c03 * c24 + c02 * c34 = 0 := by
                      linear_combination haf1 - (c23 : ℂ) * q04
                    have hr2 : c02 * c13 + c03 * c12 = 0 := by
                      linear_combination haf4 - (c23 : ℂ) * q01
                    have key : (2 : ℂ) * ((c12 * c34) * (c03 * c24) * (c02 * c13)) = 0 := by
                      linear_combination ((c03 * c24) * (c02 * c13) : ℂ) * hr0 - ((c13 * c24) * (c02 * c13) : ℂ) * hr1
                        + ((c13 * c24) * (c02 * c34) : ℂ) * hr2
                    refine (mul_ne_zero (by norm_num : (2:ℂ) ≠ 0) (mul_ne_zero (mul_ne_zero (mul_ne_zero q12 q34) (mul_ne_zero q03 q24)) (mul_ne_zero q02 q13))) ?_
                    exact key
              · refine (mul_ne_zero q03 q14) ?_
                linear_combination haf2 - (c34 : ℂ) * q01 - (c13 : ℂ) * q04
            · rcases eq_or_ne c14 0 with q14 | q14
              · refine (mul_ne_zero q04 q13) ?_
                linear_combination haf2 - (c34 : ℂ) * q01 - (c03 : ℂ) * q14
              · have hr0 : c03 * c14 + c04 * c13 = 0 := by
                  linear_combination haf2 - (c34 : ℂ) * q01
                have hr1 : c04 * c12 + c02 * c14 = 0 := by
                  linear_combination haf3 - (c24 : ℂ) * q01
                have hr2 : c02 * c13 + c03 * c12 = 0 := by
                  linear_combination haf4 - (c23 : ℂ) * q01
                have key : (2 : ℂ) * ((c03 * c14) * (c04 * c12) * (c02 * c13)) = 0 := by
                  linear_combination ((c04 * c12) * (c02 * c13) : ℂ) * hr0 - ((c04 * c13) * (c02 * c13) : ℂ) * hr1
                    + ((c04 * c13) * (c02 * c14) : ℂ) * hr2
                refine (mul_ne_zero (by norm_num : (2:ℂ) ≠ 0) (mul_ne_zero (mul_ne_zero (mul_ne_zero q03 q14) (mul_ne_zero q04 q12)) (mul_ne_zero q02 q13))) ?_
                exact key
  · rcases eq_or_ne c23 0 with q23 | q23
    · rcases eq_or_ne c02 0 with q02 | q02
      · rcases eq_or_ne c12 0 with q12 | q12
        · exact dg_2_4 q02 q12 q23
        · rcases eq_or_ne c03 0 with q03 | q03
          · rcases eq_or_ne c04 0 with q04 | q04
            · exact dg_0_1 q02 q03 q04
            · rcases eq_or_ne c13 0 with q13 | q13
              · exact dg_3_4 q03 q13 q23
              · rcases eq_or_ne c24 0 with q24 | q24
                · exact dg_2_1 q02 q23 q24
                · rcases eq_or_ne c34 0 with q34 | q34
                  · exact dg_3_1 q03 q23 q34
                  · have hr0 : c12 * c34 + c13 * c24 = 0 := by
                      linear_combination haf0 - (c14 : ℂ) * q23
                    have hr1 : c04 * c13 + c01 * c34 = 0 := by
                      linear_combination haf2 - (c14 : ℂ) * q03
                    have hr2 : c01 * c24 + c04 * c12 = 0 := by
                      linear_combination haf3 - (c14 : ℂ) * q02
                    have key : (2 : ℂ) * ((c12 * c34) * (c04 * c13) * (c01 * c24)) = 0 := by
                      linear_combination ((c04 * c13) * (c01 * c24) : ℂ) * hr0 - ((c13 * c24) * (c01 * c24) : ℂ) * hr1
                        + ((c13 * c24) * (c01 * c34) : ℂ) * hr2
                    refine (mul_ne_zero (by norm_num : (2:ℂ) ≠ 0) (mul_ne_zero (mul_ne_zero (mul_ne_zero q12 q34) (mul_ne_zero q04 q13)) (mul_ne_zero q01 q24))) ?_
                    exact key
          · refine (mul_ne_zero q03 q12) ?_
            linear_combination haf4 - (c01 : ℂ) * q23 - (c13 : ℂ) * q02
      · rcases eq_or_ne c03 0 with q03 | q03
        · rcases eq_or_ne c13 0 with q13 | q13
          · exact dg_3_4 q03 q13 q23
          · refine (mul_ne_zero q02 q13) ?_
            linear_combination haf4 - (c01 : ℂ) * q23 - (c12 : ℂ) * q03
        · rcases eq_or_ne c12 0 with q12 | q12
          · rcases eq_or_ne c13 0 with q13 | q13
            · rcases eq_or_ne c14 0 with q14 | q14
              · exact dg_1_0 q12 q13 q14
              · rcases eq_or_ne c24 0 with q24 | q24
                · exact dg_2_0 q12 q23 q24
                · rcases eq_or_ne c34 0 with q34 | q34
                  · exact dg_3_0 q13 q23 q34
                  · have hr0 : c02 * c34 + c03 * c24 = 0 := by
                      linear_combination haf1 - (c04 : ℂ) * q23
                    have hr1 : c03 * c14 + c01 * c34 = 0 := by
                      linear_combination haf2 - (c04 : ℂ) * q13
                    have hr2 : c01 * c24 + c02 * c14 = 0 := by
                      linear_combination haf3 - (c04 : ℂ) * q12
                    have key : (2 : ℂ) * ((c02 * c34) * (c03 * c14) * (c01 * c24)) = 0 := by
                      linear_combination ((c03 * c14) * (c01 * c24) : ℂ) * hr0 - ((c03 * c24) * (c01 * c24) : ℂ) * hr1
                        + ((c03 * c24) * (c01 * c34) : ℂ) * hr2
                    refine (mul_ne_zero (by norm_num : (2:ℂ) ≠ 0) (mul_ne_zero (mul_ne_zero (mul_ne_zero q02 q34) (mul_ne_zero q03 q14)) (mul_ne_zero q01 q24))) ?_
                    exact key
            · refine (mul_ne_zero q02 q13) ?_
              linear_combination haf4 - (c01 : ℂ) * q23 - (c03 : ℂ) * q12
          · rcases eq_or_ne c13 0 with q13 | q13
            · refine (mul_ne_zero q03 q12) ?_
              linear_combination haf4 - (c01 : ℂ) * q23 - (c02 : ℂ) * q13
            · rcases eq_or_ne c24 0 with q24 | q24
              · rcases eq_or_ne c34 0 with q34 | q34
                · rcases eq_or_ne c04 0 with q04 | q04
                  · exact dg_4_1 q04 q24 q34
                  · rcases eq_or_ne c14 0 with q14 | q14
                    · exact dg_4_0 q14 q24 q34
                    · have hr0 : c03 * c14 + c04 * c13 = 0 := by
                        linear_combination haf2 - (c01 : ℂ) * q34
                      have hr1 : c04 * c12 + c02 * c14 = 0 := by
                        linear_combination haf3 - (c01 : ℂ) * q24
                      have hr2 : c02 * c13 + c03 * c12 = 0 := by
                        linear_combination haf4 - (c01 : ℂ) * q23
                      have key : (2 : ℂ) * ((c03 * c14) * (c04 * c12) * (c02 * c13)) = 0 := by
                        linear_combination ((c04 * c12) * (c02 * c13) : ℂ) * hr0 - ((c04 * c13) * (c02 * c13) : ℂ) * hr1
                          + ((c04 * c13) * (c02 * c14) : ℂ) * hr2
                      refine (mul_ne_zero (by norm_num : (2:ℂ) ≠ 0) (mul_ne_zero (mul_ne_zero (mul_ne_zero q03 q14) (mul_ne_zero q04 q12)) (mul_ne_zero q02 q13))) ?_
                      exact key
                · refine (mul_ne_zero q12 q34) ?_
                  linear_combination haf0 - (c13 : ℂ) * q24 - (c14 : ℂ) * q23
              · refine (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero q01 q03) q13) q24) q24) ?_
                exact det24
    · rcases eq_or_ne c04 0 with q04 | q04
      · rcases eq_or_ne c14 0 with q14 | q14
        · rcases eq_or_ne c24 0 with q24 | q24
          · exact dg_4_3 q04 q14 q24
          · refine (mul_ne_zero q01 q24) ?_
            linear_combination haf3 - (c02 : ℂ) * q14 - (c12 : ℂ) * q04
        · rcases eq_or_ne c02 0 with q02 | q02
          · rcases eq_or_ne c03 0 with q03 | q03
            · exact dg_0_1 q02 q03 q04
            · rcases eq_or_ne c12 0 with q12 | q12
              · refine (mul_ne_zero q01 q23) ?_
                linear_combination haf4 - (c13 : ℂ) * q02 - (c03 : ℂ) * q12
              · rcases eq_or_ne c24 0 with q24 | q24
                · rcases eq_or_ne c34 0 with q34 | q34
                  · exact dg_4_1 q04 q24 q34
                  · have hr0 : c12 * c34 + c14 * c23 = 0 := by
                      linear_combination haf0 - (c13 : ℂ) * q24
                    have hr1 : c03 * c14 + c01 * c34 = 0 := by
                      linear_combination haf2 - (c13 : ℂ) * q04
                    have hr2 : c01 * c23 + c03 * c12 = 0 := by
                      linear_combination haf4 - (c13 : ℂ) * q02
                    have key : (2 : ℂ) * ((c12 * c34) * (c03 * c14) * (c01 * c23)) = 0 := by
                      linear_combination ((c03 * c14) * (c01 * c23) : ℂ) * hr0 - ((c14 * c23) * (c01 * c23) : ℂ) * hr1
                        + ((c14 * c23) * (c01 * c34) : ℂ) * hr2
                    refine (mul_ne_zero (by norm_num : (2:ℂ) ≠ 0) (mul_ne_zero (mul_ne_zero (mul_ne_zero q12 q34) (mul_ne_zero q03 q14)) (mul_ne_zero q01 q23))) ?_
                    exact key
                · refine (mul_ne_zero q03 q24) ?_
                  linear_combination haf1 - (c34 : ℂ) * q02 - (c23 : ℂ) * q04
          · rcases eq_or_ne c03 0 with q03 | q03
            · rcases eq_or_ne c13 0 with q13 | q13
              · refine (mul_ne_zero q01 q23) ?_
                linear_combination haf4 - (c02 : ℂ) * q13 - (c12 : ℂ) * q03
              · rcases eq_or_ne c24 0 with q24 | q24
                · refine (mul_ne_zero q02 q14) ?_
                  linear_combination haf3 - (c01 : ℂ) * q24 - (c12 : ℂ) * q04
                · rcases eq_or_ne c34 0 with q34 | q34
                  · have hr0 : c13 * c24 + c14 * c23 = 0 := by
                      linear_combination haf0 - (c12 : ℂ) * q34
                    have hr1 : c02 * c14 + c01 * c24 = 0 := by
                      linear_combination haf3 - (c12 : ℂ) * q04
                    have hr2 : c01 * c23 + c02 * c13 = 0 := by
                      linear_combination haf4 - (c12 : ℂ) * q03
                    have key : (2 : ℂ) * ((c13 * c24) * (c02 * c14) * (c01 * c23)) = 0 := by
                      linear_combination ((c02 * c14) * (c01 * c23) : ℂ) * hr0 - ((c14 * c23) * (c01 * c23) : ℂ) * hr1
                        + ((c14 * c23) * (c01 * c24) : ℂ) * hr2
                    refine (mul_ne_zero (by norm_num : (2:ℂ) ≠ 0) (mul_ne_zero (mul_ne_zero (mul_ne_zero q13 q24) (mul_ne_zero q02 q14)) (mul_ne_zero q01 q23))) ?_
                    exact key
                  · refine (mul_ne_zero q02 q34) ?_
                    linear_combination haf1 - (c24 : ℂ) * q03 - (c23 : ℂ) * q04
            · refine (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero q02 q03) q23) q14) q14) ?_
              exact det14
      · rcases eq_or_ne c14 0 with q14 | q14
        · rcases eq_or_ne c12 0 with q12 | q12
          · rcases eq_or_ne c02 0 with q02 | q02
            · refine (mul_ne_zero q01 q23) ?_
              linear_combination haf4 - (c13 : ℂ) * q02 - (c03 : ℂ) * q12
            · rcases eq_or_ne c13 0 with q13 | q13
              · exact dg_1_0 q12 q13 q14
              · rcases eq_or_ne c24 0 with q24 | q24
                · rcases eq_or_ne c34 0 with q34 | q34
                  · exact dg_4_0 q14 q24 q34
                  · have hr0 : c02 * c34 + c04 * c23 = 0 := by
                      linear_combination haf1 - (c03 : ℂ) * q24
                    have hr1 : c04 * c13 + c01 * c34 = 0 := by
                      linear_combination haf2 - (c03 : ℂ) * q14
                    have hr2 : c01 * c23 + c02 * c13 = 0 := by
                      linear_combination haf4 - (c03 : ℂ) * q12
                    have key : (2 : ℂ) * ((c02 * c34) * (c04 * c13) * (c01 * c23)) = 0 := by
                      linear_combination ((c04 * c13) * (c01 * c23) : ℂ) * hr0 - ((c04 * c23) * (c01 * c23) : ℂ) * hr1
                        + ((c04 * c23) * (c01 * c34) : ℂ) * hr2
                    refine (mul_ne_zero (by norm_num : (2:ℂ) ≠ 0) (mul_ne_zero (mul_ne_zero (mul_ne_zero q02 q34) (mul_ne_zero q04 q13)) (mul_ne_zero q01 q23))) ?_
                    exact key
                · refine (mul_ne_zero q13 q24) ?_
                  linear_combination haf0 - (c34 : ℂ) * q12 - (c23 : ℂ) * q14
          · rcases eq_or_ne c13 0 with q13 | q13
            · rcases eq_or_ne c03 0 with q03 | q03
              · refine (mul_ne_zero q01 q23) ?_
                linear_combination haf4 - (c02 : ℂ) * q13 - (c12 : ℂ) * q03
              · rcases eq_or_ne c24 0 with q24 | q24
                · refine (mul_ne_zero q04 q12) ?_
                  linear_combination haf3 - (c01 : ℂ) * q24 - (c02 : ℂ) * q14
                · rcases eq_or_ne c34 0 with q34 | q34
                  · have hr0 : c03 * c24 + c04 * c23 = 0 := by
                      linear_combination haf1 - (c02 : ℂ) * q34
                    have hr1 : c04 * c12 + c01 * c24 = 0 := by
                      linear_combination haf3 - (c02 : ℂ) * q14
                    have hr2 : c01 * c23 + c03 * c12 = 0 := by
                      linear_combination haf4 - (c02 : ℂ) * q13
                    have key : (2 : ℂ) * ((c03 * c24) * (c04 * c12) * (c01 * c23)) = 0 := by
                      linear_combination ((c04 * c12) * (c01 * c23) : ℂ) * hr0 - ((c04 * c23) * (c01 * c23) : ℂ) * hr1
                        + ((c04 * c23) * (c01 * c24) : ℂ) * hr2
                    refine (mul_ne_zero (by norm_num : (2:ℂ) ≠ 0) (mul_ne_zero (mul_ne_zero (mul_ne_zero q03 q24) (mul_ne_zero q04 q12)) (mul_ne_zero q01 q23))) ?_
                    exact key
                  · refine (mul_ne_zero q12 q34) ?_
                    linear_combination haf0 - (c24 : ℂ) * q13 - (c23 : ℂ) * q14
            · refine (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero q12 q13) q23) q04) q04) ?_
              exact det04
        · refine (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero q01 q04) q14) q23) q23) ?_
          exact det23

/-! ## The determinant identities -/

/-- The determinant identity, in the ten shapes obtained by relabelling
the vertices, cancelled against the nonzero point amplitude `b0`. -/
theorem dets0 {b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 : ℂ}
    (st0 : b1 * c01 + b2 * c02 + b3 * c03 + b4 * c04 = 0)
    (st1 : b0 * c01 + b2 * c12 + b3 * c13 + b4 * c14 = 0)
    (st2 : b0 * c02 + b1 * c12 + b3 * c23 + b4 * c24 = 0)
    (st3 : b0 * c03 + b1 * c13 + b2 * c23 + b4 * c34 = 0)
    (st4 : b0 * c04 + b1 * c14 + b2 * c24 + b3 * c34 = 0)
    (haf0 : c12 * c34 + c13 * c24 + c14 * c23 = 0)
    (haf1 : c02 * c34 + c03 * c24 + c04 * c23 = 0)
    (haf2 : c01 * c34 + c03 * c14 + c04 * c13 = 0)
    (haf3 : c01 * c24 + c02 * c14 + c04 * c12 = 0)
    (haf4 : c01 * c23 + c02 * c13 + c03 * c12 = 0)
    (hb : b0 ≠ 0) :
    c23 * c24 * c34 * c01 * c01 = 0
      ∧ c13 * c14 * c34 * c02 * c02 = 0
      ∧ c12 * c14 * c24 * c03 * c03 = 0
      ∧ c12 * c13 * c23 * c04 * c04 = 0
      ∧ c03 * c04 * c34 * c12 * c12 = 0
      ∧ c02 * c04 * c24 * c13 * c13 = 0
      ∧ c02 * c03 * c23 * c14 * c14 = 0
      ∧ c01 * c04 * c14 * c23 * c23 = 0
      ∧ c01 * c03 * c13 * c24 * c24 = 0
      ∧ c01 * c02 * c12 * c34 * c34 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hx : c23 * c24 * c34 * c01 * c01 * b0 = 0 := by
      linear_combination (((-8*c01*c02*c34 - 8*c01*c03*c24 - 18*c01*c04*c23 + 8*c02*c03*c14 - 2*c02*c04*c13 - 2*c03*c04*c12) * b0) / 32 : ℂ) * haf0
        + (((10*c01*c12*c34 + 10*c01*c13*c24 - 2*c02*c13*c14 - 2*c03*c12*c14 + 8*c04*c12*c13) * b0) / 32 : ℂ) * haf1
        + (((30*c01*c23*c24 - 4*c02*c12*c34 + 10*c02*c14*c23 + 10*c04*c12*c23) * b0) / 32 : ℂ) * haf2
        + (((-4*c03*c13*c24 - 20*c03*c14*c23 - 20*c04*c13*c23) * b0) / 32 : ℂ) * haf3
        + (((16*c04*c14*c23) * b0) / 32 : ℂ) * haf4
        - ((c12^2*c34^2 - 2*c12*c13*c24*c34 - 2*c12*c14*c23*c34 + c13^2*c24^2 - 2*c13*c14*c23*c24 + c14^2*c23^2) / 32 : ℂ) * st0
        - ((-2*c01*c23*c24*c34 - c02*c12*c34^2 + c02*c13*c24*c34 + c02*c14*c23*c34 + c03*c12*c24*c34 - c03*c13*c24^2 + c03*c14*c23*c24 + c04*c12*c23*c34 + c04*c13*c23*c24 - c04*c14*c23^2) / 32 : ℂ) * st1
        - ((-c01*c12*c34^2 + c01*c13*c24*c34 + c01*c14*c23*c34 - 2*c02*c13*c14*c34 + c03*c12*c14*c34 + c03*c13*c14*c24 - c03*c14^2*c23 + c04*c12*c13*c34 - c04*c13^2*c24 + c04*c13*c14*c23) / 32 : ℂ) * st2
        - ((c01*c12*c24*c34 - c01*c13*c24^2 + c01*c14*c23*c24 + c02*c12*c14*c34 + c02*c13*c14*c24 - c02*c14^2*c23 - 2*c03*c12*c14*c24 - c04*c12^2*c34 + c04*c12*c13*c24 + c04*c12*c14*c23) / 32 : ℂ) * st3
        - ((c01*c12*c23*c34 + c01*c13*c23*c24 - c01*c14*c23^2 + c02*c12*c13*c34 - c02*c13^2*c24 + c02*c13*c14*c23 - c03*c12^2*c34 + c03*c12*c13*c24 + c03*c12*c14*c23 - 2*c04*c12*c13*c23) / 32 : ℂ) * st4
    rcases mul_eq_zero.mp hx with y | y
    · exact y
    · exact absurd y hb
  · have hx : c13 * c14 * c34 * c02 * c02 * b0 = 0 := by
      linear_combination (((-8*c01*c02*c34 + 8*c01*c03*c24 - 2*c01*c04*c23 - 8*c02*c03*c14 - 18*c02*c04*c13 - 2*c03*c04*c12) * b0) / 32 : ℂ) * haf0
        + (((-6*c01*c12*c34 + 10*c01*c13*c24 + 30*c02*c13*c14 - 2*c03*c12*c14 + 8*c04*c12*c13) * b0) / 32 : ℂ) * haf1
        + (((-2*c01*c23*c24 + 12*c02*c12*c34 + 10*c02*c14*c23 + 10*c04*c12*c23) * b0) / 32 : ℂ) * haf2
        + (((-20*c03*c13*c24 - 4*c03*c14*c23 - 20*c04*c13*c23) * b0) / 32 : ℂ) * haf3
        + (((16*c04*c13*c24) * b0) / 32 : ℂ) * haf4
        - ((c12^2*c34^2 - 2*c12*c13*c24*c34 - 2*c12*c14*c23*c34 + c13^2*c24^2 - 2*c13*c14*c23*c24 + c14^2*c23^2) / 32 : ℂ) * st0
        - ((-2*c01*c23*c24*c34 - c02*c12*c34^2 + c02*c13*c24*c34 + c02*c14*c23*c34 + c03*c12*c24*c34 - c03*c13*c24^2 + c03*c14*c23*c24 + c04*c12*c23*c34 + c04*c13*c23*c24 - c04*c14*c23^2) / 32 : ℂ) * st1
        - ((-c01*c12*c34^2 + c01*c13*c24*c34 + c01*c14*c23*c34 - 2*c02*c13*c14*c34 + c03*c12*c14*c34 + c03*c13*c14*c24 - c03*c14^2*c23 + c04*c12*c13*c34 - c04*c13^2*c24 + c04*c13*c14*c23) / 32 : ℂ) * st2
        - ((c01*c12*c24*c34 - c01*c13*c24^2 + c01*c14*c23*c24 + c02*c12*c14*c34 + c02*c13*c14*c24 - c02*c14^2*c23 - 2*c03*c12*c14*c24 - c04*c12^2*c34 + c04*c12*c13*c24 + c04*c12*c14*c23) / 32 : ℂ) * st3
        - ((c01*c12*c23*c34 + c01*c13*c23*c24 - c01*c14*c23^2 + c02*c12*c13*c34 - c02*c13^2*c24 + c02*c13*c14*c23 - c03*c12^2*c34 + c03*c12*c13*c24 + c03*c12*c14*c23 - 2*c04*c12*c13*c23) / 32 : ℂ) * st4
    rcases mul_eq_zero.mp hx with y | y
    · exact y
    · exact absurd y hb
  · have hx : c12 * c14 * c24 * c03 * c03 * b0 = 0 := by
      linear_combination (((8*c01*c02*c34 - 8*c01*c03*c24 + 14*c01*c04*c23 - 8*c02*c03*c14 + 14*c02*c04*c13 - 2*c03*c04*c12) * b0) / 32 : ℂ) * haf0
        + (((10*c01*c12*c34 - 6*c01*c13*c24 - 2*c02*c13*c14 + 30*c03*c12*c14 + 8*c04*c12*c13) * b0) / 32 : ℂ) * haf1
        + (((-2*c01*c23*c24 - 20*c02*c12*c34 - 6*c02*c14*c23 - 22*c04*c12*c23) * b0) / 32 : ℂ) * haf2
        + (((12*c03*c13*c24 + 12*c03*c14*c23 + 12*c04*c13*c23) * b0) / 32 : ℂ) * haf3
        + (((-16*c04*c13*c24 - 16*c04*c14*c23) * b0) / 32 : ℂ) * haf4
        - ((c12^2*c34^2 - 2*c12*c13*c24*c34 - 2*c12*c14*c23*c34 + c13^2*c24^2 - 2*c13*c14*c23*c24 + c14^2*c23^2) / 32 : ℂ) * st0
        - ((-2*c01*c23*c24*c34 - c02*c12*c34^2 + c02*c13*c24*c34 + c02*c14*c23*c34 + c03*c12*c24*c34 - c03*c13*c24^2 + c03*c14*c23*c24 + c04*c12*c23*c34 + c04*c13*c23*c24 - c04*c14*c23^2) / 32 : ℂ) * st1
        - ((-c01*c12*c34^2 + c01*c13*c24*c34 + c01*c14*c23*c34 - 2*c02*c13*c14*c34 + c03*c12*c14*c34 + c03*c13*c14*c24 - c03*c14^2*c23 + c04*c12*c13*c34 - c04*c13^2*c24 + c04*c13*c14*c23) / 32 : ℂ) * st2
        - ((c01*c12*c24*c34 - c01*c13*c24^2 + c01*c14*c23*c24 + c02*c12*c14*c34 + c02*c13*c14*c24 - c02*c14^2*c23 - 2*c03*c12*c14*c24 - c04*c12^2*c34 + c04*c12*c13*c24 + c04*c12*c14*c23) / 32 : ℂ) * st3
        - ((c01*c12*c23*c34 + c01*c13*c23*c24 - c01*c14*c23^2 + c02*c12*c13*c34 - c02*c13^2*c24 + c02*c13*c14*c23 - c03*c12^2*c34 + c03*c12*c13*c24 + c03*c12*c14*c23 - 2*c04*c12*c13*c23) / 32 : ℂ) * st4
    rcases mul_eq_zero.mp hx with y | y
    · exact y
    · exact absurd y hb
  · have hx : c12 * c13 * c23 * c04 * c04 * b0 = 0 := by
      linear_combination (((8*c01*c02*c34 + 8*c01*c03*c24 - 2*c01*c04*c23 + 8*c02*c03*c14 - 2*c02*c04*c13 - 2*c03*c04*c12) * b0) / 32 : ℂ) * haf0
        + (((-6*c01*c12*c34 - 6*c01*c13*c24 - 2*c02*c13*c14 - 2*c03*c12*c14 + 8*c04*c12*c13) * b0) / 32 : ℂ) * haf1
        + (((-2*c01*c23*c24 - 4*c02*c12*c34 - 6*c02*c14*c23 + 10*c04*c12*c23) * b0) / 32 : ℂ) * haf2
        + (((-4*c03*c13*c24 - 4*c03*c14*c23 + 12*c04*c13*c23) * b0) / 32 : ℂ) * haf3
        - ((c12^2*c34^2 - 2*c12*c13*c24*c34 - 2*c12*c14*c23*c34 + c13^2*c24^2 - 2*c13*c14*c23*c24 + c14^2*c23^2) / 32 : ℂ) * st0
        - ((-2*c01*c23*c24*c34 - c02*c12*c34^2 + c02*c13*c24*c34 + c02*c14*c23*c34 + c03*c12*c24*c34 - c03*c13*c24^2 + c03*c14*c23*c24 + c04*c12*c23*c34 + c04*c13*c23*c24 - c04*c14*c23^2) / 32 : ℂ) * st1
        - ((-c01*c12*c34^2 + c01*c13*c24*c34 + c01*c14*c23*c34 - 2*c02*c13*c14*c34 + c03*c12*c14*c34 + c03*c13*c14*c24 - c03*c14^2*c23 + c04*c12*c13*c34 - c04*c13^2*c24 + c04*c13*c14*c23) / 32 : ℂ) * st2
        - ((c01*c12*c24*c34 - c01*c13*c24^2 + c01*c14*c23*c24 + c02*c12*c14*c34 + c02*c13*c14*c24 - c02*c14^2*c23 - 2*c03*c12*c14*c24 - c04*c12^2*c34 + c04*c12*c13*c24 + c04*c12*c14*c23) / 32 : ℂ) * st3
        - ((c01*c12*c23*c34 + c01*c13*c23*c24 - c01*c14*c23^2 + c02*c12*c13*c34 - c02*c13^2*c24 + c02*c13*c14*c23 - c03*c12^2*c34 + c03*c12*c13*c24 + c03*c12*c14*c23 - 2*c04*c12*c13*c23) / 32 : ℂ) * st4
    rcases mul_eq_zero.mp hx with y | y
    · exact y
    · exact absurd y hb
  · have hx : c03 * c04 * c34 * c12 * c12 * b0 = 0 := by
      linear_combination (((8*c01*c02*c34 + 8*c01*c03*c24 + 14*c01*c04*c23 + 8*c02*c03*c14 + 14*c02*c04*c13 + 30*c03*c04*c12) * b0) / 32 : ℂ) * haf0
        + (((-6*c01*c12*c34 - 6*c01*c13*c24 - 2*c02*c13*c14 - 2*c03*c12*c14 - 8*c04*c12*c13) * b0) / 32 : ℂ) * haf1
        + (((-2*c01*c23*c24 - 4*c02*c12*c34 - 6*c02*c14*c23 - 6*c04*c12*c23) * b0) / 32 : ℂ) * haf2
        + (((-4*c03*c13*c24 - 4*c03*c14*c23 + 12*c04*c13*c23) * b0) / 32 : ℂ) * haf3
        + (((-16*c04*c13*c24 - 16*c04*c14*c23) * b0) / 32 : ℂ) * haf4
        - ((c12^2*c34^2 - 2*c12*c13*c24*c34 - 2*c12*c14*c23*c34 + c13^2*c24^2 - 2*c13*c14*c23*c24 + c14^2*c23^2) / 32 : ℂ) * st0
        - ((-2*c01*c23*c24*c34 - c02*c12*c34^2 + c02*c13*c24*c34 + c02*c14*c23*c34 + c03*c12*c24*c34 - c03*c13*c24^2 + c03*c14*c23*c24 + c04*c12*c23*c34 + c04*c13*c23*c24 - c04*c14*c23^2) / 32 : ℂ) * st1
        - ((-c01*c12*c34^2 + c01*c13*c24*c34 + c01*c14*c23*c34 - 2*c02*c13*c14*c34 + c03*c12*c14*c34 + c03*c13*c14*c24 - c03*c14^2*c23 + c04*c12*c13*c34 - c04*c13^2*c24 + c04*c13*c14*c23) / 32 : ℂ) * st2
        - ((c01*c12*c24*c34 - c01*c13*c24^2 + c01*c14*c23*c24 + c02*c12*c14*c34 + c02*c13*c14*c24 - c02*c14^2*c23 - 2*c03*c12*c14*c24 - c04*c12^2*c34 + c04*c12*c13*c24 + c04*c12*c14*c23) / 32 : ℂ) * st3
        - ((c01*c12*c23*c34 + c01*c13*c23*c24 - c01*c14*c23^2 + c02*c12*c13*c34 - c02*c13^2*c24 + c02*c13*c14*c23 - c03*c12^2*c34 + c03*c12*c13*c24 + c03*c12*c14*c23 - 2*c04*c12*c13*c23) / 32 : ℂ) * st4
    rcases mul_eq_zero.mp hx with y | y
    · exact y
    · exact absurd y hb
  · have hx : c02 * c04 * c24 * c13 * c13 * b0 = 0 := by
      linear_combination (((8*c01*c02*c34 + 8*c01*c03*c24 - 2*c01*c04*c23 + 8*c02*c03*c14 + 14*c02*c04*c13 - 2*c03*c04*c12) * b0) / 32 : ℂ) * haf0
        + (((-6*c01*c12*c34 - 6*c01*c13*c24 - 2*c02*c13*c14 - 2*c03*c12*c14 - 8*c04*c12*c13) * b0) / 32 : ℂ) * haf1
        + (((-2*c01*c23*c24 - 4*c02*c12*c34 - 6*c02*c14*c23 + 10*c04*c12*c23) * b0) / 32 : ℂ) * haf2
        + (((-4*c03*c13*c24 - 4*c03*c14*c23 - 4*c04*c13*c23) * b0) / 32 : ℂ) * haf3
        + (((16*c04*c13*c24) * b0) / 32 : ℂ) * haf4
        - ((c12^2*c34^2 - 2*c12*c13*c24*c34 - 2*c12*c14*c23*c34 + c13^2*c24^2 - 2*c13*c14*c23*c24 + c14^2*c23^2) / 32 : ℂ) * st0
        - ((-2*c01*c23*c24*c34 - c02*c12*c34^2 + c02*c13*c24*c34 + c02*c14*c23*c34 + c03*c12*c24*c34 - c03*c13*c24^2 + c03*c14*c23*c24 + c04*c12*c23*c34 + c04*c13*c23*c24 - c04*c14*c23^2) / 32 : ℂ) * st1
        - ((-c01*c12*c34^2 + c01*c13*c24*c34 + c01*c14*c23*c34 - 2*c02*c13*c14*c34 + c03*c12*c14*c34 + c03*c13*c14*c24 - c03*c14^2*c23 + c04*c12*c13*c34 - c04*c13^2*c24 + c04*c13*c14*c23) / 32 : ℂ) * st2
        - ((c01*c12*c24*c34 - c01*c13*c24^2 + c01*c14*c23*c24 + c02*c12*c14*c34 + c02*c13*c14*c24 - c02*c14^2*c23 - 2*c03*c12*c14*c24 - c04*c12^2*c34 + c04*c12*c13*c24 + c04*c12*c14*c23) / 32 : ℂ) * st3
        - ((c01*c12*c23*c34 + c01*c13*c23*c24 - c01*c14*c23^2 + c02*c12*c13*c34 - c02*c13^2*c24 + c02*c13*c14*c23 - c03*c12^2*c34 + c03*c12*c13*c24 + c03*c12*c14*c23 - 2*c04*c12*c13*c23) / 32 : ℂ) * st4
    rcases mul_eq_zero.mp hx with y | y
    · exact y
    · exact absurd y hb
  · have hx : c02 * c03 * c23 * c14 * c14 * b0 = 0 := by
      linear_combination (((-8*c01*c02*c34 - 8*c01*c03*c24 - 2*c01*c04*c23 + 8*c02*c03*c14 - 2*c02*c04*c13 - 2*c03*c04*c12) * b0) / 32 : ℂ) * haf0
        + (((10*c01*c12*c34 + 10*c01*c13*c24 - 2*c02*c13*c14 - 2*c03*c12*c14 + 8*c04*c12*c13) * b0) / 32 : ℂ) * haf1
        + (((-2*c01*c23*c24 - 4*c02*c12*c34 + 10*c02*c14*c23 - 6*c04*c12*c23) * b0) / 32 : ℂ) * haf2
        + (((-4*c03*c13*c24 + 12*c03*c14*c23 - 4*c04*c13*c23) * b0) / 32 : ℂ) * haf3
        - ((c12^2*c34^2 - 2*c12*c13*c24*c34 - 2*c12*c14*c23*c34 + c13^2*c24^2 - 2*c13*c14*c23*c24 + c14^2*c23^2) / 32 : ℂ) * st0
        - ((-2*c01*c23*c24*c34 - c02*c12*c34^2 + c02*c13*c24*c34 + c02*c14*c23*c34 + c03*c12*c24*c34 - c03*c13*c24^2 + c03*c14*c23*c24 + c04*c12*c23*c34 + c04*c13*c23*c24 - c04*c14*c23^2) / 32 : ℂ) * st1
        - ((-c01*c12*c34^2 + c01*c13*c24*c34 + c01*c14*c23*c34 - 2*c02*c13*c14*c34 + c03*c12*c14*c34 + c03*c13*c14*c24 - c03*c14^2*c23 + c04*c12*c13*c34 - c04*c13^2*c24 + c04*c13*c14*c23) / 32 : ℂ) * st2
        - ((c01*c12*c24*c34 - c01*c13*c24^2 + c01*c14*c23*c24 + c02*c12*c14*c34 + c02*c13*c14*c24 - c02*c14^2*c23 - 2*c03*c12*c14*c24 - c04*c12^2*c34 + c04*c12*c13*c24 + c04*c12*c14*c23) / 32 : ℂ) * st3
        - ((c01*c12*c23*c34 + c01*c13*c23*c24 - c01*c14*c23^2 + c02*c12*c13*c34 - c02*c13^2*c24 + c02*c13*c14*c23 - c03*c12^2*c34 + c03*c12*c13*c24 + c03*c12*c14*c23 - 2*c04*c12*c13*c23) / 32 : ℂ) * st4
    rcases mul_eq_zero.mp hx with y | y
    · exact y
    · exact absurd y hb
  · have hx : c01 * c04 * c14 * c23 * c23 * b0 = 0 := by
      linear_combination (((8*c01*c02*c34 + 8*c01*c03*c24 + 14*c01*c04*c23 + 8*c02*c03*c14 - 2*c02*c04*c13 - 2*c03*c04*c12) * b0) / 32 : ℂ) * haf0
        + (((-6*c01*c12*c34 - 6*c01*c13*c24 - 2*c02*c13*c14 - 2*c03*c12*c14 + 8*c04*c12*c13) * b0) / 32 : ℂ) * haf1
        + (((-2*c01*c23*c24 - 4*c02*c12*c34 - 6*c02*c14*c23 - 6*c04*c12*c23) * b0) / 32 : ℂ) * haf2
        + (((-4*c03*c13*c24 - 4*c03*c14*c23 - 4*c04*c13*c23) * b0) / 32 : ℂ) * haf3
        + (((16*c04*c14*c23) * b0) / 32 : ℂ) * haf4
        - ((c12^2*c34^2 - 2*c12*c13*c24*c34 - 2*c12*c14*c23*c34 + c13^2*c24^2 - 2*c13*c14*c23*c24 + c14^2*c23^2) / 32 : ℂ) * st0
        - ((-2*c01*c23*c24*c34 - c02*c12*c34^2 + c02*c13*c24*c34 + c02*c14*c23*c34 + c03*c12*c24*c34 - c03*c13*c24^2 + c03*c14*c23*c24 + c04*c12*c23*c34 + c04*c13*c23*c24 - c04*c14*c23^2) / 32 : ℂ) * st1
        - ((-c01*c12*c34^2 + c01*c13*c24*c34 + c01*c14*c23*c34 - 2*c02*c13*c14*c34 + c03*c12*c14*c34 + c03*c13*c14*c24 - c03*c14^2*c23 + c04*c12*c13*c34 - c04*c13^2*c24 + c04*c13*c14*c23) / 32 : ℂ) * st2
        - ((c01*c12*c24*c34 - c01*c13*c24^2 + c01*c14*c23*c24 + c02*c12*c14*c34 + c02*c13*c14*c24 - c02*c14^2*c23 - 2*c03*c12*c14*c24 - c04*c12^2*c34 + c04*c12*c13*c24 + c04*c12*c14*c23) / 32 : ℂ) * st3
        - ((c01*c12*c23*c34 + c01*c13*c23*c24 - c01*c14*c23^2 + c02*c12*c13*c34 - c02*c13^2*c24 + c02*c13*c14*c23 - c03*c12^2*c34 + c03*c12*c13*c24 + c03*c12*c14*c23 - 2*c04*c12*c13*c23) / 32 : ℂ) * st4
    rcases mul_eq_zero.mp hx with y | y
    · exact y
    · exact absurd y hb
  · have hx : c01 * c03 * c13 * c24 * c24 * b0 = 0 := by
      linear_combination (((-8*c01*c02*c34 + 8*c01*c03*c24 - 2*c01*c04*c23 - 8*c02*c03*c14 - 2*c02*c04*c13 - 2*c03*c04*c12) * b0) / 32 : ℂ) * haf0
        + (((-6*c01*c12*c34 + 10*c01*c13*c24 - 2*c02*c13*c14 - 2*c03*c12*c14 - 8*c04*c12*c13) * b0) / 32 : ℂ) * haf1
        + (((-2*c01*c23*c24 + 12*c02*c12*c34 + 10*c02*c14*c23 + 10*c04*c12*c23) * b0) / 32 : ℂ) * haf2
        + (((12*c03*c13*c24 - 4*c03*c14*c23 - 4*c04*c13*c23) * b0) / 32 : ℂ) * haf3
        - ((c12^2*c34^2 - 2*c12*c13*c24*c34 - 2*c12*c14*c23*c34 + c13^2*c24^2 - 2*c13*c14*c23*c24 + c14^2*c23^2) / 32 : ℂ) * st0
        - ((-2*c01*c23*c24*c34 - c02*c12*c34^2 + c02*c13*c24*c34 + c02*c14*c23*c34 + c03*c12*c24*c34 - c03*c13*c24^2 + c03*c14*c23*c24 + c04*c12*c23*c34 + c04*c13*c23*c24 - c04*c14*c23^2) / 32 : ℂ) * st1
        - ((-c01*c12*c34^2 + c01*c13*c24*c34 + c01*c14*c23*c34 - 2*c02*c13*c14*c34 + c03*c12*c14*c34 + c03*c13*c14*c24 - c03*c14^2*c23 + c04*c12*c13*c34 - c04*c13^2*c24 + c04*c13*c14*c23) / 32 : ℂ) * st2
        - ((c01*c12*c24*c34 - c01*c13*c24^2 + c01*c14*c23*c24 + c02*c12*c14*c34 + c02*c13*c14*c24 - c02*c14^2*c23 - 2*c03*c12*c14*c24 - c04*c12^2*c34 + c04*c12*c13*c24 + c04*c12*c14*c23) / 32 : ℂ) * st3
        - ((c01*c12*c23*c34 + c01*c13*c23*c24 - c01*c14*c23^2 + c02*c12*c13*c34 - c02*c13^2*c24 + c02*c13*c14*c23 - c03*c12^2*c34 + c03*c12*c13*c24 + c03*c12*c14*c23 - 2*c04*c12*c13*c23) / 32 : ℂ) * st4
    rcases mul_eq_zero.mp hx with y | y
    · exact y
    · exact absurd y hb
  · have hx : c01 * c02 * c12 * c34 * c34 * b0 = 0 := by
      linear_combination (((8*c01*c02*c34 - 8*c01*c03*c24 - 2*c01*c04*c23 - 8*c02*c03*c14 - 2*c02*c04*c13 - 2*c03*c04*c12) * b0) / 32 : ℂ) * haf0
        + (((10*c01*c12*c34 - 6*c01*c13*c24 - 2*c02*c13*c14 - 2*c03*c12*c14 - 8*c04*c12*c13) * b0) / 32 : ℂ) * haf1
        + (((-2*c01*c23*c24 + 12*c02*c12*c34 - 6*c02*c14*c23 - 6*c04*c12*c23) * b0) / 32 : ℂ) * haf2
        + (((12*c03*c13*c24 + 12*c03*c14*c23 + 12*c04*c13*c23) * b0) / 32 : ℂ) * haf3
        - ((c12^2*c34^2 - 2*c12*c13*c24*c34 - 2*c12*c14*c23*c34 + c13^2*c24^2 - 2*c13*c14*c23*c24 + c14^2*c23^2) / 32 : ℂ) * st0
        - ((-2*c01*c23*c24*c34 - c02*c12*c34^2 + c02*c13*c24*c34 + c02*c14*c23*c34 + c03*c12*c24*c34 - c03*c13*c24^2 + c03*c14*c23*c24 + c04*c12*c23*c34 + c04*c13*c23*c24 - c04*c14*c23^2) / 32 : ℂ) * st1
        - ((-c01*c12*c34^2 + c01*c13*c24*c34 + c01*c14*c23*c34 - 2*c02*c13*c14*c34 + c03*c12*c14*c34 + c03*c13*c14*c24 - c03*c14^2*c23 + c04*c12*c13*c34 - c04*c13^2*c24 + c04*c13*c14*c23) / 32 : ℂ) * st2
        - ((c01*c12*c24*c34 - c01*c13*c24^2 + c01*c14*c23*c24 + c02*c12*c14*c34 + c02*c13*c14*c24 - c02*c14^2*c23 - 2*c03*c12*c14*c24 - c04*c12^2*c34 + c04*c12*c13*c24 + c04*c12*c14*c23) / 32 : ℂ) * st3
        - ((c01*c12*c23*c34 + c01*c13*c23*c24 - c01*c14*c23^2 + c02*c12*c13*c34 - c02*c13^2*c24 + c02*c13*c14*c23 - c03*c12^2*c34 + c03*c12*c13*c24 + c03*c12*c14*c23 - 2*c04*c12*c13*c23) / 32 : ℂ) * st4
    rcases mul_eq_zero.mp hx with y | y
    · exact y
    · exact absurd y hb

/-- The determinant identity, in the ten shapes obtained by relabelling
the vertices, cancelled against the nonzero point amplitude `b1`. -/
theorem dets1 {b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 : ℂ}
    (st0 : b1 * c01 + b2 * c02 + b3 * c03 + b4 * c04 = 0)
    (st1 : b0 * c01 + b2 * c12 + b3 * c13 + b4 * c14 = 0)
    (st2 : b0 * c02 + b1 * c12 + b3 * c23 + b4 * c24 = 0)
    (st3 : b0 * c03 + b1 * c13 + b2 * c23 + b4 * c34 = 0)
    (st4 : b0 * c04 + b1 * c14 + b2 * c24 + b3 * c34 = 0)
    (haf0 : c12 * c34 + c13 * c24 + c14 * c23 = 0)
    (haf1 : c02 * c34 + c03 * c24 + c04 * c23 = 0)
    (haf2 : c01 * c34 + c03 * c14 + c04 * c13 = 0)
    (haf3 : c01 * c24 + c02 * c14 + c04 * c12 = 0)
    (haf4 : c01 * c23 + c02 * c13 + c03 * c12 = 0)
    (hb : b1 ≠ 0) :
    c23 * c24 * c34 * c01 * c01 = 0
      ∧ c13 * c14 * c34 * c02 * c02 = 0
      ∧ c12 * c14 * c24 * c03 * c03 = 0
      ∧ c12 * c13 * c23 * c04 * c04 = 0
      ∧ c03 * c04 * c34 * c12 * c12 = 0
      ∧ c02 * c04 * c24 * c13 * c13 = 0
      ∧ c02 * c03 * c23 * c14 * c14 = 0
      ∧ c01 * c04 * c14 * c23 * c23 = 0
      ∧ c01 * c03 * c13 * c24 * c24 = 0
      ∧ c01 * c02 * c12 * c34 * c34 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hx : c23 * c24 * c34 * c01 * c01 * b1 = 0 := by
      linear_combination (((-8*c01*c02*c34 - 8*c01*c03*c24 - 18*c01*c04*c23 + 8*c02*c03*c14 - 2*c02*c04*c13 - 2*c03*c04*c12) * b1) / 32 : ℂ) * haf0
        + (((10*c01*c12*c34 + 10*c01*c13*c24 - 2*c02*c13*c14 - 2*c03*c12*c14 + 8*c04*c12*c13) * b1) / 32 : ℂ) * haf1
        + (((30*c01*c23*c24 - 4*c02*c12*c34 + 10*c02*c14*c23 + 10*c04*c12*c23) * b1) / 32 : ℂ) * haf2
        + (((-4*c03*c13*c24 - 20*c03*c14*c23 - 20*c04*c13*c23) * b1) / 32 : ℂ) * haf3
        + (((16*c04*c14*c23) * b1) / 32 : ℂ) * haf4
        - ((-2*c01*c23*c24*c34 - c02*c12*c34^2 + c02*c13*c24*c34 + c02*c14*c23*c34 + c03*c12*c24*c34 - c03*c13*c24^2 + c03*c14*c23*c24 + c04*c12*c23*c34 + c04*c13*c23*c24 - c04*c14*c23^2) / 32 : ℂ) * st0
        - ((c02^2*c34^2 - 2*c02*c03*c24*c34 - 2*c02*c04*c23*c34 + c03^2*c24^2 - 2*c03*c04*c23*c24 + c04^2*c23^2) / 32 : ℂ) * st1
        - ((-c01*c02*c34^2 + c01*c03*c24*c34 + c01*c04*c23*c34 + c02*c03*c14*c34 + c02*c04*c13*c34 - c03^2*c14*c24 - 2*c03*c04*c12*c34 + c03*c04*c13*c24 + c03*c04*c14*c23 - c04^2*c13*c23) / 32 : ℂ) * st2
        - ((c01*c02*c24*c34 - c01*c03*c24^2 + c01*c04*c23*c24 - c02^2*c14*c34 + c02*c03*c14*c24 + c02*c04*c12*c34 - 2*c02*c04*c13*c24 + c02*c04*c14*c23 + c03*c04*c12*c24 - c04^2*c12*c23) / 32 : ℂ) * st3
        - ((c01*c02*c23*c34 + c01*c03*c23*c24 - c01*c04*c23^2 - c02^2*c13*c34 + c02*c03*c12*c34 + c02*c03*c13*c24 - 2*c02*c03*c14*c23 + c02*c04*c13*c23 - c03^2*c12*c24 + c03*c04*c12*c23) / 32 : ℂ) * st4
    rcases mul_eq_zero.mp hx with y | y
    · exact y
    · exact absurd y hb
  · have hx : c13 * c14 * c34 * c02 * c02 * b1 = 0 := by
      linear_combination (((-8*c01*c02*c34 + 8*c01*c03*c24 - 2*c01*c04*c23 - 8*c02*c03*c14 - 18*c02*c04*c13 - 2*c03*c04*c12) * b1) / 32 : ℂ) * haf0
        + (((-6*c01*c12*c34 + 10*c01*c13*c24 + 30*c02*c13*c14 - 2*c03*c12*c14 + 8*c04*c12*c13) * b1) / 32 : ℂ) * haf1
        + (((-2*c01*c23*c24 + 12*c02*c12*c34 + 10*c02*c14*c23 + 10*c04*c12*c23) * b1) / 32 : ℂ) * haf2
        + (((-20*c03*c13*c24 - 4*c03*c14*c23 - 20*c04*c13*c23) * b1) / 32 : ℂ) * haf3
        + (((16*c04*c13*c24) * b1) / 32 : ℂ) * haf4
        - ((-2*c01*c23*c24*c34 - c02*c12*c34^2 + c02*c13*c24*c34 + c02*c14*c23*c34 + c03*c12*c24*c34 - c03*c13*c24^2 + c03*c14*c23*c24 + c04*c12*c23*c34 + c04*c13*c23*c24 - c04*c14*c23^2) / 32 : ℂ) * st0
        - ((c02^2*c34^2 - 2*c02*c03*c24*c34 - 2*c02*c04*c23*c34 + c03^2*c24^2 - 2*c03*c04*c23*c24 + c04^2*c23^2) / 32 : ℂ) * st1
        - ((-c01*c02*c34^2 + c01*c03*c24*c34 + c01*c04*c23*c34 + c02*c03*c14*c34 + c02*c04*c13*c34 - c03^2*c14*c24 - 2*c03*c04*c12*c34 + c03*c04*c13*c24 + c03*c04*c14*c23 - c04^2*c13*c23) / 32 : ℂ) * st2
        - ((c01*c02*c24*c34 - c01*c03*c24^2 + c01*c04*c23*c24 - c02^2*c14*c34 + c02*c03*c14*c24 + c02*c04*c12*c34 - 2*c02*c04*c13*c24 + c02*c04*c14*c23 + c03*c04*c12*c24 - c04^2*c12*c23) / 32 : ℂ) * st3
        - ((c01*c02*c23*c34 + c01*c03*c23*c24 - c01*c04*c23^2 - c02^2*c13*c34 + c02*c03*c12*c34 + c02*c03*c13*c24 - 2*c02*c03*c14*c23 + c02*c04*c13*c23 - c03^2*c12*c24 + c03*c04*c12*c23) / 32 : ℂ) * st4
    rcases mul_eq_zero.mp hx with y | y
    · exact y
    · exact absurd y hb
  · have hx : c12 * c14 * c24 * c03 * c03 * b1 = 0 := by
      linear_combination (((8*c01*c02*c34 - 8*c01*c03*c24 + 14*c01*c04*c23 - 8*c02*c03*c14 + 14*c02*c04*c13 - 2*c03*c04*c12) * b1) / 32 : ℂ) * haf0
        + (((10*c01*c12*c34 - 6*c01*c13*c24 - 2*c02*c13*c14 + 30*c03*c12*c14 + 8*c04*c12*c13) * b1) / 32 : ℂ) * haf1
        + (((-2*c01*c23*c24 - 20*c02*c12*c34 - 6*c02*c14*c23 - 22*c04*c12*c23) * b1) / 32 : ℂ) * haf2
        + (((12*c03*c13*c24 + 12*c03*c14*c23 + 12*c04*c13*c23) * b1) / 32 : ℂ) * haf3
        + (((-16*c04*c13*c24 - 16*c04*c14*c23) * b1) / 32 : ℂ) * haf4
        - ((-2*c01*c23*c24*c34 - c02*c12*c34^2 + c02*c13*c24*c34 + c02*c14*c23*c34 + c03*c12*c24*c34 - c03*c13*c24^2 + c03*c14*c23*c24 + c04*c12*c23*c34 + c04*c13*c23*c24 - c04*c14*c23^2) / 32 : ℂ) * st0
        - ((c02^2*c34^2 - 2*c02*c03*c24*c34 - 2*c02*c04*c23*c34 + c03^2*c24^2 - 2*c03*c04*c23*c24 + c04^2*c23^2) / 32 : ℂ) * st1
        - ((-c01*c02*c34^2 + c01*c03*c24*c34 + c01*c04*c23*c34 + c02*c03*c14*c34 + c02*c04*c13*c34 - c03^2*c14*c24 - 2*c03*c04*c12*c34 + c03*c04*c13*c24 + c03*c04*c14*c23 - c04^2*c13*c23) / 32 : ℂ) * st2
        - ((c01*c02*c24*c34 - c01*c03*c24^2 + c01*c04*c23*c24 - c02^2*c14*c34 + c02*c03*c14*c24 + c02*c04*c12*c34 - 2*c02*c04*c13*c24 + c02*c04*c14*c23 + c03*c04*c12*c24 - c04^2*c12*c23) / 32 : ℂ) * st3
        - ((c01*c02*c23*c34 + c01*c03*c23*c24 - c01*c04*c23^2 - c02^2*c13*c34 + c02*c03*c12*c34 + c02*c03*c13*c24 - 2*c02*c03*c14*c23 + c02*c04*c13*c23 - c03^2*c12*c24 + c03*c04*c12*c23) / 32 : ℂ) * st4
    rcases mul_eq_zero.mp hx with y | y
    · exact y
    · exact absurd y hb
  · have hx : c12 * c13 * c23 * c04 * c04 * b1 = 0 := by
      linear_combination (((8*c01*c02*c34 + 8*c01*c03*c24 - 2*c01*c04*c23 + 8*c02*c03*c14 - 2*c02*c04*c13 - 2*c03*c04*c12) * b1) / 32 : ℂ) * haf0
        + (((-6*c01*c12*c34 - 6*c01*c13*c24 - 2*c02*c13*c14 - 2*c03*c12*c14 + 8*c04*c12*c13) * b1) / 32 : ℂ) * haf1
        + (((-2*c01*c23*c24 - 4*c02*c12*c34 - 6*c02*c14*c23 + 10*c04*c12*c23) * b1) / 32 : ℂ) * haf2
        + (((-4*c03*c13*c24 - 4*c03*c14*c23 + 12*c04*c13*c23) * b1) / 32 : ℂ) * haf3
        - ((-2*c01*c23*c24*c34 - c02*c12*c34^2 + c02*c13*c24*c34 + c02*c14*c23*c34 + c03*c12*c24*c34 - c03*c13*c24^2 + c03*c14*c23*c24 + c04*c12*c23*c34 + c04*c13*c23*c24 - c04*c14*c23^2) / 32 : ℂ) * st0
        - ((c02^2*c34^2 - 2*c02*c03*c24*c34 - 2*c02*c04*c23*c34 + c03^2*c24^2 - 2*c03*c04*c23*c24 + c04^2*c23^2) / 32 : ℂ) * st1
        - ((-c01*c02*c34^2 + c01*c03*c24*c34 + c01*c04*c23*c34 + c02*c03*c14*c34 + c02*c04*c13*c34 - c03^2*c14*c24 - 2*c03*c04*c12*c34 + c03*c04*c13*c24 + c03*c04*c14*c23 - c04^2*c13*c23) / 32 : ℂ) * st2
        - ((c01*c02*c24*c34 - c01*c03*c24^2 + c01*c04*c23*c24 - c02^2*c14*c34 + c02*c03*c14*c24 + c02*c04*c12*c34 - 2*c02*c04*c13*c24 + c02*c04*c14*c23 + c03*c04*c12*c24 - c04^2*c12*c23) / 32 : ℂ) * st3
        - ((c01*c02*c23*c34 + c01*c03*c23*c24 - c01*c04*c23^2 - c02^2*c13*c34 + c02*c03*c12*c34 + c02*c03*c13*c24 - 2*c02*c03*c14*c23 + c02*c04*c13*c23 - c03^2*c12*c24 + c03*c04*c12*c23) / 32 : ℂ) * st4
    rcases mul_eq_zero.mp hx with y | y
    · exact y
    · exact absurd y hb
  · have hx : c03 * c04 * c34 * c12 * c12 * b1 = 0 := by
      linear_combination (((8*c01*c02*c34 + 8*c01*c03*c24 + 14*c01*c04*c23 + 8*c02*c03*c14 + 14*c02*c04*c13 + 30*c03*c04*c12) * b1) / 32 : ℂ) * haf0
        + (((-6*c01*c12*c34 - 6*c01*c13*c24 - 2*c02*c13*c14 - 2*c03*c12*c14 - 8*c04*c12*c13) * b1) / 32 : ℂ) * haf1
        + (((-2*c01*c23*c24 - 4*c02*c12*c34 - 6*c02*c14*c23 - 6*c04*c12*c23) * b1) / 32 : ℂ) * haf2
        + (((-4*c03*c13*c24 - 4*c03*c14*c23 + 12*c04*c13*c23) * b1) / 32 : ℂ) * haf3
        + (((-16*c04*c13*c24 - 16*c04*c14*c23) * b1) / 32 : ℂ) * haf4
        - ((-2*c01*c23*c24*c34 - c02*c12*c34^2 + c02*c13*c24*c34 + c02*c14*c23*c34 + c03*c12*c24*c34 - c03*c13*c24^2 + c03*c14*c23*c24 + c04*c12*c23*c34 + c04*c13*c23*c24 - c04*c14*c23^2) / 32 : ℂ) * st0
        - ((c02^2*c34^2 - 2*c02*c03*c24*c34 - 2*c02*c04*c23*c34 + c03^2*c24^2 - 2*c03*c04*c23*c24 + c04^2*c23^2) / 32 : ℂ) * st1
        - ((-c01*c02*c34^2 + c01*c03*c24*c34 + c01*c04*c23*c34 + c02*c03*c14*c34 + c02*c04*c13*c34 - c03^2*c14*c24 - 2*c03*c04*c12*c34 + c03*c04*c13*c24 + c03*c04*c14*c23 - c04^2*c13*c23) / 32 : ℂ) * st2
        - ((c01*c02*c24*c34 - c01*c03*c24^2 + c01*c04*c23*c24 - c02^2*c14*c34 + c02*c03*c14*c24 + c02*c04*c12*c34 - 2*c02*c04*c13*c24 + c02*c04*c14*c23 + c03*c04*c12*c24 - c04^2*c12*c23) / 32 : ℂ) * st3
        - ((c01*c02*c23*c34 + c01*c03*c23*c24 - c01*c04*c23^2 - c02^2*c13*c34 + c02*c03*c12*c34 + c02*c03*c13*c24 - 2*c02*c03*c14*c23 + c02*c04*c13*c23 - c03^2*c12*c24 + c03*c04*c12*c23) / 32 : ℂ) * st4
    rcases mul_eq_zero.mp hx with y | y
    · exact y
    · exact absurd y hb
  · have hx : c02 * c04 * c24 * c13 * c13 * b1 = 0 := by
      linear_combination (((8*c01*c02*c34 + 8*c01*c03*c24 - 2*c01*c04*c23 + 8*c02*c03*c14 + 14*c02*c04*c13 - 2*c03*c04*c12) * b1) / 32 : ℂ) * haf0
        + (((-6*c01*c12*c34 - 6*c01*c13*c24 - 2*c02*c13*c14 - 2*c03*c12*c14 - 8*c04*c12*c13) * b1) / 32 : ℂ) * haf1
        + (((-2*c01*c23*c24 - 4*c02*c12*c34 - 6*c02*c14*c23 + 10*c04*c12*c23) * b1) / 32 : ℂ) * haf2
        + (((-4*c03*c13*c24 - 4*c03*c14*c23 - 4*c04*c13*c23) * b1) / 32 : ℂ) * haf3
        + (((16*c04*c13*c24) * b1) / 32 : ℂ) * haf4
        - ((-2*c01*c23*c24*c34 - c02*c12*c34^2 + c02*c13*c24*c34 + c02*c14*c23*c34 + c03*c12*c24*c34 - c03*c13*c24^2 + c03*c14*c23*c24 + c04*c12*c23*c34 + c04*c13*c23*c24 - c04*c14*c23^2) / 32 : ℂ) * st0
        - ((c02^2*c34^2 - 2*c02*c03*c24*c34 - 2*c02*c04*c23*c34 + c03^2*c24^2 - 2*c03*c04*c23*c24 + c04^2*c23^2) / 32 : ℂ) * st1
        - ((-c01*c02*c34^2 + c01*c03*c24*c34 + c01*c04*c23*c34 + c02*c03*c14*c34 + c02*c04*c13*c34 - c03^2*c14*c24 - 2*c03*c04*c12*c34 + c03*c04*c13*c24 + c03*c04*c14*c23 - c04^2*c13*c23) / 32 : ℂ) * st2
        - ((c01*c02*c24*c34 - c01*c03*c24^2 + c01*c04*c23*c24 - c02^2*c14*c34 + c02*c03*c14*c24 + c02*c04*c12*c34 - 2*c02*c04*c13*c24 + c02*c04*c14*c23 + c03*c04*c12*c24 - c04^2*c12*c23) / 32 : ℂ) * st3
        - ((c01*c02*c23*c34 + c01*c03*c23*c24 - c01*c04*c23^2 - c02^2*c13*c34 + c02*c03*c12*c34 + c02*c03*c13*c24 - 2*c02*c03*c14*c23 + c02*c04*c13*c23 - c03^2*c12*c24 + c03*c04*c12*c23) / 32 : ℂ) * st4
    rcases mul_eq_zero.mp hx with y | y
    · exact y
    · exact absurd y hb
  · have hx : c02 * c03 * c23 * c14 * c14 * b1 = 0 := by
      linear_combination (((-8*c01*c02*c34 - 8*c01*c03*c24 - 2*c01*c04*c23 + 8*c02*c03*c14 - 2*c02*c04*c13 - 2*c03*c04*c12) * b1) / 32 : ℂ) * haf0
        + (((10*c01*c12*c34 + 10*c01*c13*c24 - 2*c02*c13*c14 - 2*c03*c12*c14 + 8*c04*c12*c13) * b1) / 32 : ℂ) * haf1
        + (((-2*c01*c23*c24 - 4*c02*c12*c34 + 10*c02*c14*c23 - 6*c04*c12*c23) * b1) / 32 : ℂ) * haf2
        + (((-4*c03*c13*c24 + 12*c03*c14*c23 - 4*c04*c13*c23) * b1) / 32 : ℂ) * haf3
        - ((-2*c01*c23*c24*c34 - c02*c12*c34^2 + c02*c13*c24*c34 + c02*c14*c23*c34 + c03*c12*c24*c34 - c03*c13*c24^2 + c03*c14*c23*c24 + c04*c12*c23*c34 + c04*c13*c23*c24 - c04*c14*c23^2) / 32 : ℂ) * st0
        - ((c02^2*c34^2 - 2*c02*c03*c24*c34 - 2*c02*c04*c23*c34 + c03^2*c24^2 - 2*c03*c04*c23*c24 + c04^2*c23^2) / 32 : ℂ) * st1
        - ((-c01*c02*c34^2 + c01*c03*c24*c34 + c01*c04*c23*c34 + c02*c03*c14*c34 + c02*c04*c13*c34 - c03^2*c14*c24 - 2*c03*c04*c12*c34 + c03*c04*c13*c24 + c03*c04*c14*c23 - c04^2*c13*c23) / 32 : ℂ) * st2
        - ((c01*c02*c24*c34 - c01*c03*c24^2 + c01*c04*c23*c24 - c02^2*c14*c34 + c02*c03*c14*c24 + c02*c04*c12*c34 - 2*c02*c04*c13*c24 + c02*c04*c14*c23 + c03*c04*c12*c24 - c04^2*c12*c23) / 32 : ℂ) * st3
        - ((c01*c02*c23*c34 + c01*c03*c23*c24 - c01*c04*c23^2 - c02^2*c13*c34 + c02*c03*c12*c34 + c02*c03*c13*c24 - 2*c02*c03*c14*c23 + c02*c04*c13*c23 - c03^2*c12*c24 + c03*c04*c12*c23) / 32 : ℂ) * st4
    rcases mul_eq_zero.mp hx with y | y
    · exact y
    · exact absurd y hb
  · have hx : c01 * c04 * c14 * c23 * c23 * b1 = 0 := by
      linear_combination (((8*c01*c02*c34 + 8*c01*c03*c24 + 14*c01*c04*c23 + 8*c02*c03*c14 - 2*c02*c04*c13 - 2*c03*c04*c12) * b1) / 32 : ℂ) * haf0
        + (((-6*c01*c12*c34 - 6*c01*c13*c24 - 2*c02*c13*c14 - 2*c03*c12*c14 + 8*c04*c12*c13) * b1) / 32 : ℂ) * haf1
        + (((-2*c01*c23*c24 - 4*c02*c12*c34 - 6*c02*c14*c23 - 6*c04*c12*c23) * b1) / 32 : ℂ) * haf2
        + (((-4*c03*c13*c24 - 4*c03*c14*c23 - 4*c04*c13*c23) * b1) / 32 : ℂ) * haf3
        + (((16*c04*c14*c23) * b1) / 32 : ℂ) * haf4
        - ((-2*c01*c23*c24*c34 - c02*c12*c34^2 + c02*c13*c24*c34 + c02*c14*c23*c34 + c03*c12*c24*c34 - c03*c13*c24^2 + c03*c14*c23*c24 + c04*c12*c23*c34 + c04*c13*c23*c24 - c04*c14*c23^2) / 32 : ℂ) * st0
        - ((c02^2*c34^2 - 2*c02*c03*c24*c34 - 2*c02*c04*c23*c34 + c03^2*c24^2 - 2*c03*c04*c23*c24 + c04^2*c23^2) / 32 : ℂ) * st1
        - ((-c01*c02*c34^2 + c01*c03*c24*c34 + c01*c04*c23*c34 + c02*c03*c14*c34 + c02*c04*c13*c34 - c03^2*c14*c24 - 2*c03*c04*c12*c34 + c03*c04*c13*c24 + c03*c04*c14*c23 - c04^2*c13*c23) / 32 : ℂ) * st2
        - ((c01*c02*c24*c34 - c01*c03*c24^2 + c01*c04*c23*c24 - c02^2*c14*c34 + c02*c03*c14*c24 + c02*c04*c12*c34 - 2*c02*c04*c13*c24 + c02*c04*c14*c23 + c03*c04*c12*c24 - c04^2*c12*c23) / 32 : ℂ) * st3
        - ((c01*c02*c23*c34 + c01*c03*c23*c24 - c01*c04*c23^2 - c02^2*c13*c34 + c02*c03*c12*c34 + c02*c03*c13*c24 - 2*c02*c03*c14*c23 + c02*c04*c13*c23 - c03^2*c12*c24 + c03*c04*c12*c23) / 32 : ℂ) * st4
    rcases mul_eq_zero.mp hx with y | y
    · exact y
    · exact absurd y hb
  · have hx : c01 * c03 * c13 * c24 * c24 * b1 = 0 := by
      linear_combination (((-8*c01*c02*c34 + 8*c01*c03*c24 - 2*c01*c04*c23 - 8*c02*c03*c14 - 2*c02*c04*c13 - 2*c03*c04*c12) * b1) / 32 : ℂ) * haf0
        + (((-6*c01*c12*c34 + 10*c01*c13*c24 - 2*c02*c13*c14 - 2*c03*c12*c14 - 8*c04*c12*c13) * b1) / 32 : ℂ) * haf1
        + (((-2*c01*c23*c24 + 12*c02*c12*c34 + 10*c02*c14*c23 + 10*c04*c12*c23) * b1) / 32 : ℂ) * haf2
        + (((12*c03*c13*c24 - 4*c03*c14*c23 - 4*c04*c13*c23) * b1) / 32 : ℂ) * haf3
        - ((-2*c01*c23*c24*c34 - c02*c12*c34^2 + c02*c13*c24*c34 + c02*c14*c23*c34 + c03*c12*c24*c34 - c03*c13*c24^2 + c03*c14*c23*c24 + c04*c12*c23*c34 + c04*c13*c23*c24 - c04*c14*c23^2) / 32 : ℂ) * st0
        - ((c02^2*c34^2 - 2*c02*c03*c24*c34 - 2*c02*c04*c23*c34 + c03^2*c24^2 - 2*c03*c04*c23*c24 + c04^2*c23^2) / 32 : ℂ) * st1
        - ((-c01*c02*c34^2 + c01*c03*c24*c34 + c01*c04*c23*c34 + c02*c03*c14*c34 + c02*c04*c13*c34 - c03^2*c14*c24 - 2*c03*c04*c12*c34 + c03*c04*c13*c24 + c03*c04*c14*c23 - c04^2*c13*c23) / 32 : ℂ) * st2
        - ((c01*c02*c24*c34 - c01*c03*c24^2 + c01*c04*c23*c24 - c02^2*c14*c34 + c02*c03*c14*c24 + c02*c04*c12*c34 - 2*c02*c04*c13*c24 + c02*c04*c14*c23 + c03*c04*c12*c24 - c04^2*c12*c23) / 32 : ℂ) * st3
        - ((c01*c02*c23*c34 + c01*c03*c23*c24 - c01*c04*c23^2 - c02^2*c13*c34 + c02*c03*c12*c34 + c02*c03*c13*c24 - 2*c02*c03*c14*c23 + c02*c04*c13*c23 - c03^2*c12*c24 + c03*c04*c12*c23) / 32 : ℂ) * st4
    rcases mul_eq_zero.mp hx with y | y
    · exact y
    · exact absurd y hb
  · have hx : c01 * c02 * c12 * c34 * c34 * b1 = 0 := by
      linear_combination (((8*c01*c02*c34 - 8*c01*c03*c24 - 2*c01*c04*c23 - 8*c02*c03*c14 - 2*c02*c04*c13 - 2*c03*c04*c12) * b1) / 32 : ℂ) * haf0
        + (((10*c01*c12*c34 - 6*c01*c13*c24 - 2*c02*c13*c14 - 2*c03*c12*c14 - 8*c04*c12*c13) * b1) / 32 : ℂ) * haf1
        + (((-2*c01*c23*c24 + 12*c02*c12*c34 - 6*c02*c14*c23 - 6*c04*c12*c23) * b1) / 32 : ℂ) * haf2
        + (((12*c03*c13*c24 + 12*c03*c14*c23 + 12*c04*c13*c23) * b1) / 32 : ℂ) * haf3
        - ((-2*c01*c23*c24*c34 - c02*c12*c34^2 + c02*c13*c24*c34 + c02*c14*c23*c34 + c03*c12*c24*c34 - c03*c13*c24^2 + c03*c14*c23*c24 + c04*c12*c23*c34 + c04*c13*c23*c24 - c04*c14*c23^2) / 32 : ℂ) * st0
        - ((c02^2*c34^2 - 2*c02*c03*c24*c34 - 2*c02*c04*c23*c34 + c03^2*c24^2 - 2*c03*c04*c23*c24 + c04^2*c23^2) / 32 : ℂ) * st1
        - ((-c01*c02*c34^2 + c01*c03*c24*c34 + c01*c04*c23*c34 + c02*c03*c14*c34 + c02*c04*c13*c34 - c03^2*c14*c24 - 2*c03*c04*c12*c34 + c03*c04*c13*c24 + c03*c04*c14*c23 - c04^2*c13*c23) / 32 : ℂ) * st2
        - ((c01*c02*c24*c34 - c01*c03*c24^2 + c01*c04*c23*c24 - c02^2*c14*c34 + c02*c03*c14*c24 + c02*c04*c12*c34 - 2*c02*c04*c13*c24 + c02*c04*c14*c23 + c03*c04*c12*c24 - c04^2*c12*c23) / 32 : ℂ) * st3
        - ((c01*c02*c23*c34 + c01*c03*c23*c24 - c01*c04*c23^2 - c02^2*c13*c34 + c02*c03*c12*c34 + c02*c03*c13*c24 - 2*c02*c03*c14*c23 + c02*c04*c13*c23 - c03^2*c12*c24 + c03*c04*c12*c23) / 32 : ℂ) * st4
    rcases mul_eq_zero.mp hx with y | y
    · exact y
    · exact absurd y hb

/-! ## The hypothesis bundle -/

/-- The reduced Walsh data of orbit 30 on the `K_5` labelling, together
with the exact moment data. -/
structure Sys (s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34 : ℂ) : Prop where
  hs : s ≠ 0
  st0 : b1 * c01 + b2 * c02 + b3 * c03 + b4 * c04 = 0
  st1 : b0 * c01 + b2 * c12 + b3 * c13 + b4 * c14 = 0
  st2 : b0 * c02 + b1 * c12 + b3 * c23 + b4 * c24 = 0
  st3 : b0 * c03 + b1 * c13 + b2 * c23 + b4 * c34 = 0
  st4 : b0 * c04 + b1 * c14 + b2 * c24 + b3 * c34 = 0
  kb01_0 : b0 * k01 = 0
  kb01_1 : b1 * k01 = 0
  kb02_0 : b0 * k02 = 0
  kb02_2 : b2 * k02 = 0
  kb03_0 : b0 * k03 = 0
  kb03_3 : b3 * k03 = 0
  kb04_0 : b0 * k04 = 0
  kb04_4 : b4 * k04 = 0
  kb12_1 : b1 * k12 = 0
  kb12_2 : b2 * k12 = 0
  kb13_1 : b1 * k13 = 0
  kb13_3 : b3 * k13 = 0
  kb14_1 : b1 * k14 = 0
  kb14_4 : b4 * k14 = 0
  kb23_2 : b2 * k23 = 0
  kb23_3 : b3 * k23 = 0
  kb24_2 : b2 * k24 = 0
  kb24_4 : b4 * k24 = 0
  kb34_3 : b3 * k34 = 0
  kb34_4 : b4 * k34 = 0
  hf0 : c12 * k34 + c34 * k12 + c13 * k24 + c24 * k13 + c14 * k23 + c23 * k14
      = 2 * s * (c12 * c34 + c13 * c24 + c14 * c23)
  hf1 : c02 * k34 + c34 * k02 + c03 * k24 + c24 * k03 + c04 * k23 + c23 * k04
      = 2 * s * (c02 * c34 + c03 * c24 + c04 * c23)
  hf2 : c01 * k34 + c34 * k01 + c03 * k14 + c14 * k03 + c04 * k13 + c13 * k04
      = 2 * s * (c01 * c34 + c03 * c14 + c04 * c13)
  hf3 : c01 * k24 + c24 * k01 + c02 * k14 + c14 * k02 + c04 * k12 + c12 * k04
      = 2 * s * (c01 * c24 + c02 * c14 + c04 * c12)
  hf4 : c01 * k23 + c23 * k01 + c02 * k13 + c13 * k02 + c03 * k12 + c12 * k03
      = 2 * s * (c01 * c23 + c02 * c13 + c03 * c12)
  dg0 : Complex.normSq c01 + Complex.normSq c02 + Complex.normSq c03 + Complex.normSq c04 = Complex.normSq b0 + 1/8
  dg1 : Complex.normSq c01 + Complex.normSq c12 + Complex.normSq c13 + Complex.normSq c14 = Complex.normSq b1 + 1/8
  dg2 : Complex.normSq c02 + Complex.normSq c12 + Complex.normSq c23 + Complex.normSq c24 = Complex.normSq b2 + 1/8
  dg3 : Complex.normSq c03 + Complex.normSq c13 + Complex.normSq c23 + Complex.normSq c34 = Complex.normSq b3 + 1/8
  dg4 : Complex.normSq c04 + Complex.normSq c14 + Complex.normSq c24 + Complex.normSq c34 = Complex.normSq b4 + 1/8
  tb : Complex.normSq b0 + Complex.normSq b1 + Complex.normSq b2 + Complex.normSq b3 + Complex.normSq b4 = 3/8
  tc : Complex.normSq c01 + Complex.normSq c02 + Complex.normSq c03 + Complex.normSq c04 + Complex.normSq c12 + Complex.normSq c13 + Complex.normSq c14 + Complex.normSq c23 + Complex.normSq c24 + Complex.normSq c34 = 1/2

/-! ## The no-go -/

/-- The branch in which exactly the point amplitudes none are nonzero. -/
theorem case0 {s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34 : ℂ} (h : Sys s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34)
    (p0 : b0 = 0) (p1 : b1 = 0) (p2 : b2 = 0) (p3 : b3 = 0) (p4 : b4 = 0) : False := by
  have ht := h.tb
  rw [p0, p1, p2, p3, p4, Complex.normSq_zero] at ht
  norm_num at ht

/-- The branch in which exactly the point amplitudes b0 are nonzero. -/
theorem case1 {s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34 : ℂ} (h : Sys s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34)
    (p0 : b0 ≠ 0) (p1 : b1 = 0) (p2 : b2 = 0) (p3 : b3 = 0) (p4 : b4 = 0) : False := by
  have x1 : c01 = 0 := by
    have hx : b0 * c01 = 0 := by linear_combination h.st1 - (c12 : ℂ) * p2 - (c13 : ℂ) * p3 - (c14 : ℂ) * p4
    rcases mul_eq_zero.mp hx with y | y
    · exact absurd y p0
    · exact y
  have x2 : c02 = 0 := by
    have hx : b0 * c02 = 0 := by linear_combination h.st2 - (c12 : ℂ) * p1 - (c23 : ℂ) * p3 - (c24 : ℂ) * p4
    rcases mul_eq_zero.mp hx with y | y
    · exact absurd y p0
    · exact y
  have x3 : c03 = 0 := by
    have hx : b0 * c03 = 0 := by linear_combination h.st3 - (c13 : ℂ) * p1 - (c23 : ℂ) * p2 - (c34 : ℂ) * p4
    rcases mul_eq_zero.mp hx with y | y
    · exact absurd y p0
    · exact y
  have x4 : c04 = 0 := by
    have hx : b0 * c04 = 0 := by linear_combination h.st4 - (c14 : ℂ) * p1 - (c24 : ℂ) * p2 - (c34 : ℂ) * p3
    rcases mul_eq_zero.mp hx with y | y
    · exact absurd y p0
    · exact y
  have hd := h.dg0
  rw [x1, x2, x3, x4, Complex.normSq_zero] at hd
  linarith only [hd, Complex.normSq_nonneg b0]

/-- The branch in which exactly the point amplitudes b1 are nonzero. -/
theorem case2 {s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34 : ℂ} (h : Sys s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34)
    (p0 : b0 = 0) (p1 : b1 ≠ 0) (p2 : b2 = 0) (p3 : b3 = 0) (p4 : b4 = 0) : False := by
  have x0 : c01 = 0 := by
    have hx : b1 * c01 = 0 := by linear_combination h.st0 - (c02 : ℂ) * p2 - (c03 : ℂ) * p3 - (c04 : ℂ) * p4
    rcases mul_eq_zero.mp hx with y | y
    · exact absurd y p1
    · exact y
  have x2 : c12 = 0 := by
    have hx : b1 * c12 = 0 := by linear_combination h.st2 - (c02 : ℂ) * p0 - (c23 : ℂ) * p3 - (c24 : ℂ) * p4
    rcases mul_eq_zero.mp hx with y | y
    · exact absurd y p1
    · exact y
  have x3 : c13 = 0 := by
    have hx : b1 * c13 = 0 := by linear_combination h.st3 - (c03 : ℂ) * p0 - (c23 : ℂ) * p2 - (c34 : ℂ) * p4
    rcases mul_eq_zero.mp hx with y | y
    · exact absurd y p1
    · exact y
  have x4 : c14 = 0 := by
    have hx : b1 * c14 = 0 := by linear_combination h.st4 - (c04 : ℂ) * p0 - (c24 : ℂ) * p2 - (c34 : ℂ) * p3
    rcases mul_eq_zero.mp hx with y | y
    · exact absurd y p1
    · exact y
  have hd := h.dg1
  rw [x0, x2, x3, x4, Complex.normSq_zero] at hd
  linarith only [hd, Complex.normSq_nonneg b1]

/-- The branch in which exactly the point amplitudes b0, b1 are nonzero. -/
theorem case3 {s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34 : ℂ} (h : Sys s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34)
    (_p0 : b0 ≠ 0) (p1 : b1 ≠ 0) (p2 : b2 = 0) (p3 : b3 = 0) (p4 : b4 = 0) : False := by
  have hab : c01 = 0 := by
    have hx : b1 * c01 = 0 := by linear_combination h.st0 - (c02 : ℂ) * p2 - (c03 : ℂ) * p3 - (c04 : ℂ) * p4
    rcases mul_eq_zero.mp hx with y | y
    · exact absurd y p1
    · exact y
  have hd1 := h.dg0
  have hd2 := h.dg1
  have ht := h.tb
  have hc := h.tc
  rw [hab, Complex.normSq_zero] at hd1 hd2 hc
  rw [p2, p3, p4, Complex.normSq_zero] at ht
  linarith only [hd1, hd2, ht, hc, Complex.normSq_nonneg b0, Complex.normSq_nonneg b1, Complex.normSq_nonneg b2, Complex.normSq_nonneg b3, Complex.normSq_nonneg b4, Complex.normSq_nonneg c01, Complex.normSq_nonneg c02, Complex.normSq_nonneg c03, Complex.normSq_nonneg c04, Complex.normSq_nonneg c12, Complex.normSq_nonneg c13, Complex.normSq_nonneg c14, Complex.normSq_nonneg c23, Complex.normSq_nonneg c24, Complex.normSq_nonneg c34]

/-- The branch in which exactly the point amplitudes b2 are nonzero. -/
theorem case4 {s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34 : ℂ} (h : Sys s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34)
    (p0 : b0 = 0) (p1 : b1 = 0) (p2 : b2 ≠ 0) (p3 : b3 = 0) (p4 : b4 = 0) : False := by
  have x0 : c02 = 0 := by
    have hx : b2 * c02 = 0 := by linear_combination h.st0 - (c01 : ℂ) * p1 - (c03 : ℂ) * p3 - (c04 : ℂ) * p4
    rcases mul_eq_zero.mp hx with y | y
    · exact absurd y p2
    · exact y
  have x1 : c12 = 0 := by
    have hx : b2 * c12 = 0 := by linear_combination h.st1 - (c01 : ℂ) * p0 - (c13 : ℂ) * p3 - (c14 : ℂ) * p4
    rcases mul_eq_zero.mp hx with y | y
    · exact absurd y p2
    · exact y
  have x3 : c23 = 0 := by
    have hx : b2 * c23 = 0 := by linear_combination h.st3 - (c03 : ℂ) * p0 - (c13 : ℂ) * p1 - (c34 : ℂ) * p4
    rcases mul_eq_zero.mp hx with y | y
    · exact absurd y p2
    · exact y
  have x4 : c24 = 0 := by
    have hx : b2 * c24 = 0 := by linear_combination h.st4 - (c04 : ℂ) * p0 - (c14 : ℂ) * p1 - (c34 : ℂ) * p3
    rcases mul_eq_zero.mp hx with y | y
    · exact absurd y p2
    · exact y
  have hd := h.dg2
  rw [x0, x1, x3, x4, Complex.normSq_zero] at hd
  linarith only [hd, Complex.normSq_nonneg b2]

/-- The branch in which exactly the point amplitudes b0, b2 are nonzero. -/
theorem case5 {s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34 : ℂ} (h : Sys s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34)
    (_p0 : b0 ≠ 0) (p1 : b1 = 0) (p2 : b2 ≠ 0) (p3 : b3 = 0) (p4 : b4 = 0) : False := by
  have hab : c02 = 0 := by
    have hx : b2 * c02 = 0 := by linear_combination h.st0 - (c01 : ℂ) * p1 - (c03 : ℂ) * p3 - (c04 : ℂ) * p4
    rcases mul_eq_zero.mp hx with y | y
    · exact absurd y p2
    · exact y
  have hd1 := h.dg0
  have hd2 := h.dg2
  have ht := h.tb
  have hc := h.tc
  rw [hab, Complex.normSq_zero] at hd1 hd2 hc
  rw [p1, p3, p4, Complex.normSq_zero] at ht
  linarith only [hd1, hd2, ht, hc, Complex.normSq_nonneg b0, Complex.normSq_nonneg b1, Complex.normSq_nonneg b2, Complex.normSq_nonneg b3, Complex.normSq_nonneg b4, Complex.normSq_nonneg c01, Complex.normSq_nonneg c02, Complex.normSq_nonneg c03, Complex.normSq_nonneg c04, Complex.normSq_nonneg c12, Complex.normSq_nonneg c13, Complex.normSq_nonneg c14, Complex.normSq_nonneg c23, Complex.normSq_nonneg c24, Complex.normSq_nonneg c34]

/-- The branch in which exactly the point amplitudes b1, b2 are nonzero. -/
theorem case6 {s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34 : ℂ} (h : Sys s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34)
    (p0 : b0 = 0) (_p1 : b1 ≠ 0) (p2 : b2 ≠ 0) (p3 : b3 = 0) (p4 : b4 = 0) : False := by
  have hab : c12 = 0 := by
    have hx : b2 * c12 = 0 := by linear_combination h.st1 - (c01 : ℂ) * p0 - (c13 : ℂ) * p3 - (c14 : ℂ) * p4
    rcases mul_eq_zero.mp hx with y | y
    · exact absurd y p2
    · exact y
  have hd1 := h.dg1
  have hd2 := h.dg2
  have ht := h.tb
  have hc := h.tc
  rw [hab, Complex.normSq_zero] at hd1 hd2 hc
  rw [p0, p3, p4, Complex.normSq_zero] at ht
  linarith only [hd1, hd2, ht, hc, Complex.normSq_nonneg b0, Complex.normSq_nonneg b1, Complex.normSq_nonneg b2, Complex.normSq_nonneg b3, Complex.normSq_nonneg b4, Complex.normSq_nonneg c01, Complex.normSq_nonneg c02, Complex.normSq_nonneg c03, Complex.normSq_nonneg c04, Complex.normSq_nonneg c12, Complex.normSq_nonneg c13, Complex.normSq_nonneg c14, Complex.normSq_nonneg c23, Complex.normSq_nonneg c24, Complex.normSq_nonneg c34]

/-- The branch in which exactly the point amplitudes b0, b1, b2 are nonzero. -/
theorem case7 {s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34 : ℂ} (h : Sys s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34)
    (p0 : b0 ≠ 0) (p1 : b1 ≠ 0) (p2 : b2 ≠ 0) (p3 : b3 = 0) (p4 : b4 = 0) : False := by
  have hd1 := h.dg0
  have hd2 := h.dg1
  have hd3 := h.dg2
  have ht := h.tb
  have hc := h.tc
  rw [p3, p4, Complex.normSq_zero] at ht
  have hW : (0:Real) < Complex.normSq c01 + Complex.normSq c02 + Complex.normSq c12 := by
    linarith only [hd1, hd2, hd3, ht, hc, Complex.normSq_nonneg b0, Complex.normSq_nonneg b1, Complex.normSq_nonneg b2, Complex.normSq_nonneg b3, Complex.normSq_nonneg b4, Complex.normSq_nonneg c01, Complex.normSq_nonneg c02, Complex.normSq_nonneg c03, Complex.normSq_nonneg c04, Complex.normSq_nonneg c12, Complex.normSq_nonneg c13, Complex.normSq_nonneg c14, Complex.normSq_nonneg c23, Complex.normSq_nonneg c24, Complex.normSq_nonneg c34]
  have sa : b1 * c01 + b2 * c02 = 0 := by linear_combination h.st0 - (c03 : ℂ) * p3 - (c04 : ℂ) * p4
  have sb : b0 * c01 + b2 * c12 = 0 := by linear_combination h.st1 - (c13 : ℂ) * p3 - (c14 : ℂ) * p4
  have sc : b0 * c02 + b1 * c12 = 0 := by linear_combination h.st2 - (c23 : ℂ) * p3 - (c24 : ℂ) * p4
  have kk := SixQubit.Triangle.prod_eq_zero sc sb sa
  have z1 : c12 = 0 ∨ c02 = 0 := by
    rcases mul_eq_zero.mp kk with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · exact absurd y2 p2
      · exact Or.inl y2
    · exact Or.inr y
  have zz : c01 = 0 ∧ c02 = 0 ∧ c12 = 0 := by
    rcases z1 with y | y
    · have h1 : c01 = 0 := by
        have hx : b0 * c01 = 0 := by linear_combination sb - (b2 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p0
        · exact w
      have h2 : c02 = 0 := by
        have hx : b0 * c02 = 0 := by linear_combination sc - (b1 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p0
        · exact w
      exact ⟨h1, h2, y⟩
    · have h1 : c01 = 0 := by
        have hx : b1 * c01 = 0 := by linear_combination sa - (b2 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p1
        · exact w
      have h2 : c12 = 0 := by
        have hx : b1 * c12 = 0 := by linear_combination sc - (b0 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p1
        · exact w
      exact ⟨h1, y, h2⟩
  obtain ⟨u1, u2, u3⟩ := zz
  rw [u1, u2, u3, Complex.normSq_zero] at hW
  norm_num at hW

/-- The branch in which exactly the point amplitudes b3 are nonzero. -/
theorem case8 {s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34 : ℂ} (h : Sys s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34)
    (p0 : b0 = 0) (p1 : b1 = 0) (p2 : b2 = 0) (p3 : b3 ≠ 0) (p4 : b4 = 0) : False := by
  have x0 : c03 = 0 := by
    have hx : b3 * c03 = 0 := by linear_combination h.st0 - (c01 : ℂ) * p1 - (c02 : ℂ) * p2 - (c04 : ℂ) * p4
    rcases mul_eq_zero.mp hx with y | y
    · exact absurd y p3
    · exact y
  have x1 : c13 = 0 := by
    have hx : b3 * c13 = 0 := by linear_combination h.st1 - (c01 : ℂ) * p0 - (c12 : ℂ) * p2 - (c14 : ℂ) * p4
    rcases mul_eq_zero.mp hx with y | y
    · exact absurd y p3
    · exact y
  have x2 : c23 = 0 := by
    have hx : b3 * c23 = 0 := by linear_combination h.st2 - (c02 : ℂ) * p0 - (c12 : ℂ) * p1 - (c24 : ℂ) * p4
    rcases mul_eq_zero.mp hx with y | y
    · exact absurd y p3
    · exact y
  have x4 : c34 = 0 := by
    have hx : b3 * c34 = 0 := by linear_combination h.st4 - (c04 : ℂ) * p0 - (c14 : ℂ) * p1 - (c24 : ℂ) * p2
    rcases mul_eq_zero.mp hx with y | y
    · exact absurd y p3
    · exact y
  have hd := h.dg3
  rw [x0, x1, x2, x4, Complex.normSq_zero] at hd
  linarith only [hd, Complex.normSq_nonneg b3]

/-- The branch in which exactly the point amplitudes b0, b3 are nonzero. -/
theorem case9 {s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34 : ℂ} (h : Sys s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34)
    (_p0 : b0 ≠ 0) (p1 : b1 = 0) (p2 : b2 = 0) (p3 : b3 ≠ 0) (p4 : b4 = 0) : False := by
  have hab : c03 = 0 := by
    have hx : b3 * c03 = 0 := by linear_combination h.st0 - (c01 : ℂ) * p1 - (c02 : ℂ) * p2 - (c04 : ℂ) * p4
    rcases mul_eq_zero.mp hx with y | y
    · exact absurd y p3
    · exact y
  have hd1 := h.dg0
  have hd2 := h.dg3
  have ht := h.tb
  have hc := h.tc
  rw [hab, Complex.normSq_zero] at hd1 hd2 hc
  rw [p1, p2, p4, Complex.normSq_zero] at ht
  linarith only [hd1, hd2, ht, hc, Complex.normSq_nonneg b0, Complex.normSq_nonneg b1, Complex.normSq_nonneg b2, Complex.normSq_nonneg b3, Complex.normSq_nonneg b4, Complex.normSq_nonneg c01, Complex.normSq_nonneg c02, Complex.normSq_nonneg c03, Complex.normSq_nonneg c04, Complex.normSq_nonneg c12, Complex.normSq_nonneg c13, Complex.normSq_nonneg c14, Complex.normSq_nonneg c23, Complex.normSq_nonneg c24, Complex.normSq_nonneg c34]

/-- The branch in which exactly the point amplitudes b1, b3 are nonzero. -/
theorem case10 {s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34 : ℂ} (h : Sys s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34)
    (p0 : b0 = 0) (_p1 : b1 ≠ 0) (p2 : b2 = 0) (p3 : b3 ≠ 0) (p4 : b4 = 0) : False := by
  have hab : c13 = 0 := by
    have hx : b3 * c13 = 0 := by linear_combination h.st1 - (c01 : ℂ) * p0 - (c12 : ℂ) * p2 - (c14 : ℂ) * p4
    rcases mul_eq_zero.mp hx with y | y
    · exact absurd y p3
    · exact y
  have hd1 := h.dg1
  have hd2 := h.dg3
  have ht := h.tb
  have hc := h.tc
  rw [hab, Complex.normSq_zero] at hd1 hd2 hc
  rw [p0, p2, p4, Complex.normSq_zero] at ht
  linarith only [hd1, hd2, ht, hc, Complex.normSq_nonneg b0, Complex.normSq_nonneg b1, Complex.normSq_nonneg b2, Complex.normSq_nonneg b3, Complex.normSq_nonneg b4, Complex.normSq_nonneg c01, Complex.normSq_nonneg c02, Complex.normSq_nonneg c03, Complex.normSq_nonneg c04, Complex.normSq_nonneg c12, Complex.normSq_nonneg c13, Complex.normSq_nonneg c14, Complex.normSq_nonneg c23, Complex.normSq_nonneg c24, Complex.normSq_nonneg c34]

/-- The branch in which exactly the point amplitudes b0, b1, b3 are nonzero. -/
theorem case11 {s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34 : ℂ} (h : Sys s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34)
    (p0 : b0 ≠ 0) (p1 : b1 ≠ 0) (p2 : b2 = 0) (p3 : b3 ≠ 0) (p4 : b4 = 0) : False := by
  have hd1 := h.dg0
  have hd2 := h.dg1
  have hd3 := h.dg3
  have ht := h.tb
  have hc := h.tc
  rw [p2, p4, Complex.normSq_zero] at ht
  have hW : (0:Real) < Complex.normSq c01 + Complex.normSq c03 + Complex.normSq c13 := by
    linarith only [hd1, hd2, hd3, ht, hc, Complex.normSq_nonneg b0, Complex.normSq_nonneg b1, Complex.normSq_nonneg b2, Complex.normSq_nonneg b3, Complex.normSq_nonneg b4, Complex.normSq_nonneg c01, Complex.normSq_nonneg c02, Complex.normSq_nonneg c03, Complex.normSq_nonneg c04, Complex.normSq_nonneg c12, Complex.normSq_nonneg c13, Complex.normSq_nonneg c14, Complex.normSq_nonneg c23, Complex.normSq_nonneg c24, Complex.normSq_nonneg c34]
  have sa : b1 * c01 + b3 * c03 = 0 := by linear_combination h.st0 - (c02 : ℂ) * p2 - (c04 : ℂ) * p4
  have sb : b0 * c01 + b3 * c13 = 0 := by linear_combination h.st1 - (c12 : ℂ) * p2 - (c14 : ℂ) * p4
  have sc : b0 * c03 + b1 * c13 = 0 := by linear_combination h.st3 - (c23 : ℂ) * p2 - (c34 : ℂ) * p4
  have kk := SixQubit.Triangle.prod_eq_zero sc sb sa
  have z1 : c13 = 0 ∨ c03 = 0 := by
    rcases mul_eq_zero.mp kk with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · exact absurd y2 p3
      · exact Or.inl y2
    · exact Or.inr y
  have zz : c01 = 0 ∧ c03 = 0 ∧ c13 = 0 := by
    rcases z1 with y | y
    · have h1 : c01 = 0 := by
        have hx : b0 * c01 = 0 := by linear_combination sb - (b3 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p0
        · exact w
      have h2 : c03 = 0 := by
        have hx : b0 * c03 = 0 := by linear_combination sc - (b1 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p0
        · exact w
      exact ⟨h1, h2, y⟩
    · have h1 : c01 = 0 := by
        have hx : b1 * c01 = 0 := by linear_combination sa - (b3 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p1
        · exact w
      have h2 : c13 = 0 := by
        have hx : b1 * c13 = 0 := by linear_combination sc - (b0 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p1
        · exact w
      exact ⟨h1, y, h2⟩
  obtain ⟨u1, u2, u3⟩ := zz
  rw [u1, u2, u3, Complex.normSq_zero] at hW
  norm_num at hW

/-- The branch in which exactly the point amplitudes b2, b3 are nonzero. -/
theorem case12 {s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34 : ℂ} (h : Sys s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34)
    (p0 : b0 = 0) (p1 : b1 = 0) (_p2 : b2 ≠ 0) (p3 : b3 ≠ 0) (p4 : b4 = 0) : False := by
  have hab : c23 = 0 := by
    have hx : b3 * c23 = 0 := by linear_combination h.st2 - (c02 : ℂ) * p0 - (c12 : ℂ) * p1 - (c24 : ℂ) * p4
    rcases mul_eq_zero.mp hx with y | y
    · exact absurd y p3
    · exact y
  have hd1 := h.dg2
  have hd2 := h.dg3
  have ht := h.tb
  have hc := h.tc
  rw [hab, Complex.normSq_zero] at hd1 hd2 hc
  rw [p0, p1, p4, Complex.normSq_zero] at ht
  linarith only [hd1, hd2, ht, hc, Complex.normSq_nonneg b0, Complex.normSq_nonneg b1, Complex.normSq_nonneg b2, Complex.normSq_nonneg b3, Complex.normSq_nonneg b4, Complex.normSq_nonneg c01, Complex.normSq_nonneg c02, Complex.normSq_nonneg c03, Complex.normSq_nonneg c04, Complex.normSq_nonneg c12, Complex.normSq_nonneg c13, Complex.normSq_nonneg c14, Complex.normSq_nonneg c23, Complex.normSq_nonneg c24, Complex.normSq_nonneg c34]

/-- The branch in which exactly the point amplitudes b0, b2, b3 are nonzero. -/
theorem case13 {s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34 : ℂ} (h : Sys s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34)
    (p0 : b0 ≠ 0) (p1 : b1 = 0) (p2 : b2 ≠ 0) (p3 : b3 ≠ 0) (p4 : b4 = 0) : False := by
  have hd1 := h.dg0
  have hd2 := h.dg2
  have hd3 := h.dg3
  have ht := h.tb
  have hc := h.tc
  rw [p1, p4, Complex.normSq_zero] at ht
  have hW : (0:Real) < Complex.normSq c02 + Complex.normSq c03 + Complex.normSq c23 := by
    linarith only [hd1, hd2, hd3, ht, hc, Complex.normSq_nonneg b0, Complex.normSq_nonneg b1, Complex.normSq_nonneg b2, Complex.normSq_nonneg b3, Complex.normSq_nonneg b4, Complex.normSq_nonneg c01, Complex.normSq_nonneg c02, Complex.normSq_nonneg c03, Complex.normSq_nonneg c04, Complex.normSq_nonneg c12, Complex.normSq_nonneg c13, Complex.normSq_nonneg c14, Complex.normSq_nonneg c23, Complex.normSq_nonneg c24, Complex.normSq_nonneg c34]
  have sa : b2 * c02 + b3 * c03 = 0 := by linear_combination h.st0 - (c01 : ℂ) * p1 - (c04 : ℂ) * p4
  have sb : b0 * c02 + b3 * c23 = 0 := by linear_combination h.st2 - (c12 : ℂ) * p1 - (c24 : ℂ) * p4
  have sc : b0 * c03 + b2 * c23 = 0 := by linear_combination h.st3 - (c13 : ℂ) * p1 - (c34 : ℂ) * p4
  have kk := SixQubit.Triangle.prod_eq_zero sc sb sa
  have z1 : c23 = 0 ∨ c03 = 0 := by
    rcases mul_eq_zero.mp kk with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · exact absurd y2 p3
      · exact Or.inl y2
    · exact Or.inr y
  have zz : c02 = 0 ∧ c03 = 0 ∧ c23 = 0 := by
    rcases z1 with y | y
    · have h1 : c02 = 0 := by
        have hx : b0 * c02 = 0 := by linear_combination sb - (b3 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p0
        · exact w
      have h2 : c03 = 0 := by
        have hx : b0 * c03 = 0 := by linear_combination sc - (b2 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p0
        · exact w
      exact ⟨h1, h2, y⟩
    · have h1 : c02 = 0 := by
        have hx : b2 * c02 = 0 := by linear_combination sa - (b3 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p2
        · exact w
      have h2 : c23 = 0 := by
        have hx : b2 * c23 = 0 := by linear_combination sc - (b0 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p2
        · exact w
      exact ⟨h1, y, h2⟩
  obtain ⟨u1, u2, u3⟩ := zz
  rw [u1, u2, u3, Complex.normSq_zero] at hW
  norm_num at hW

/-- The branch in which exactly the point amplitudes b1, b2, b3 are nonzero. -/
theorem case14 {s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34 : ℂ} (h : Sys s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34)
    (p0 : b0 = 0) (p1 : b1 ≠ 0) (p2 : b2 ≠ 0) (p3 : b3 ≠ 0) (p4 : b4 = 0) : False := by
  have hd1 := h.dg1
  have hd2 := h.dg2
  have hd3 := h.dg3
  have ht := h.tb
  have hc := h.tc
  rw [p0, p4, Complex.normSq_zero] at ht
  have hW : (0:Real) < Complex.normSq c12 + Complex.normSq c13 + Complex.normSq c23 := by
    linarith only [hd1, hd2, hd3, ht, hc, Complex.normSq_nonneg b0, Complex.normSq_nonneg b1, Complex.normSq_nonneg b2, Complex.normSq_nonneg b3, Complex.normSq_nonneg b4, Complex.normSq_nonneg c01, Complex.normSq_nonneg c02, Complex.normSq_nonneg c03, Complex.normSq_nonneg c04, Complex.normSq_nonneg c12, Complex.normSq_nonneg c13, Complex.normSq_nonneg c14, Complex.normSq_nonneg c23, Complex.normSq_nonneg c24, Complex.normSq_nonneg c34]
  have sa : b2 * c12 + b3 * c13 = 0 := by linear_combination h.st1 - (c01 : ℂ) * p0 - (c14 : ℂ) * p4
  have sb : b1 * c12 + b3 * c23 = 0 := by linear_combination h.st2 - (c02 : ℂ) * p0 - (c24 : ℂ) * p4
  have sc : b1 * c13 + b2 * c23 = 0 := by linear_combination h.st3 - (c03 : ℂ) * p0 - (c34 : ℂ) * p4
  have kk := SixQubit.Triangle.prod_eq_zero sc sb sa
  have z1 : c23 = 0 ∨ c13 = 0 := by
    rcases mul_eq_zero.mp kk with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · exact absurd y2 p3
      · exact Or.inl y2
    · exact Or.inr y
  have zz : c12 = 0 ∧ c13 = 0 ∧ c23 = 0 := by
    rcases z1 with y | y
    · have h1 : c12 = 0 := by
        have hx : b1 * c12 = 0 := by linear_combination sb - (b3 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p1
        · exact w
      have h2 : c13 = 0 := by
        have hx : b1 * c13 = 0 := by linear_combination sc - (b2 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p1
        · exact w
      exact ⟨h1, h2, y⟩
    · have h1 : c12 = 0 := by
        have hx : b2 * c12 = 0 := by linear_combination sa - (b3 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p2
        · exact w
      have h2 : c23 = 0 := by
        have hx : b2 * c23 = 0 := by linear_combination sc - (b1 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p2
        · exact w
      exact ⟨h1, y, h2⟩
  obtain ⟨u1, u2, u3⟩ := zz
  rw [u1, u2, u3, Complex.normSq_zero] at hW
  norm_num at hW

/-- The branch in which exactly the point amplitudes b0, b1, b2, b3 are nonzero. -/
theorem case15 {s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34 : ℂ} (h : Sys s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34)
    (p0 : b0 ≠ 0) (p1 : b1 ≠ 0) (p2 : b2 ≠ 0) (p3 : b3 ≠ 0) (p4 : b4 = 0) : False := by
  have kk01 : k01 = 0 := by
    rcases mul_eq_zero.mp h.kb01_0 with y | y
    · exact absurd y p0
    · exact y
  have kk02 : k02 = 0 := by
    rcases mul_eq_zero.mp h.kb02_0 with y | y
    · exact absurd y p0
    · exact y
  have kk03 : k03 = 0 := by
    rcases mul_eq_zero.mp h.kb03_0 with y | y
    · exact absurd y p0
    · exact y
  have kk04 : k04 = 0 := by
    rcases mul_eq_zero.mp h.kb04_0 with y | y
    · exact absurd y p0
    · exact y
  have kk12 : k12 = 0 := by
    rcases mul_eq_zero.mp h.kb12_1 with y | y
    · exact absurd y p1
    · exact y
  have kk13 : k13 = 0 := by
    rcases mul_eq_zero.mp h.kb13_1 with y | y
    · exact absurd y p1
    · exact y
  have kk14 : k14 = 0 := by
    rcases mul_eq_zero.mp h.kb14_1 with y | y
    · exact absurd y p1
    · exact y
  have kk23 : k23 = 0 := by
    rcases mul_eq_zero.mp h.kb23_2 with y | y
    · exact absurd y p2
    · exact y
  have kk24 : k24 = 0 := by
    rcases mul_eq_zero.mp h.kb24_2 with y | y
    · exact absurd y p2
    · exact y
  have kk34 : k34 = 0 := by
    rcases mul_eq_zero.mp h.kb34_3 with y | y
    · exact absurd y p3
    · exact y
  have haf0 : c12 * c34 + c13 * c24 + c14 * c23 = 0 := by
    have hx : (2 : ℂ) * s * (c12 * c34 + c13 * c24 + c14 * c23) = 0 := by
      linear_combination (-1 : ℂ) * h.hf0 + (c12 : ℂ) * kk34 + (c34 : ℂ) * kk12 + (c13 : ℂ) * kk24 + (c24 : ℂ) * kk13 + (c14 : ℂ) * kk23 + (c23 : ℂ) * kk14
    rcases mul_eq_zero.mp hx with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · norm_num at y2
      · exact absurd y2 h.hs
    · exact y
  have haf1 : c02 * c34 + c03 * c24 + c04 * c23 = 0 := by
    have hx : (2 : ℂ) * s * (c02 * c34 + c03 * c24 + c04 * c23) = 0 := by
      linear_combination (-1 : ℂ) * h.hf1 + (c02 : ℂ) * kk34 + (c34 : ℂ) * kk02 + (c03 : ℂ) * kk24 + (c24 : ℂ) * kk03 + (c04 : ℂ) * kk23 + (c23 : ℂ) * kk04
    rcases mul_eq_zero.mp hx with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · norm_num at y2
      · exact absurd y2 h.hs
    · exact y
  have haf2 : c01 * c34 + c03 * c14 + c04 * c13 = 0 := by
    have hx : (2 : ℂ) * s * (c01 * c34 + c03 * c14 + c04 * c13) = 0 := by
      linear_combination (-1 : ℂ) * h.hf2 + (c01 : ℂ) * kk34 + (c34 : ℂ) * kk01 + (c03 : ℂ) * kk14 + (c14 : ℂ) * kk03 + (c04 : ℂ) * kk13 + (c13 : ℂ) * kk04
    rcases mul_eq_zero.mp hx with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · norm_num at y2
      · exact absurd y2 h.hs
    · exact y
  have haf3 : c01 * c24 + c02 * c14 + c04 * c12 = 0 := by
    have hx : (2 : ℂ) * s * (c01 * c24 + c02 * c14 + c04 * c12) = 0 := by
      linear_combination (-1 : ℂ) * h.hf3 + (c01 : ℂ) * kk24 + (c24 : ℂ) * kk01 + (c02 : ℂ) * kk14 + (c14 : ℂ) * kk02 + (c04 : ℂ) * kk12 + (c12 : ℂ) * kk04
    rcases mul_eq_zero.mp hx with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · norm_num at y2
      · exact absurd y2 h.hs
    · exact y
  have haf4 : c01 * c23 + c02 * c13 + c03 * c12 = 0 := by
    have hx : (2 : ℂ) * s * (c01 * c23 + c02 * c13 + c03 * c12) = 0 := by
      linear_combination (-1 : ℂ) * h.hf4 + (c01 : ℂ) * kk23 + (c23 : ℂ) * kk01 + (c02 : ℂ) * kk13 + (c13 : ℂ) * kk02 + (c03 : ℂ) * kk12 + (c12 : ℂ) * kk03
    rcases mul_eq_zero.mp hx with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · norm_num at y2
      · exact absurd y2 h.hs
    · exact y
  have dg_0_1 : c02 = 0 → c03 = 0 → c04 = 0 → False := by
    intro z1 z2 z3
    have hij : c01 = 0 := by
      have hx : b1 * c01 = 0 := by linear_combination h.st0 - (b2 : ℂ) * z1 - (b3 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p1
      · exact y
    have hd := h.dg0
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b0]
  have dg_0_2 : c01 = 0 → c03 = 0 → c04 = 0 → False := by
    intro z1 z2 z3
    have hij : c02 = 0 := by
      have hx : b2 * c02 = 0 := by linear_combination h.st0 - (b1 : ℂ) * z1 - (b3 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p2
      · exact y
    have hd := h.dg0
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b0]
  have dg_0_3 : c01 = 0 → c02 = 0 → c04 = 0 → False := by
    intro z1 z2 z3
    have hij : c03 = 0 := by
      have hx : b3 * c03 = 0 := by linear_combination h.st0 - (b1 : ℂ) * z1 - (b2 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p3
      · exact y
    have hd := h.dg0
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b0]
  have dg_0_4 : c01 = 0 → c02 = 0 → c03 = 0 → False := by
    intro z1 z2 z3
    have hd1 := h.dg0
    have hd2 := h.dg4
    rw [z1, z2, z3, Complex.normSq_zero] at hd1
    rw [p4, Complex.normSq_zero] at hd2
    have hz : Complex.normSq b0 = 0 := by linarith only [hd1, hd2, Complex.normSq_nonneg b0, Complex.normSq_nonneg c14, Complex.normSq_nonneg c24, Complex.normSq_nonneg c34]
    exact p0 (Complex.normSq_eq_zero.mp hz)
  have dg_1_0 : c12 = 0 → c13 = 0 → c14 = 0 → False := by
    intro z1 z2 z3
    have hij : c01 = 0 := by
      have hx : b0 * c01 = 0 := by linear_combination h.st1 - (b2 : ℂ) * z1 - (b3 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p0
      · exact y
    have hd := h.dg1
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b1]
  have dg_1_2 : c01 = 0 → c13 = 0 → c14 = 0 → False := by
    intro z1 z2 z3
    have hij : c12 = 0 := by
      have hx : b2 * c12 = 0 := by linear_combination h.st1 - (b0 : ℂ) * z1 - (b3 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p2
      · exact y
    have hd := h.dg1
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b1]
  have dg_1_3 : c01 = 0 → c12 = 0 → c14 = 0 → False := by
    intro z1 z2 z3
    have hij : c13 = 0 := by
      have hx : b3 * c13 = 0 := by linear_combination h.st1 - (b0 : ℂ) * z1 - (b2 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p3
      · exact y
    have hd := h.dg1
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b1]
  have dg_1_4 : c01 = 0 → c12 = 0 → c13 = 0 → False := by
    intro z1 z2 z3
    have hd1 := h.dg1
    have hd2 := h.dg4
    rw [z1, z2, z3, Complex.normSq_zero] at hd1
    rw [p4, Complex.normSq_zero] at hd2
    have hz : Complex.normSq b1 = 0 := by linarith only [hd1, hd2, Complex.normSq_nonneg b1, Complex.normSq_nonneg c04, Complex.normSq_nonneg c24, Complex.normSq_nonneg c34]
    exact p1 (Complex.normSq_eq_zero.mp hz)
  have dg_2_0 : c12 = 0 → c23 = 0 → c24 = 0 → False := by
    intro z1 z2 z3
    have hij : c02 = 0 := by
      have hx : b0 * c02 = 0 := by linear_combination h.st2 - (b1 : ℂ) * z1 - (b3 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p0
      · exact y
    have hd := h.dg2
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b2]
  have dg_2_1 : c02 = 0 → c23 = 0 → c24 = 0 → False := by
    intro z1 z2 z3
    have hij : c12 = 0 := by
      have hx : b1 * c12 = 0 := by linear_combination h.st2 - (b0 : ℂ) * z1 - (b3 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p1
      · exact y
    have hd := h.dg2
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b2]
  have dg_2_3 : c02 = 0 → c12 = 0 → c24 = 0 → False := by
    intro z1 z2 z3
    have hij : c23 = 0 := by
      have hx : b3 * c23 = 0 := by linear_combination h.st2 - (b0 : ℂ) * z1 - (b1 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p3
      · exact y
    have hd := h.dg2
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b2]
  have dg_2_4 : c02 = 0 → c12 = 0 → c23 = 0 → False := by
    intro z1 z2 z3
    have hd1 := h.dg2
    have hd2 := h.dg4
    rw [z1, z2, z3, Complex.normSq_zero] at hd1
    rw [p4, Complex.normSq_zero] at hd2
    have hz : Complex.normSq b2 = 0 := by linarith only [hd1, hd2, Complex.normSq_nonneg b2, Complex.normSq_nonneg c04, Complex.normSq_nonneg c14, Complex.normSq_nonneg c34]
    exact p2 (Complex.normSq_eq_zero.mp hz)
  have dg_3_0 : c13 = 0 → c23 = 0 → c34 = 0 → False := by
    intro z1 z2 z3
    have hij : c03 = 0 := by
      have hx : b0 * c03 = 0 := by linear_combination h.st3 - (b1 : ℂ) * z1 - (b2 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p0
      · exact y
    have hd := h.dg3
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b3]
  have dg_3_1 : c03 = 0 → c23 = 0 → c34 = 0 → False := by
    intro z1 z2 z3
    have hij : c13 = 0 := by
      have hx : b1 * c13 = 0 := by linear_combination h.st3 - (b0 : ℂ) * z1 - (b2 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p1
      · exact y
    have hd := h.dg3
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b3]
  have dg_3_2 : c03 = 0 → c13 = 0 → c34 = 0 → False := by
    intro z1 z2 z3
    have hij : c23 = 0 := by
      have hx : b2 * c23 = 0 := by linear_combination h.st3 - (b0 : ℂ) * z1 - (b1 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p2
      · exact y
    have hd := h.dg3
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b3]
  have dg_3_4 : c03 = 0 → c13 = 0 → c23 = 0 → False := by
    intro z1 z2 z3
    have hd1 := h.dg3
    have hd2 := h.dg4
    rw [z1, z2, z3, Complex.normSq_zero] at hd1
    rw [p4, Complex.normSq_zero] at hd2
    have hz : Complex.normSq b3 = 0 := by linarith only [hd1, hd2, Complex.normSq_nonneg b3, Complex.normSq_nonneg c04, Complex.normSq_nonneg c14, Complex.normSq_nonneg c24]
    exact p3 (Complex.normSq_eq_zero.mp hz)
  have dg_4_0 : c14 = 0 → c24 = 0 → c34 = 0 → False := by
    intro z1 z2 z3
    have hij : c04 = 0 := by
      have hx : b0 * c04 = 0 := by linear_combination h.st4 - (b1 : ℂ) * z1 - (b2 : ℂ) * z2 - (b3 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p0
      · exact y
    have hd := h.dg4
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b4]
  have dg_4_1 : c04 = 0 → c24 = 0 → c34 = 0 → False := by
    intro z1 z2 z3
    have hij : c14 = 0 := by
      have hx : b1 * c14 = 0 := by linear_combination h.st4 - (b0 : ℂ) * z1 - (b2 : ℂ) * z2 - (b3 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p1
      · exact y
    have hd := h.dg4
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b4]
  have dg_4_2 : c04 = 0 → c14 = 0 → c34 = 0 → False := by
    intro z1 z2 z3
    have hij : c24 = 0 := by
      have hx : b2 * c24 = 0 := by linear_combination h.st4 - (b0 : ℂ) * z1 - (b1 : ℂ) * z2 - (b3 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p2
      · exact y
    have hd := h.dg4
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b4]
  have dg_4_3 : c04 = 0 → c14 = 0 → c24 = 0 → False := by
    intro z1 z2 z3
    have hij : c34 = 0 := by
      have hx : b3 * c34 = 0 := by linear_combination h.st4 - (b0 : ℂ) * z1 - (b1 : ℂ) * z2 - (b2 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p3
      · exact y
    have hd := h.dg4
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b4]
  obtain ⟨d01, d02, d03, d04, d12, d13, d14, d23, d24, d34⟩ := dets0 h.st0 h.st1 h.st2 h.st3 h.st4 haf0 haf1 haf2 haf3 haf4 p0
  exact graph haf0 haf1 haf2 haf3 haf4 dg_0_1 dg_0_2 dg_0_3 dg_0_4 dg_1_0 dg_1_2 dg_1_3 dg_1_4 dg_2_0 dg_2_1 dg_2_3 dg_2_4 dg_3_0 dg_3_1 dg_3_2 dg_3_4 dg_4_0 dg_4_1 dg_4_2 dg_4_3 d01 d02 d03 d04 d12 d13 d14 d23 d24 d34

/-- The branch in which exactly the point amplitudes b4 are nonzero. -/
theorem case16 {s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34 : ℂ} (h : Sys s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34)
    (p0 : b0 = 0) (p1 : b1 = 0) (p2 : b2 = 0) (p3 : b3 = 0) (p4 : b4 ≠ 0) : False := by
  have x0 : c04 = 0 := by
    have hx : b4 * c04 = 0 := by linear_combination h.st0 - (c01 : ℂ) * p1 - (c02 : ℂ) * p2 - (c03 : ℂ) * p3
    rcases mul_eq_zero.mp hx with y | y
    · exact absurd y p4
    · exact y
  have x1 : c14 = 0 := by
    have hx : b4 * c14 = 0 := by linear_combination h.st1 - (c01 : ℂ) * p0 - (c12 : ℂ) * p2 - (c13 : ℂ) * p3
    rcases mul_eq_zero.mp hx with y | y
    · exact absurd y p4
    · exact y
  have x2 : c24 = 0 := by
    have hx : b4 * c24 = 0 := by linear_combination h.st2 - (c02 : ℂ) * p0 - (c12 : ℂ) * p1 - (c23 : ℂ) * p3
    rcases mul_eq_zero.mp hx with y | y
    · exact absurd y p4
    · exact y
  have x3 : c34 = 0 := by
    have hx : b4 * c34 = 0 := by linear_combination h.st3 - (c03 : ℂ) * p0 - (c13 : ℂ) * p1 - (c23 : ℂ) * p2
    rcases mul_eq_zero.mp hx with y | y
    · exact absurd y p4
    · exact y
  have hd := h.dg4
  rw [x0, x1, x2, x3, Complex.normSq_zero] at hd
  linarith only [hd, Complex.normSq_nonneg b4]

/-- The branch in which exactly the point amplitudes b0, b4 are nonzero. -/
theorem case17 {s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34 : ℂ} (h : Sys s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34)
    (_p0 : b0 ≠ 0) (p1 : b1 = 0) (p2 : b2 = 0) (p3 : b3 = 0) (p4 : b4 ≠ 0) : False := by
  have hab : c04 = 0 := by
    have hx : b4 * c04 = 0 := by linear_combination h.st0 - (c01 : ℂ) * p1 - (c02 : ℂ) * p2 - (c03 : ℂ) * p3
    rcases mul_eq_zero.mp hx with y | y
    · exact absurd y p4
    · exact y
  have hd1 := h.dg0
  have hd2 := h.dg4
  have ht := h.tb
  have hc := h.tc
  rw [hab, Complex.normSq_zero] at hd1 hd2 hc
  rw [p1, p2, p3, Complex.normSq_zero] at ht
  linarith only [hd1, hd2, ht, hc, Complex.normSq_nonneg b0, Complex.normSq_nonneg b1, Complex.normSq_nonneg b2, Complex.normSq_nonneg b3, Complex.normSq_nonneg b4, Complex.normSq_nonneg c01, Complex.normSq_nonneg c02, Complex.normSq_nonneg c03, Complex.normSq_nonneg c04, Complex.normSq_nonneg c12, Complex.normSq_nonneg c13, Complex.normSq_nonneg c14, Complex.normSq_nonneg c23, Complex.normSq_nonneg c24, Complex.normSq_nonneg c34]

/-- The branch in which exactly the point amplitudes b1, b4 are nonzero. -/
theorem case18 {s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34 : ℂ} (h : Sys s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34)
    (p0 : b0 = 0) (_p1 : b1 ≠ 0) (p2 : b2 = 0) (p3 : b3 = 0) (p4 : b4 ≠ 0) : False := by
  have hab : c14 = 0 := by
    have hx : b4 * c14 = 0 := by linear_combination h.st1 - (c01 : ℂ) * p0 - (c12 : ℂ) * p2 - (c13 : ℂ) * p3
    rcases mul_eq_zero.mp hx with y | y
    · exact absurd y p4
    · exact y
  have hd1 := h.dg1
  have hd2 := h.dg4
  have ht := h.tb
  have hc := h.tc
  rw [hab, Complex.normSq_zero] at hd1 hd2 hc
  rw [p0, p2, p3, Complex.normSq_zero] at ht
  linarith only [hd1, hd2, ht, hc, Complex.normSq_nonneg b0, Complex.normSq_nonneg b1, Complex.normSq_nonneg b2, Complex.normSq_nonneg b3, Complex.normSq_nonneg b4, Complex.normSq_nonneg c01, Complex.normSq_nonneg c02, Complex.normSq_nonneg c03, Complex.normSq_nonneg c04, Complex.normSq_nonneg c12, Complex.normSq_nonneg c13, Complex.normSq_nonneg c14, Complex.normSq_nonneg c23, Complex.normSq_nonneg c24, Complex.normSq_nonneg c34]

/-- The branch in which exactly the point amplitudes b0, b1, b4 are nonzero. -/
theorem case19 {s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34 : ℂ} (h : Sys s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34)
    (p0 : b0 ≠ 0) (p1 : b1 ≠ 0) (p2 : b2 = 0) (p3 : b3 = 0) (p4 : b4 ≠ 0) : False := by
  have hd1 := h.dg0
  have hd2 := h.dg1
  have hd3 := h.dg4
  have ht := h.tb
  have hc := h.tc
  rw [p2, p3, Complex.normSq_zero] at ht
  have hW : (0:Real) < Complex.normSq c01 + Complex.normSq c04 + Complex.normSq c14 := by
    linarith only [hd1, hd2, hd3, ht, hc, Complex.normSq_nonneg b0, Complex.normSq_nonneg b1, Complex.normSq_nonneg b2, Complex.normSq_nonneg b3, Complex.normSq_nonneg b4, Complex.normSq_nonneg c01, Complex.normSq_nonneg c02, Complex.normSq_nonneg c03, Complex.normSq_nonneg c04, Complex.normSq_nonneg c12, Complex.normSq_nonneg c13, Complex.normSq_nonneg c14, Complex.normSq_nonneg c23, Complex.normSq_nonneg c24, Complex.normSq_nonneg c34]
  have sa : b1 * c01 + b4 * c04 = 0 := by linear_combination h.st0 - (c02 : ℂ) * p2 - (c03 : ℂ) * p3
  have sb : b0 * c01 + b4 * c14 = 0 := by linear_combination h.st1 - (c12 : ℂ) * p2 - (c13 : ℂ) * p3
  have sc : b0 * c04 + b1 * c14 = 0 := by linear_combination h.st4 - (c24 : ℂ) * p2 - (c34 : ℂ) * p3
  have kk := SixQubit.Triangle.prod_eq_zero sc sb sa
  have z1 : c14 = 0 ∨ c04 = 0 := by
    rcases mul_eq_zero.mp kk with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · exact absurd y2 p4
      · exact Or.inl y2
    · exact Or.inr y
  have zz : c01 = 0 ∧ c04 = 0 ∧ c14 = 0 := by
    rcases z1 with y | y
    · have h1 : c01 = 0 := by
        have hx : b0 * c01 = 0 := by linear_combination sb - (b4 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p0
        · exact w
      have h2 : c04 = 0 := by
        have hx : b0 * c04 = 0 := by linear_combination sc - (b1 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p0
        · exact w
      exact ⟨h1, h2, y⟩
    · have h1 : c01 = 0 := by
        have hx : b1 * c01 = 0 := by linear_combination sa - (b4 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p1
        · exact w
      have h2 : c14 = 0 := by
        have hx : b1 * c14 = 0 := by linear_combination sc - (b0 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p1
        · exact w
      exact ⟨h1, y, h2⟩
  obtain ⟨u1, u2, u3⟩ := zz
  rw [u1, u2, u3, Complex.normSq_zero] at hW
  norm_num at hW

/-- The branch in which exactly the point amplitudes b2, b4 are nonzero. -/
theorem case20 {s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34 : ℂ} (h : Sys s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34)
    (p0 : b0 = 0) (p1 : b1 = 0) (_p2 : b2 ≠ 0) (p3 : b3 = 0) (p4 : b4 ≠ 0) : False := by
  have hab : c24 = 0 := by
    have hx : b4 * c24 = 0 := by linear_combination h.st2 - (c02 : ℂ) * p0 - (c12 : ℂ) * p1 - (c23 : ℂ) * p3
    rcases mul_eq_zero.mp hx with y | y
    · exact absurd y p4
    · exact y
  have hd1 := h.dg2
  have hd2 := h.dg4
  have ht := h.tb
  have hc := h.tc
  rw [hab, Complex.normSq_zero] at hd1 hd2 hc
  rw [p0, p1, p3, Complex.normSq_zero] at ht
  linarith only [hd1, hd2, ht, hc, Complex.normSq_nonneg b0, Complex.normSq_nonneg b1, Complex.normSq_nonneg b2, Complex.normSq_nonneg b3, Complex.normSq_nonneg b4, Complex.normSq_nonneg c01, Complex.normSq_nonneg c02, Complex.normSq_nonneg c03, Complex.normSq_nonneg c04, Complex.normSq_nonneg c12, Complex.normSq_nonneg c13, Complex.normSq_nonneg c14, Complex.normSq_nonneg c23, Complex.normSq_nonneg c24, Complex.normSq_nonneg c34]

/-- The branch in which exactly the point amplitudes b0, b2, b4 are nonzero. -/
theorem case21 {s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34 : ℂ} (h : Sys s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34)
    (p0 : b0 ≠ 0) (p1 : b1 = 0) (p2 : b2 ≠ 0) (p3 : b3 = 0) (p4 : b4 ≠ 0) : False := by
  have hd1 := h.dg0
  have hd2 := h.dg2
  have hd3 := h.dg4
  have ht := h.tb
  have hc := h.tc
  rw [p1, p3, Complex.normSq_zero] at ht
  have hW : (0:Real) < Complex.normSq c02 + Complex.normSq c04 + Complex.normSq c24 := by
    linarith only [hd1, hd2, hd3, ht, hc, Complex.normSq_nonneg b0, Complex.normSq_nonneg b1, Complex.normSq_nonneg b2, Complex.normSq_nonneg b3, Complex.normSq_nonneg b4, Complex.normSq_nonneg c01, Complex.normSq_nonneg c02, Complex.normSq_nonneg c03, Complex.normSq_nonneg c04, Complex.normSq_nonneg c12, Complex.normSq_nonneg c13, Complex.normSq_nonneg c14, Complex.normSq_nonneg c23, Complex.normSq_nonneg c24, Complex.normSq_nonneg c34]
  have sa : b2 * c02 + b4 * c04 = 0 := by linear_combination h.st0 - (c01 : ℂ) * p1 - (c03 : ℂ) * p3
  have sb : b0 * c02 + b4 * c24 = 0 := by linear_combination h.st2 - (c12 : ℂ) * p1 - (c23 : ℂ) * p3
  have sc : b0 * c04 + b2 * c24 = 0 := by linear_combination h.st4 - (c14 : ℂ) * p1 - (c34 : ℂ) * p3
  have kk := SixQubit.Triangle.prod_eq_zero sc sb sa
  have z1 : c24 = 0 ∨ c04 = 0 := by
    rcases mul_eq_zero.mp kk with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · exact absurd y2 p4
      · exact Or.inl y2
    · exact Or.inr y
  have zz : c02 = 0 ∧ c04 = 0 ∧ c24 = 0 := by
    rcases z1 with y | y
    · have h1 : c02 = 0 := by
        have hx : b0 * c02 = 0 := by linear_combination sb - (b4 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p0
        · exact w
      have h2 : c04 = 0 := by
        have hx : b0 * c04 = 0 := by linear_combination sc - (b2 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p0
        · exact w
      exact ⟨h1, h2, y⟩
    · have h1 : c02 = 0 := by
        have hx : b2 * c02 = 0 := by linear_combination sa - (b4 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p2
        · exact w
      have h2 : c24 = 0 := by
        have hx : b2 * c24 = 0 := by linear_combination sc - (b0 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p2
        · exact w
      exact ⟨h1, y, h2⟩
  obtain ⟨u1, u2, u3⟩ := zz
  rw [u1, u2, u3, Complex.normSq_zero] at hW
  norm_num at hW

/-- The branch in which exactly the point amplitudes b1, b2, b4 are nonzero. -/
theorem case22 {s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34 : ℂ} (h : Sys s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34)
    (p0 : b0 = 0) (p1 : b1 ≠ 0) (p2 : b2 ≠ 0) (p3 : b3 = 0) (p4 : b4 ≠ 0) : False := by
  have hd1 := h.dg1
  have hd2 := h.dg2
  have hd3 := h.dg4
  have ht := h.tb
  have hc := h.tc
  rw [p0, p3, Complex.normSq_zero] at ht
  have hW : (0:Real) < Complex.normSq c12 + Complex.normSq c14 + Complex.normSq c24 := by
    linarith only [hd1, hd2, hd3, ht, hc, Complex.normSq_nonneg b0, Complex.normSq_nonneg b1, Complex.normSq_nonneg b2, Complex.normSq_nonneg b3, Complex.normSq_nonneg b4, Complex.normSq_nonneg c01, Complex.normSq_nonneg c02, Complex.normSq_nonneg c03, Complex.normSq_nonneg c04, Complex.normSq_nonneg c12, Complex.normSq_nonneg c13, Complex.normSq_nonneg c14, Complex.normSq_nonneg c23, Complex.normSq_nonneg c24, Complex.normSq_nonneg c34]
  have sa : b2 * c12 + b4 * c14 = 0 := by linear_combination h.st1 - (c01 : ℂ) * p0 - (c13 : ℂ) * p3
  have sb : b1 * c12 + b4 * c24 = 0 := by linear_combination h.st2 - (c02 : ℂ) * p0 - (c23 : ℂ) * p3
  have sc : b1 * c14 + b2 * c24 = 0 := by linear_combination h.st4 - (c04 : ℂ) * p0 - (c34 : ℂ) * p3
  have kk := SixQubit.Triangle.prod_eq_zero sc sb sa
  have z1 : c24 = 0 ∨ c14 = 0 := by
    rcases mul_eq_zero.mp kk with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · exact absurd y2 p4
      · exact Or.inl y2
    · exact Or.inr y
  have zz : c12 = 0 ∧ c14 = 0 ∧ c24 = 0 := by
    rcases z1 with y | y
    · have h1 : c12 = 0 := by
        have hx : b1 * c12 = 0 := by linear_combination sb - (b4 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p1
        · exact w
      have h2 : c14 = 0 := by
        have hx : b1 * c14 = 0 := by linear_combination sc - (b2 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p1
        · exact w
      exact ⟨h1, h2, y⟩
    · have h1 : c12 = 0 := by
        have hx : b2 * c12 = 0 := by linear_combination sa - (b4 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p2
        · exact w
      have h2 : c24 = 0 := by
        have hx : b2 * c24 = 0 := by linear_combination sc - (b1 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p2
        · exact w
      exact ⟨h1, y, h2⟩
  obtain ⟨u1, u2, u3⟩ := zz
  rw [u1, u2, u3, Complex.normSq_zero] at hW
  norm_num at hW

/-- The branch in which exactly the point amplitudes b0, b1, b2, b4 are nonzero. -/
theorem case23 {s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34 : ℂ} (h : Sys s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34)
    (p0 : b0 ≠ 0) (p1 : b1 ≠ 0) (p2 : b2 ≠ 0) (p3 : b3 = 0) (p4 : b4 ≠ 0) : False := by
  have kk01 : k01 = 0 := by
    rcases mul_eq_zero.mp h.kb01_0 with y | y
    · exact absurd y p0
    · exact y
  have kk02 : k02 = 0 := by
    rcases mul_eq_zero.mp h.kb02_0 with y | y
    · exact absurd y p0
    · exact y
  have kk03 : k03 = 0 := by
    rcases mul_eq_zero.mp h.kb03_0 with y | y
    · exact absurd y p0
    · exact y
  have kk04 : k04 = 0 := by
    rcases mul_eq_zero.mp h.kb04_0 with y | y
    · exact absurd y p0
    · exact y
  have kk12 : k12 = 0 := by
    rcases mul_eq_zero.mp h.kb12_1 with y | y
    · exact absurd y p1
    · exact y
  have kk13 : k13 = 0 := by
    rcases mul_eq_zero.mp h.kb13_1 with y | y
    · exact absurd y p1
    · exact y
  have kk14 : k14 = 0 := by
    rcases mul_eq_zero.mp h.kb14_1 with y | y
    · exact absurd y p1
    · exact y
  have kk23 : k23 = 0 := by
    rcases mul_eq_zero.mp h.kb23_2 with y | y
    · exact absurd y p2
    · exact y
  have kk24 : k24 = 0 := by
    rcases mul_eq_zero.mp h.kb24_2 with y | y
    · exact absurd y p2
    · exact y
  have kk34 : k34 = 0 := by
    rcases mul_eq_zero.mp h.kb34_4 with y | y
    · exact absurd y p4
    · exact y
  have haf0 : c12 * c34 + c13 * c24 + c14 * c23 = 0 := by
    have hx : (2 : ℂ) * s * (c12 * c34 + c13 * c24 + c14 * c23) = 0 := by
      linear_combination (-1 : ℂ) * h.hf0 + (c12 : ℂ) * kk34 + (c34 : ℂ) * kk12 + (c13 : ℂ) * kk24 + (c24 : ℂ) * kk13 + (c14 : ℂ) * kk23 + (c23 : ℂ) * kk14
    rcases mul_eq_zero.mp hx with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · norm_num at y2
      · exact absurd y2 h.hs
    · exact y
  have haf1 : c02 * c34 + c03 * c24 + c04 * c23 = 0 := by
    have hx : (2 : ℂ) * s * (c02 * c34 + c03 * c24 + c04 * c23) = 0 := by
      linear_combination (-1 : ℂ) * h.hf1 + (c02 : ℂ) * kk34 + (c34 : ℂ) * kk02 + (c03 : ℂ) * kk24 + (c24 : ℂ) * kk03 + (c04 : ℂ) * kk23 + (c23 : ℂ) * kk04
    rcases mul_eq_zero.mp hx with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · norm_num at y2
      · exact absurd y2 h.hs
    · exact y
  have haf2 : c01 * c34 + c03 * c14 + c04 * c13 = 0 := by
    have hx : (2 : ℂ) * s * (c01 * c34 + c03 * c14 + c04 * c13) = 0 := by
      linear_combination (-1 : ℂ) * h.hf2 + (c01 : ℂ) * kk34 + (c34 : ℂ) * kk01 + (c03 : ℂ) * kk14 + (c14 : ℂ) * kk03 + (c04 : ℂ) * kk13 + (c13 : ℂ) * kk04
    rcases mul_eq_zero.mp hx with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · norm_num at y2
      · exact absurd y2 h.hs
    · exact y
  have haf3 : c01 * c24 + c02 * c14 + c04 * c12 = 0 := by
    have hx : (2 : ℂ) * s * (c01 * c24 + c02 * c14 + c04 * c12) = 0 := by
      linear_combination (-1 : ℂ) * h.hf3 + (c01 : ℂ) * kk24 + (c24 : ℂ) * kk01 + (c02 : ℂ) * kk14 + (c14 : ℂ) * kk02 + (c04 : ℂ) * kk12 + (c12 : ℂ) * kk04
    rcases mul_eq_zero.mp hx with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · norm_num at y2
      · exact absurd y2 h.hs
    · exact y
  have haf4 : c01 * c23 + c02 * c13 + c03 * c12 = 0 := by
    have hx : (2 : ℂ) * s * (c01 * c23 + c02 * c13 + c03 * c12) = 0 := by
      linear_combination (-1 : ℂ) * h.hf4 + (c01 : ℂ) * kk23 + (c23 : ℂ) * kk01 + (c02 : ℂ) * kk13 + (c13 : ℂ) * kk02 + (c03 : ℂ) * kk12 + (c12 : ℂ) * kk03
    rcases mul_eq_zero.mp hx with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · norm_num at y2
      · exact absurd y2 h.hs
    · exact y
  have dg_0_1 : c02 = 0 → c03 = 0 → c04 = 0 → False := by
    intro z1 z2 z3
    have hij : c01 = 0 := by
      have hx : b1 * c01 = 0 := by linear_combination h.st0 - (b2 : ℂ) * z1 - (b3 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p1
      · exact y
    have hd := h.dg0
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b0]
  have dg_0_2 : c01 = 0 → c03 = 0 → c04 = 0 → False := by
    intro z1 z2 z3
    have hij : c02 = 0 := by
      have hx : b2 * c02 = 0 := by linear_combination h.st0 - (b1 : ℂ) * z1 - (b3 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p2
      · exact y
    have hd := h.dg0
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b0]
  have dg_0_3 : c01 = 0 → c02 = 0 → c04 = 0 → False := by
    intro z1 z2 z3
    have hd1 := h.dg0
    have hd2 := h.dg3
    rw [z1, z2, z3, Complex.normSq_zero] at hd1
    rw [p3, Complex.normSq_zero] at hd2
    have hz : Complex.normSq b0 = 0 := by linarith only [hd1, hd2, Complex.normSq_nonneg b0, Complex.normSq_nonneg c13, Complex.normSq_nonneg c23, Complex.normSq_nonneg c34]
    exact p0 (Complex.normSq_eq_zero.mp hz)
  have dg_0_4 : c01 = 0 → c02 = 0 → c03 = 0 → False := by
    intro z1 z2 z3
    have hij : c04 = 0 := by
      have hx : b4 * c04 = 0 := by linear_combination h.st0 - (b1 : ℂ) * z1 - (b2 : ℂ) * z2 - (b3 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p4
      · exact y
    have hd := h.dg0
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b0]
  have dg_1_0 : c12 = 0 → c13 = 0 → c14 = 0 → False := by
    intro z1 z2 z3
    have hij : c01 = 0 := by
      have hx : b0 * c01 = 0 := by linear_combination h.st1 - (b2 : ℂ) * z1 - (b3 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p0
      · exact y
    have hd := h.dg1
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b1]
  have dg_1_2 : c01 = 0 → c13 = 0 → c14 = 0 → False := by
    intro z1 z2 z3
    have hij : c12 = 0 := by
      have hx : b2 * c12 = 0 := by linear_combination h.st1 - (b0 : ℂ) * z1 - (b3 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p2
      · exact y
    have hd := h.dg1
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b1]
  have dg_1_3 : c01 = 0 → c12 = 0 → c14 = 0 → False := by
    intro z1 z2 z3
    have hd1 := h.dg1
    have hd2 := h.dg3
    rw [z1, z2, z3, Complex.normSq_zero] at hd1
    rw [p3, Complex.normSq_zero] at hd2
    have hz : Complex.normSq b1 = 0 := by linarith only [hd1, hd2, Complex.normSq_nonneg b1, Complex.normSq_nonneg c03, Complex.normSq_nonneg c23, Complex.normSq_nonneg c34]
    exact p1 (Complex.normSq_eq_zero.mp hz)
  have dg_1_4 : c01 = 0 → c12 = 0 → c13 = 0 → False := by
    intro z1 z2 z3
    have hij : c14 = 0 := by
      have hx : b4 * c14 = 0 := by linear_combination h.st1 - (b0 : ℂ) * z1 - (b2 : ℂ) * z2 - (b3 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p4
      · exact y
    have hd := h.dg1
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b1]
  have dg_2_0 : c12 = 0 → c23 = 0 → c24 = 0 → False := by
    intro z1 z2 z3
    have hij : c02 = 0 := by
      have hx : b0 * c02 = 0 := by linear_combination h.st2 - (b1 : ℂ) * z1 - (b3 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p0
      · exact y
    have hd := h.dg2
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b2]
  have dg_2_1 : c02 = 0 → c23 = 0 → c24 = 0 → False := by
    intro z1 z2 z3
    have hij : c12 = 0 := by
      have hx : b1 * c12 = 0 := by linear_combination h.st2 - (b0 : ℂ) * z1 - (b3 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p1
      · exact y
    have hd := h.dg2
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b2]
  have dg_2_3 : c02 = 0 → c12 = 0 → c24 = 0 → False := by
    intro z1 z2 z3
    have hd1 := h.dg2
    have hd2 := h.dg3
    rw [z1, z2, z3, Complex.normSq_zero] at hd1
    rw [p3, Complex.normSq_zero] at hd2
    have hz : Complex.normSq b2 = 0 := by linarith only [hd1, hd2, Complex.normSq_nonneg b2, Complex.normSq_nonneg c03, Complex.normSq_nonneg c13, Complex.normSq_nonneg c34]
    exact p2 (Complex.normSq_eq_zero.mp hz)
  have dg_2_4 : c02 = 0 → c12 = 0 → c23 = 0 → False := by
    intro z1 z2 z3
    have hij : c24 = 0 := by
      have hx : b4 * c24 = 0 := by linear_combination h.st2 - (b0 : ℂ) * z1 - (b1 : ℂ) * z2 - (b3 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p4
      · exact y
    have hd := h.dg2
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b2]
  have dg_3_0 : c13 = 0 → c23 = 0 → c34 = 0 → False := by
    intro z1 z2 z3
    have hij : c03 = 0 := by
      have hx : b0 * c03 = 0 := by linear_combination h.st3 - (b1 : ℂ) * z1 - (b2 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p0
      · exact y
    have hd := h.dg3
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b3]
  have dg_3_1 : c03 = 0 → c23 = 0 → c34 = 0 → False := by
    intro z1 z2 z3
    have hij : c13 = 0 := by
      have hx : b1 * c13 = 0 := by linear_combination h.st3 - (b0 : ℂ) * z1 - (b2 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p1
      · exact y
    have hd := h.dg3
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b3]
  have dg_3_2 : c03 = 0 → c13 = 0 → c34 = 0 → False := by
    intro z1 z2 z3
    have hij : c23 = 0 := by
      have hx : b2 * c23 = 0 := by linear_combination h.st3 - (b0 : ℂ) * z1 - (b1 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p2
      · exact y
    have hd := h.dg3
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b3]
  have dg_3_4 : c03 = 0 → c13 = 0 → c23 = 0 → False := by
    intro z1 z2 z3
    have hij : c34 = 0 := by
      have hx : b4 * c34 = 0 := by linear_combination h.st3 - (b0 : ℂ) * z1 - (b1 : ℂ) * z2 - (b2 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p4
      · exact y
    have hd := h.dg3
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b3]
  have dg_4_0 : c14 = 0 → c24 = 0 → c34 = 0 → False := by
    intro z1 z2 z3
    have hij : c04 = 0 := by
      have hx : b0 * c04 = 0 := by linear_combination h.st4 - (b1 : ℂ) * z1 - (b2 : ℂ) * z2 - (b3 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p0
      · exact y
    have hd := h.dg4
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b4]
  have dg_4_1 : c04 = 0 → c24 = 0 → c34 = 0 → False := by
    intro z1 z2 z3
    have hij : c14 = 0 := by
      have hx : b1 * c14 = 0 := by linear_combination h.st4 - (b0 : ℂ) * z1 - (b2 : ℂ) * z2 - (b3 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p1
      · exact y
    have hd := h.dg4
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b4]
  have dg_4_2 : c04 = 0 → c14 = 0 → c34 = 0 → False := by
    intro z1 z2 z3
    have hij : c24 = 0 := by
      have hx : b2 * c24 = 0 := by linear_combination h.st4 - (b0 : ℂ) * z1 - (b1 : ℂ) * z2 - (b3 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p2
      · exact y
    have hd := h.dg4
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b4]
  have dg_4_3 : c04 = 0 → c14 = 0 → c24 = 0 → False := by
    intro z1 z2 z3
    have hd1 := h.dg4
    have hd2 := h.dg3
    rw [z1, z2, z3, Complex.normSq_zero] at hd1
    rw [p3, Complex.normSq_zero] at hd2
    have hz : Complex.normSq b4 = 0 := by linarith only [hd1, hd2, Complex.normSq_nonneg b4, Complex.normSq_nonneg c03, Complex.normSq_nonneg c13, Complex.normSq_nonneg c23]
    exact p4 (Complex.normSq_eq_zero.mp hz)
  obtain ⟨d01, d02, d03, d04, d12, d13, d14, d23, d24, d34⟩ := dets0 h.st0 h.st1 h.st2 h.st3 h.st4 haf0 haf1 haf2 haf3 haf4 p0
  exact graph haf0 haf1 haf2 haf3 haf4 dg_0_1 dg_0_2 dg_0_3 dg_0_4 dg_1_0 dg_1_2 dg_1_3 dg_1_4 dg_2_0 dg_2_1 dg_2_3 dg_2_4 dg_3_0 dg_3_1 dg_3_2 dg_3_4 dg_4_0 dg_4_1 dg_4_2 dg_4_3 d01 d02 d03 d04 d12 d13 d14 d23 d24 d34

/-- The branch in which exactly the point amplitudes b3, b4 are nonzero. -/
theorem case24 {s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34 : ℂ} (h : Sys s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34)
    (p0 : b0 = 0) (p1 : b1 = 0) (p2 : b2 = 0) (_p3 : b3 ≠ 0) (p4 : b4 ≠ 0) : False := by
  have hab : c34 = 0 := by
    have hx : b4 * c34 = 0 := by linear_combination h.st3 - (c03 : ℂ) * p0 - (c13 : ℂ) * p1 - (c23 : ℂ) * p2
    rcases mul_eq_zero.mp hx with y | y
    · exact absurd y p4
    · exact y
  have hd1 := h.dg3
  have hd2 := h.dg4
  have ht := h.tb
  have hc := h.tc
  rw [hab, Complex.normSq_zero] at hd1 hd2 hc
  rw [p0, p1, p2, Complex.normSq_zero] at ht
  linarith only [hd1, hd2, ht, hc, Complex.normSq_nonneg b0, Complex.normSq_nonneg b1, Complex.normSq_nonneg b2, Complex.normSq_nonneg b3, Complex.normSq_nonneg b4, Complex.normSq_nonneg c01, Complex.normSq_nonneg c02, Complex.normSq_nonneg c03, Complex.normSq_nonneg c04, Complex.normSq_nonneg c12, Complex.normSq_nonneg c13, Complex.normSq_nonneg c14, Complex.normSq_nonneg c23, Complex.normSq_nonneg c24, Complex.normSq_nonneg c34]

/-- The branch in which exactly the point amplitudes b0, b3, b4 are nonzero. -/
theorem case25 {s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34 : ℂ} (h : Sys s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34)
    (p0 : b0 ≠ 0) (p1 : b1 = 0) (p2 : b2 = 0) (p3 : b3 ≠ 0) (p4 : b4 ≠ 0) : False := by
  have hd1 := h.dg0
  have hd2 := h.dg3
  have hd3 := h.dg4
  have ht := h.tb
  have hc := h.tc
  rw [p1, p2, Complex.normSq_zero] at ht
  have hW : (0:Real) < Complex.normSq c03 + Complex.normSq c04 + Complex.normSq c34 := by
    linarith only [hd1, hd2, hd3, ht, hc, Complex.normSq_nonneg b0, Complex.normSq_nonneg b1, Complex.normSq_nonneg b2, Complex.normSq_nonneg b3, Complex.normSq_nonneg b4, Complex.normSq_nonneg c01, Complex.normSq_nonneg c02, Complex.normSq_nonneg c03, Complex.normSq_nonneg c04, Complex.normSq_nonneg c12, Complex.normSq_nonneg c13, Complex.normSq_nonneg c14, Complex.normSq_nonneg c23, Complex.normSq_nonneg c24, Complex.normSq_nonneg c34]
  have sa : b3 * c03 + b4 * c04 = 0 := by linear_combination h.st0 - (c01 : ℂ) * p1 - (c02 : ℂ) * p2
  have sb : b0 * c03 + b4 * c34 = 0 := by linear_combination h.st3 - (c13 : ℂ) * p1 - (c23 : ℂ) * p2
  have sc : b0 * c04 + b3 * c34 = 0 := by linear_combination h.st4 - (c14 : ℂ) * p1 - (c24 : ℂ) * p2
  have kk := SixQubit.Triangle.prod_eq_zero sc sb sa
  have z1 : c34 = 0 ∨ c04 = 0 := by
    rcases mul_eq_zero.mp kk with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · exact absurd y2 p4
      · exact Or.inl y2
    · exact Or.inr y
  have zz : c03 = 0 ∧ c04 = 0 ∧ c34 = 0 := by
    rcases z1 with y | y
    · have h1 : c03 = 0 := by
        have hx : b0 * c03 = 0 := by linear_combination sb - (b4 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p0
        · exact w
      have h2 : c04 = 0 := by
        have hx : b0 * c04 = 0 := by linear_combination sc - (b3 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p0
        · exact w
      exact ⟨h1, h2, y⟩
    · have h1 : c03 = 0 := by
        have hx : b3 * c03 = 0 := by linear_combination sa - (b4 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p3
        · exact w
      have h2 : c34 = 0 := by
        have hx : b3 * c34 = 0 := by linear_combination sc - (b0 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p3
        · exact w
      exact ⟨h1, y, h2⟩
  obtain ⟨u1, u2, u3⟩ := zz
  rw [u1, u2, u3, Complex.normSq_zero] at hW
  norm_num at hW

/-- The branch in which exactly the point amplitudes b1, b3, b4 are nonzero. -/
theorem case26 {s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34 : ℂ} (h : Sys s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34)
    (p0 : b0 = 0) (p1 : b1 ≠ 0) (p2 : b2 = 0) (p3 : b3 ≠ 0) (p4 : b4 ≠ 0) : False := by
  have hd1 := h.dg1
  have hd2 := h.dg3
  have hd3 := h.dg4
  have ht := h.tb
  have hc := h.tc
  rw [p0, p2, Complex.normSq_zero] at ht
  have hW : (0:Real) < Complex.normSq c13 + Complex.normSq c14 + Complex.normSq c34 := by
    linarith only [hd1, hd2, hd3, ht, hc, Complex.normSq_nonneg b0, Complex.normSq_nonneg b1, Complex.normSq_nonneg b2, Complex.normSq_nonneg b3, Complex.normSq_nonneg b4, Complex.normSq_nonneg c01, Complex.normSq_nonneg c02, Complex.normSq_nonneg c03, Complex.normSq_nonneg c04, Complex.normSq_nonneg c12, Complex.normSq_nonneg c13, Complex.normSq_nonneg c14, Complex.normSq_nonneg c23, Complex.normSq_nonneg c24, Complex.normSq_nonneg c34]
  have sa : b3 * c13 + b4 * c14 = 0 := by linear_combination h.st1 - (c01 : ℂ) * p0 - (c12 : ℂ) * p2
  have sb : b1 * c13 + b4 * c34 = 0 := by linear_combination h.st3 - (c03 : ℂ) * p0 - (c23 : ℂ) * p2
  have sc : b1 * c14 + b3 * c34 = 0 := by linear_combination h.st4 - (c04 : ℂ) * p0 - (c24 : ℂ) * p2
  have kk := SixQubit.Triangle.prod_eq_zero sc sb sa
  have z1 : c34 = 0 ∨ c14 = 0 := by
    rcases mul_eq_zero.mp kk with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · exact absurd y2 p4
      · exact Or.inl y2
    · exact Or.inr y
  have zz : c13 = 0 ∧ c14 = 0 ∧ c34 = 0 := by
    rcases z1 with y | y
    · have h1 : c13 = 0 := by
        have hx : b1 * c13 = 0 := by linear_combination sb - (b4 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p1
        · exact w
      have h2 : c14 = 0 := by
        have hx : b1 * c14 = 0 := by linear_combination sc - (b3 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p1
        · exact w
      exact ⟨h1, h2, y⟩
    · have h1 : c13 = 0 := by
        have hx : b3 * c13 = 0 := by linear_combination sa - (b4 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p3
        · exact w
      have h2 : c34 = 0 := by
        have hx : b3 * c34 = 0 := by linear_combination sc - (b1 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p3
        · exact w
      exact ⟨h1, y, h2⟩
  obtain ⟨u1, u2, u3⟩ := zz
  rw [u1, u2, u3, Complex.normSq_zero] at hW
  norm_num at hW

/-- The branch in which exactly the point amplitudes b0, b1, b3, b4 are nonzero. -/
theorem case27 {s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34 : ℂ} (h : Sys s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34)
    (p0 : b0 ≠ 0) (p1 : b1 ≠ 0) (p2 : b2 = 0) (p3 : b3 ≠ 0) (p4 : b4 ≠ 0) : False := by
  have kk01 : k01 = 0 := by
    rcases mul_eq_zero.mp h.kb01_0 with y | y
    · exact absurd y p0
    · exact y
  have kk02 : k02 = 0 := by
    rcases mul_eq_zero.mp h.kb02_0 with y | y
    · exact absurd y p0
    · exact y
  have kk03 : k03 = 0 := by
    rcases mul_eq_zero.mp h.kb03_0 with y | y
    · exact absurd y p0
    · exact y
  have kk04 : k04 = 0 := by
    rcases mul_eq_zero.mp h.kb04_0 with y | y
    · exact absurd y p0
    · exact y
  have kk12 : k12 = 0 := by
    rcases mul_eq_zero.mp h.kb12_1 with y | y
    · exact absurd y p1
    · exact y
  have kk13 : k13 = 0 := by
    rcases mul_eq_zero.mp h.kb13_1 with y | y
    · exact absurd y p1
    · exact y
  have kk14 : k14 = 0 := by
    rcases mul_eq_zero.mp h.kb14_1 with y | y
    · exact absurd y p1
    · exact y
  have kk23 : k23 = 0 := by
    rcases mul_eq_zero.mp h.kb23_3 with y | y
    · exact absurd y p3
    · exact y
  have kk24 : k24 = 0 := by
    rcases mul_eq_zero.mp h.kb24_4 with y | y
    · exact absurd y p4
    · exact y
  have kk34 : k34 = 0 := by
    rcases mul_eq_zero.mp h.kb34_3 with y | y
    · exact absurd y p3
    · exact y
  have haf0 : c12 * c34 + c13 * c24 + c14 * c23 = 0 := by
    have hx : (2 : ℂ) * s * (c12 * c34 + c13 * c24 + c14 * c23) = 0 := by
      linear_combination (-1 : ℂ) * h.hf0 + (c12 : ℂ) * kk34 + (c34 : ℂ) * kk12 + (c13 : ℂ) * kk24 + (c24 : ℂ) * kk13 + (c14 : ℂ) * kk23 + (c23 : ℂ) * kk14
    rcases mul_eq_zero.mp hx with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · norm_num at y2
      · exact absurd y2 h.hs
    · exact y
  have haf1 : c02 * c34 + c03 * c24 + c04 * c23 = 0 := by
    have hx : (2 : ℂ) * s * (c02 * c34 + c03 * c24 + c04 * c23) = 0 := by
      linear_combination (-1 : ℂ) * h.hf1 + (c02 : ℂ) * kk34 + (c34 : ℂ) * kk02 + (c03 : ℂ) * kk24 + (c24 : ℂ) * kk03 + (c04 : ℂ) * kk23 + (c23 : ℂ) * kk04
    rcases mul_eq_zero.mp hx with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · norm_num at y2
      · exact absurd y2 h.hs
    · exact y
  have haf2 : c01 * c34 + c03 * c14 + c04 * c13 = 0 := by
    have hx : (2 : ℂ) * s * (c01 * c34 + c03 * c14 + c04 * c13) = 0 := by
      linear_combination (-1 : ℂ) * h.hf2 + (c01 : ℂ) * kk34 + (c34 : ℂ) * kk01 + (c03 : ℂ) * kk14 + (c14 : ℂ) * kk03 + (c04 : ℂ) * kk13 + (c13 : ℂ) * kk04
    rcases mul_eq_zero.mp hx with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · norm_num at y2
      · exact absurd y2 h.hs
    · exact y
  have haf3 : c01 * c24 + c02 * c14 + c04 * c12 = 0 := by
    have hx : (2 : ℂ) * s * (c01 * c24 + c02 * c14 + c04 * c12) = 0 := by
      linear_combination (-1 : ℂ) * h.hf3 + (c01 : ℂ) * kk24 + (c24 : ℂ) * kk01 + (c02 : ℂ) * kk14 + (c14 : ℂ) * kk02 + (c04 : ℂ) * kk12 + (c12 : ℂ) * kk04
    rcases mul_eq_zero.mp hx with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · norm_num at y2
      · exact absurd y2 h.hs
    · exact y
  have haf4 : c01 * c23 + c02 * c13 + c03 * c12 = 0 := by
    have hx : (2 : ℂ) * s * (c01 * c23 + c02 * c13 + c03 * c12) = 0 := by
      linear_combination (-1 : ℂ) * h.hf4 + (c01 : ℂ) * kk23 + (c23 : ℂ) * kk01 + (c02 : ℂ) * kk13 + (c13 : ℂ) * kk02 + (c03 : ℂ) * kk12 + (c12 : ℂ) * kk03
    rcases mul_eq_zero.mp hx with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · norm_num at y2
      · exact absurd y2 h.hs
    · exact y
  have dg_0_1 : c02 = 0 → c03 = 0 → c04 = 0 → False := by
    intro z1 z2 z3
    have hij : c01 = 0 := by
      have hx : b1 * c01 = 0 := by linear_combination h.st0 - (b2 : ℂ) * z1 - (b3 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p1
      · exact y
    have hd := h.dg0
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b0]
  have dg_0_2 : c01 = 0 → c03 = 0 → c04 = 0 → False := by
    intro z1 z2 z3
    have hd1 := h.dg0
    have hd2 := h.dg2
    rw [z1, z2, z3, Complex.normSq_zero] at hd1
    rw [p2, Complex.normSq_zero] at hd2
    have hz : Complex.normSq b0 = 0 := by linarith only [hd1, hd2, Complex.normSq_nonneg b0, Complex.normSq_nonneg c12, Complex.normSq_nonneg c23, Complex.normSq_nonneg c24]
    exact p0 (Complex.normSq_eq_zero.mp hz)
  have dg_0_3 : c01 = 0 → c02 = 0 → c04 = 0 → False := by
    intro z1 z2 z3
    have hij : c03 = 0 := by
      have hx : b3 * c03 = 0 := by linear_combination h.st0 - (b1 : ℂ) * z1 - (b2 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p3
      · exact y
    have hd := h.dg0
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b0]
  have dg_0_4 : c01 = 0 → c02 = 0 → c03 = 0 → False := by
    intro z1 z2 z3
    have hij : c04 = 0 := by
      have hx : b4 * c04 = 0 := by linear_combination h.st0 - (b1 : ℂ) * z1 - (b2 : ℂ) * z2 - (b3 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p4
      · exact y
    have hd := h.dg0
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b0]
  have dg_1_0 : c12 = 0 → c13 = 0 → c14 = 0 → False := by
    intro z1 z2 z3
    have hij : c01 = 0 := by
      have hx : b0 * c01 = 0 := by linear_combination h.st1 - (b2 : ℂ) * z1 - (b3 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p0
      · exact y
    have hd := h.dg1
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b1]
  have dg_1_2 : c01 = 0 → c13 = 0 → c14 = 0 → False := by
    intro z1 z2 z3
    have hd1 := h.dg1
    have hd2 := h.dg2
    rw [z1, z2, z3, Complex.normSq_zero] at hd1
    rw [p2, Complex.normSq_zero] at hd2
    have hz : Complex.normSq b1 = 0 := by linarith only [hd1, hd2, Complex.normSq_nonneg b1, Complex.normSq_nonneg c02, Complex.normSq_nonneg c23, Complex.normSq_nonneg c24]
    exact p1 (Complex.normSq_eq_zero.mp hz)
  have dg_1_3 : c01 = 0 → c12 = 0 → c14 = 0 → False := by
    intro z1 z2 z3
    have hij : c13 = 0 := by
      have hx : b3 * c13 = 0 := by linear_combination h.st1 - (b0 : ℂ) * z1 - (b2 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p3
      · exact y
    have hd := h.dg1
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b1]
  have dg_1_4 : c01 = 0 → c12 = 0 → c13 = 0 → False := by
    intro z1 z2 z3
    have hij : c14 = 0 := by
      have hx : b4 * c14 = 0 := by linear_combination h.st1 - (b0 : ℂ) * z1 - (b2 : ℂ) * z2 - (b3 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p4
      · exact y
    have hd := h.dg1
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b1]
  have dg_2_0 : c12 = 0 → c23 = 0 → c24 = 0 → False := by
    intro z1 z2 z3
    have hij : c02 = 0 := by
      have hx : b0 * c02 = 0 := by linear_combination h.st2 - (b1 : ℂ) * z1 - (b3 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p0
      · exact y
    have hd := h.dg2
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b2]
  have dg_2_1 : c02 = 0 → c23 = 0 → c24 = 0 → False := by
    intro z1 z2 z3
    have hij : c12 = 0 := by
      have hx : b1 * c12 = 0 := by linear_combination h.st2 - (b0 : ℂ) * z1 - (b3 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p1
      · exact y
    have hd := h.dg2
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b2]
  have dg_2_3 : c02 = 0 → c12 = 0 → c24 = 0 → False := by
    intro z1 z2 z3
    have hij : c23 = 0 := by
      have hx : b3 * c23 = 0 := by linear_combination h.st2 - (b0 : ℂ) * z1 - (b1 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p3
      · exact y
    have hd := h.dg2
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b2]
  have dg_2_4 : c02 = 0 → c12 = 0 → c23 = 0 → False := by
    intro z1 z2 z3
    have hij : c24 = 0 := by
      have hx : b4 * c24 = 0 := by linear_combination h.st2 - (b0 : ℂ) * z1 - (b1 : ℂ) * z2 - (b3 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p4
      · exact y
    have hd := h.dg2
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b2]
  have dg_3_0 : c13 = 0 → c23 = 0 → c34 = 0 → False := by
    intro z1 z2 z3
    have hij : c03 = 0 := by
      have hx : b0 * c03 = 0 := by linear_combination h.st3 - (b1 : ℂ) * z1 - (b2 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p0
      · exact y
    have hd := h.dg3
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b3]
  have dg_3_1 : c03 = 0 → c23 = 0 → c34 = 0 → False := by
    intro z1 z2 z3
    have hij : c13 = 0 := by
      have hx : b1 * c13 = 0 := by linear_combination h.st3 - (b0 : ℂ) * z1 - (b2 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p1
      · exact y
    have hd := h.dg3
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b3]
  have dg_3_2 : c03 = 0 → c13 = 0 → c34 = 0 → False := by
    intro z1 z2 z3
    have hd1 := h.dg3
    have hd2 := h.dg2
    rw [z1, z2, z3, Complex.normSq_zero] at hd1
    rw [p2, Complex.normSq_zero] at hd2
    have hz : Complex.normSq b3 = 0 := by linarith only [hd1, hd2, Complex.normSq_nonneg b3, Complex.normSq_nonneg c02, Complex.normSq_nonneg c12, Complex.normSq_nonneg c24]
    exact p3 (Complex.normSq_eq_zero.mp hz)
  have dg_3_4 : c03 = 0 → c13 = 0 → c23 = 0 → False := by
    intro z1 z2 z3
    have hij : c34 = 0 := by
      have hx : b4 * c34 = 0 := by linear_combination h.st3 - (b0 : ℂ) * z1 - (b1 : ℂ) * z2 - (b2 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p4
      · exact y
    have hd := h.dg3
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b3]
  have dg_4_0 : c14 = 0 → c24 = 0 → c34 = 0 → False := by
    intro z1 z2 z3
    have hij : c04 = 0 := by
      have hx : b0 * c04 = 0 := by linear_combination h.st4 - (b1 : ℂ) * z1 - (b2 : ℂ) * z2 - (b3 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p0
      · exact y
    have hd := h.dg4
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b4]
  have dg_4_1 : c04 = 0 → c24 = 0 → c34 = 0 → False := by
    intro z1 z2 z3
    have hij : c14 = 0 := by
      have hx : b1 * c14 = 0 := by linear_combination h.st4 - (b0 : ℂ) * z1 - (b2 : ℂ) * z2 - (b3 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p1
      · exact y
    have hd := h.dg4
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b4]
  have dg_4_2 : c04 = 0 → c14 = 0 → c34 = 0 → False := by
    intro z1 z2 z3
    have hd1 := h.dg4
    have hd2 := h.dg2
    rw [z1, z2, z3, Complex.normSq_zero] at hd1
    rw [p2, Complex.normSq_zero] at hd2
    have hz : Complex.normSq b4 = 0 := by linarith only [hd1, hd2, Complex.normSq_nonneg b4, Complex.normSq_nonneg c02, Complex.normSq_nonneg c12, Complex.normSq_nonneg c23]
    exact p4 (Complex.normSq_eq_zero.mp hz)
  have dg_4_3 : c04 = 0 → c14 = 0 → c24 = 0 → False := by
    intro z1 z2 z3
    have hij : c34 = 0 := by
      have hx : b3 * c34 = 0 := by linear_combination h.st4 - (b0 : ℂ) * z1 - (b1 : ℂ) * z2 - (b2 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p3
      · exact y
    have hd := h.dg4
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b4]
  obtain ⟨d01, d02, d03, d04, d12, d13, d14, d23, d24, d34⟩ := dets0 h.st0 h.st1 h.st2 h.st3 h.st4 haf0 haf1 haf2 haf3 haf4 p0
  exact graph haf0 haf1 haf2 haf3 haf4 dg_0_1 dg_0_2 dg_0_3 dg_0_4 dg_1_0 dg_1_2 dg_1_3 dg_1_4 dg_2_0 dg_2_1 dg_2_3 dg_2_4 dg_3_0 dg_3_1 dg_3_2 dg_3_4 dg_4_0 dg_4_1 dg_4_2 dg_4_3 d01 d02 d03 d04 d12 d13 d14 d23 d24 d34

/-- The branch in which exactly the point amplitudes b2, b3, b4 are nonzero. -/
theorem case28 {s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34 : ℂ} (h : Sys s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34)
    (p0 : b0 = 0) (p1 : b1 = 0) (p2 : b2 ≠ 0) (p3 : b3 ≠ 0) (p4 : b4 ≠ 0) : False := by
  have hd1 := h.dg2
  have hd2 := h.dg3
  have hd3 := h.dg4
  have ht := h.tb
  have hc := h.tc
  rw [p0, p1, Complex.normSq_zero] at ht
  have hW : (0:Real) < Complex.normSq c23 + Complex.normSq c24 + Complex.normSq c34 := by
    linarith only [hd1, hd2, hd3, ht, hc, Complex.normSq_nonneg b0, Complex.normSq_nonneg b1, Complex.normSq_nonneg b2, Complex.normSq_nonneg b3, Complex.normSq_nonneg b4, Complex.normSq_nonneg c01, Complex.normSq_nonneg c02, Complex.normSq_nonneg c03, Complex.normSq_nonneg c04, Complex.normSq_nonneg c12, Complex.normSq_nonneg c13, Complex.normSq_nonneg c14, Complex.normSq_nonneg c23, Complex.normSq_nonneg c24, Complex.normSq_nonneg c34]
  have sa : b3 * c23 + b4 * c24 = 0 := by linear_combination h.st2 - (c02 : ℂ) * p0 - (c12 : ℂ) * p1
  have sb : b2 * c23 + b4 * c34 = 0 := by linear_combination h.st3 - (c03 : ℂ) * p0 - (c13 : ℂ) * p1
  have sc : b2 * c24 + b3 * c34 = 0 := by linear_combination h.st4 - (c04 : ℂ) * p0 - (c14 : ℂ) * p1
  have kk := SixQubit.Triangle.prod_eq_zero sc sb sa
  have z1 : c34 = 0 ∨ c24 = 0 := by
    rcases mul_eq_zero.mp kk with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · exact absurd y2 p4
      · exact Or.inl y2
    · exact Or.inr y
  have zz : c23 = 0 ∧ c24 = 0 ∧ c34 = 0 := by
    rcases z1 with y | y
    · have h1 : c23 = 0 := by
        have hx : b2 * c23 = 0 := by linear_combination sb - (b4 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p2
        · exact w
      have h2 : c24 = 0 := by
        have hx : b2 * c24 = 0 := by linear_combination sc - (b3 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p2
        · exact w
      exact ⟨h1, h2, y⟩
    · have h1 : c23 = 0 := by
        have hx : b3 * c23 = 0 := by linear_combination sa - (b4 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p3
        · exact w
      have h2 : c34 = 0 := by
        have hx : b3 * c34 = 0 := by linear_combination sc - (b2 : ℂ) * y
        rcases mul_eq_zero.mp hx with w | w
        · exact absurd w p3
        · exact w
      exact ⟨h1, y, h2⟩
  obtain ⟨u1, u2, u3⟩ := zz
  rw [u1, u2, u3, Complex.normSq_zero] at hW
  norm_num at hW

/-- The branch in which exactly the point amplitudes b0, b2, b3, b4 are nonzero. -/
theorem case29 {s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34 : ℂ} (h : Sys s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34)
    (p0 : b0 ≠ 0) (p1 : b1 = 0) (p2 : b2 ≠ 0) (p3 : b3 ≠ 0) (p4 : b4 ≠ 0) : False := by
  have kk01 : k01 = 0 := by
    rcases mul_eq_zero.mp h.kb01_0 with y | y
    · exact absurd y p0
    · exact y
  have kk02 : k02 = 0 := by
    rcases mul_eq_zero.mp h.kb02_0 with y | y
    · exact absurd y p0
    · exact y
  have kk03 : k03 = 0 := by
    rcases mul_eq_zero.mp h.kb03_0 with y | y
    · exact absurd y p0
    · exact y
  have kk04 : k04 = 0 := by
    rcases mul_eq_zero.mp h.kb04_0 with y | y
    · exact absurd y p0
    · exact y
  have kk12 : k12 = 0 := by
    rcases mul_eq_zero.mp h.kb12_2 with y | y
    · exact absurd y p2
    · exact y
  have kk13 : k13 = 0 := by
    rcases mul_eq_zero.mp h.kb13_3 with y | y
    · exact absurd y p3
    · exact y
  have kk14 : k14 = 0 := by
    rcases mul_eq_zero.mp h.kb14_4 with y | y
    · exact absurd y p4
    · exact y
  have kk23 : k23 = 0 := by
    rcases mul_eq_zero.mp h.kb23_2 with y | y
    · exact absurd y p2
    · exact y
  have kk24 : k24 = 0 := by
    rcases mul_eq_zero.mp h.kb24_2 with y | y
    · exact absurd y p2
    · exact y
  have kk34 : k34 = 0 := by
    rcases mul_eq_zero.mp h.kb34_3 with y | y
    · exact absurd y p3
    · exact y
  have haf0 : c12 * c34 + c13 * c24 + c14 * c23 = 0 := by
    have hx : (2 : ℂ) * s * (c12 * c34 + c13 * c24 + c14 * c23) = 0 := by
      linear_combination (-1 : ℂ) * h.hf0 + (c12 : ℂ) * kk34 + (c34 : ℂ) * kk12 + (c13 : ℂ) * kk24 + (c24 : ℂ) * kk13 + (c14 : ℂ) * kk23 + (c23 : ℂ) * kk14
    rcases mul_eq_zero.mp hx with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · norm_num at y2
      · exact absurd y2 h.hs
    · exact y
  have haf1 : c02 * c34 + c03 * c24 + c04 * c23 = 0 := by
    have hx : (2 : ℂ) * s * (c02 * c34 + c03 * c24 + c04 * c23) = 0 := by
      linear_combination (-1 : ℂ) * h.hf1 + (c02 : ℂ) * kk34 + (c34 : ℂ) * kk02 + (c03 : ℂ) * kk24 + (c24 : ℂ) * kk03 + (c04 : ℂ) * kk23 + (c23 : ℂ) * kk04
    rcases mul_eq_zero.mp hx with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · norm_num at y2
      · exact absurd y2 h.hs
    · exact y
  have haf2 : c01 * c34 + c03 * c14 + c04 * c13 = 0 := by
    have hx : (2 : ℂ) * s * (c01 * c34 + c03 * c14 + c04 * c13) = 0 := by
      linear_combination (-1 : ℂ) * h.hf2 + (c01 : ℂ) * kk34 + (c34 : ℂ) * kk01 + (c03 : ℂ) * kk14 + (c14 : ℂ) * kk03 + (c04 : ℂ) * kk13 + (c13 : ℂ) * kk04
    rcases mul_eq_zero.mp hx with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · norm_num at y2
      · exact absurd y2 h.hs
    · exact y
  have haf3 : c01 * c24 + c02 * c14 + c04 * c12 = 0 := by
    have hx : (2 : ℂ) * s * (c01 * c24 + c02 * c14 + c04 * c12) = 0 := by
      linear_combination (-1 : ℂ) * h.hf3 + (c01 : ℂ) * kk24 + (c24 : ℂ) * kk01 + (c02 : ℂ) * kk14 + (c14 : ℂ) * kk02 + (c04 : ℂ) * kk12 + (c12 : ℂ) * kk04
    rcases mul_eq_zero.mp hx with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · norm_num at y2
      · exact absurd y2 h.hs
    · exact y
  have haf4 : c01 * c23 + c02 * c13 + c03 * c12 = 0 := by
    have hx : (2 : ℂ) * s * (c01 * c23 + c02 * c13 + c03 * c12) = 0 := by
      linear_combination (-1 : ℂ) * h.hf4 + (c01 : ℂ) * kk23 + (c23 : ℂ) * kk01 + (c02 : ℂ) * kk13 + (c13 : ℂ) * kk02 + (c03 : ℂ) * kk12 + (c12 : ℂ) * kk03
    rcases mul_eq_zero.mp hx with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · norm_num at y2
      · exact absurd y2 h.hs
    · exact y
  have dg_0_1 : c02 = 0 → c03 = 0 → c04 = 0 → False := by
    intro z1 z2 z3
    have hd1 := h.dg0
    have hd2 := h.dg1
    rw [z1, z2, z3, Complex.normSq_zero] at hd1
    rw [p1, Complex.normSq_zero] at hd2
    have hz : Complex.normSq b0 = 0 := by linarith only [hd1, hd2, Complex.normSq_nonneg b0, Complex.normSq_nonneg c12, Complex.normSq_nonneg c13, Complex.normSq_nonneg c14]
    exact p0 (Complex.normSq_eq_zero.mp hz)
  have dg_0_2 : c01 = 0 → c03 = 0 → c04 = 0 → False := by
    intro z1 z2 z3
    have hij : c02 = 0 := by
      have hx : b2 * c02 = 0 := by linear_combination h.st0 - (b1 : ℂ) * z1 - (b3 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p2
      · exact y
    have hd := h.dg0
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b0]
  have dg_0_3 : c01 = 0 → c02 = 0 → c04 = 0 → False := by
    intro z1 z2 z3
    have hij : c03 = 0 := by
      have hx : b3 * c03 = 0 := by linear_combination h.st0 - (b1 : ℂ) * z1 - (b2 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p3
      · exact y
    have hd := h.dg0
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b0]
  have dg_0_4 : c01 = 0 → c02 = 0 → c03 = 0 → False := by
    intro z1 z2 z3
    have hij : c04 = 0 := by
      have hx : b4 * c04 = 0 := by linear_combination h.st0 - (b1 : ℂ) * z1 - (b2 : ℂ) * z2 - (b3 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p4
      · exact y
    have hd := h.dg0
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b0]
  have dg_1_0 : c12 = 0 → c13 = 0 → c14 = 0 → False := by
    intro z1 z2 z3
    have hij : c01 = 0 := by
      have hx : b0 * c01 = 0 := by linear_combination h.st1 - (b2 : ℂ) * z1 - (b3 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p0
      · exact y
    have hd := h.dg1
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b1]
  have dg_1_2 : c01 = 0 → c13 = 0 → c14 = 0 → False := by
    intro z1 z2 z3
    have hij : c12 = 0 := by
      have hx : b2 * c12 = 0 := by linear_combination h.st1 - (b0 : ℂ) * z1 - (b3 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p2
      · exact y
    have hd := h.dg1
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b1]
  have dg_1_3 : c01 = 0 → c12 = 0 → c14 = 0 → False := by
    intro z1 z2 z3
    have hij : c13 = 0 := by
      have hx : b3 * c13 = 0 := by linear_combination h.st1 - (b0 : ℂ) * z1 - (b2 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p3
      · exact y
    have hd := h.dg1
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b1]
  have dg_1_4 : c01 = 0 → c12 = 0 → c13 = 0 → False := by
    intro z1 z2 z3
    have hij : c14 = 0 := by
      have hx : b4 * c14 = 0 := by linear_combination h.st1 - (b0 : ℂ) * z1 - (b2 : ℂ) * z2 - (b3 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p4
      · exact y
    have hd := h.dg1
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b1]
  have dg_2_0 : c12 = 0 → c23 = 0 → c24 = 0 → False := by
    intro z1 z2 z3
    have hij : c02 = 0 := by
      have hx : b0 * c02 = 0 := by linear_combination h.st2 - (b1 : ℂ) * z1 - (b3 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p0
      · exact y
    have hd := h.dg2
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b2]
  have dg_2_1 : c02 = 0 → c23 = 0 → c24 = 0 → False := by
    intro z1 z2 z3
    have hd1 := h.dg2
    have hd2 := h.dg1
    rw [z1, z2, z3, Complex.normSq_zero] at hd1
    rw [p1, Complex.normSq_zero] at hd2
    have hz : Complex.normSq b2 = 0 := by linarith only [hd1, hd2, Complex.normSq_nonneg b2, Complex.normSq_nonneg c01, Complex.normSq_nonneg c13, Complex.normSq_nonneg c14]
    exact p2 (Complex.normSq_eq_zero.mp hz)
  have dg_2_3 : c02 = 0 → c12 = 0 → c24 = 0 → False := by
    intro z1 z2 z3
    have hij : c23 = 0 := by
      have hx : b3 * c23 = 0 := by linear_combination h.st2 - (b0 : ℂ) * z1 - (b1 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p3
      · exact y
    have hd := h.dg2
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b2]
  have dg_2_4 : c02 = 0 → c12 = 0 → c23 = 0 → False := by
    intro z1 z2 z3
    have hij : c24 = 0 := by
      have hx : b4 * c24 = 0 := by linear_combination h.st2 - (b0 : ℂ) * z1 - (b1 : ℂ) * z2 - (b3 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p4
      · exact y
    have hd := h.dg2
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b2]
  have dg_3_0 : c13 = 0 → c23 = 0 → c34 = 0 → False := by
    intro z1 z2 z3
    have hij : c03 = 0 := by
      have hx : b0 * c03 = 0 := by linear_combination h.st3 - (b1 : ℂ) * z1 - (b2 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p0
      · exact y
    have hd := h.dg3
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b3]
  have dg_3_1 : c03 = 0 → c23 = 0 → c34 = 0 → False := by
    intro z1 z2 z3
    have hd1 := h.dg3
    have hd2 := h.dg1
    rw [z1, z2, z3, Complex.normSq_zero] at hd1
    rw [p1, Complex.normSq_zero] at hd2
    have hz : Complex.normSq b3 = 0 := by linarith only [hd1, hd2, Complex.normSq_nonneg b3, Complex.normSq_nonneg c01, Complex.normSq_nonneg c12, Complex.normSq_nonneg c14]
    exact p3 (Complex.normSq_eq_zero.mp hz)
  have dg_3_2 : c03 = 0 → c13 = 0 → c34 = 0 → False := by
    intro z1 z2 z3
    have hij : c23 = 0 := by
      have hx : b2 * c23 = 0 := by linear_combination h.st3 - (b0 : ℂ) * z1 - (b1 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p2
      · exact y
    have hd := h.dg3
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b3]
  have dg_3_4 : c03 = 0 → c13 = 0 → c23 = 0 → False := by
    intro z1 z2 z3
    have hij : c34 = 0 := by
      have hx : b4 * c34 = 0 := by linear_combination h.st3 - (b0 : ℂ) * z1 - (b1 : ℂ) * z2 - (b2 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p4
      · exact y
    have hd := h.dg3
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b3]
  have dg_4_0 : c14 = 0 → c24 = 0 → c34 = 0 → False := by
    intro z1 z2 z3
    have hij : c04 = 0 := by
      have hx : b0 * c04 = 0 := by linear_combination h.st4 - (b1 : ℂ) * z1 - (b2 : ℂ) * z2 - (b3 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p0
      · exact y
    have hd := h.dg4
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b4]
  have dg_4_1 : c04 = 0 → c24 = 0 → c34 = 0 → False := by
    intro z1 z2 z3
    have hd1 := h.dg4
    have hd2 := h.dg1
    rw [z1, z2, z3, Complex.normSq_zero] at hd1
    rw [p1, Complex.normSq_zero] at hd2
    have hz : Complex.normSq b4 = 0 := by linarith only [hd1, hd2, Complex.normSq_nonneg b4, Complex.normSq_nonneg c01, Complex.normSq_nonneg c12, Complex.normSq_nonneg c13]
    exact p4 (Complex.normSq_eq_zero.mp hz)
  have dg_4_2 : c04 = 0 → c14 = 0 → c34 = 0 → False := by
    intro z1 z2 z3
    have hij : c24 = 0 := by
      have hx : b2 * c24 = 0 := by linear_combination h.st4 - (b0 : ℂ) * z1 - (b1 : ℂ) * z2 - (b3 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p2
      · exact y
    have hd := h.dg4
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b4]
  have dg_4_3 : c04 = 0 → c14 = 0 → c24 = 0 → False := by
    intro z1 z2 z3
    have hij : c34 = 0 := by
      have hx : b3 * c34 = 0 := by linear_combination h.st4 - (b0 : ℂ) * z1 - (b1 : ℂ) * z2 - (b2 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p3
      · exact y
    have hd := h.dg4
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b4]
  obtain ⟨d01, d02, d03, d04, d12, d13, d14, d23, d24, d34⟩ := dets0 h.st0 h.st1 h.st2 h.st3 h.st4 haf0 haf1 haf2 haf3 haf4 p0
  exact graph haf0 haf1 haf2 haf3 haf4 dg_0_1 dg_0_2 dg_0_3 dg_0_4 dg_1_0 dg_1_2 dg_1_3 dg_1_4 dg_2_0 dg_2_1 dg_2_3 dg_2_4 dg_3_0 dg_3_1 dg_3_2 dg_3_4 dg_4_0 dg_4_1 dg_4_2 dg_4_3 d01 d02 d03 d04 d12 d13 d14 d23 d24 d34

/-- The branch in which exactly the point amplitudes b1, b2, b3, b4 are nonzero. -/
theorem case30 {s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34 : ℂ} (h : Sys s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34)
    (p0 : b0 = 0) (p1 : b1 ≠ 0) (p2 : b2 ≠ 0) (p3 : b3 ≠ 0) (p4 : b4 ≠ 0) : False := by
  have kk01 : k01 = 0 := by
    rcases mul_eq_zero.mp h.kb01_1 with y | y
    · exact absurd y p1
    · exact y
  have kk02 : k02 = 0 := by
    rcases mul_eq_zero.mp h.kb02_2 with y | y
    · exact absurd y p2
    · exact y
  have kk03 : k03 = 0 := by
    rcases mul_eq_zero.mp h.kb03_3 with y | y
    · exact absurd y p3
    · exact y
  have kk04 : k04 = 0 := by
    rcases mul_eq_zero.mp h.kb04_4 with y | y
    · exact absurd y p4
    · exact y
  have kk12 : k12 = 0 := by
    rcases mul_eq_zero.mp h.kb12_1 with y | y
    · exact absurd y p1
    · exact y
  have kk13 : k13 = 0 := by
    rcases mul_eq_zero.mp h.kb13_1 with y | y
    · exact absurd y p1
    · exact y
  have kk14 : k14 = 0 := by
    rcases mul_eq_zero.mp h.kb14_1 with y | y
    · exact absurd y p1
    · exact y
  have kk23 : k23 = 0 := by
    rcases mul_eq_zero.mp h.kb23_2 with y | y
    · exact absurd y p2
    · exact y
  have kk24 : k24 = 0 := by
    rcases mul_eq_zero.mp h.kb24_2 with y | y
    · exact absurd y p2
    · exact y
  have kk34 : k34 = 0 := by
    rcases mul_eq_zero.mp h.kb34_3 with y | y
    · exact absurd y p3
    · exact y
  have haf0 : c12 * c34 + c13 * c24 + c14 * c23 = 0 := by
    have hx : (2 : ℂ) * s * (c12 * c34 + c13 * c24 + c14 * c23) = 0 := by
      linear_combination (-1 : ℂ) * h.hf0 + (c12 : ℂ) * kk34 + (c34 : ℂ) * kk12 + (c13 : ℂ) * kk24 + (c24 : ℂ) * kk13 + (c14 : ℂ) * kk23 + (c23 : ℂ) * kk14
    rcases mul_eq_zero.mp hx with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · norm_num at y2
      · exact absurd y2 h.hs
    · exact y
  have haf1 : c02 * c34 + c03 * c24 + c04 * c23 = 0 := by
    have hx : (2 : ℂ) * s * (c02 * c34 + c03 * c24 + c04 * c23) = 0 := by
      linear_combination (-1 : ℂ) * h.hf1 + (c02 : ℂ) * kk34 + (c34 : ℂ) * kk02 + (c03 : ℂ) * kk24 + (c24 : ℂ) * kk03 + (c04 : ℂ) * kk23 + (c23 : ℂ) * kk04
    rcases mul_eq_zero.mp hx with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · norm_num at y2
      · exact absurd y2 h.hs
    · exact y
  have haf2 : c01 * c34 + c03 * c14 + c04 * c13 = 0 := by
    have hx : (2 : ℂ) * s * (c01 * c34 + c03 * c14 + c04 * c13) = 0 := by
      linear_combination (-1 : ℂ) * h.hf2 + (c01 : ℂ) * kk34 + (c34 : ℂ) * kk01 + (c03 : ℂ) * kk14 + (c14 : ℂ) * kk03 + (c04 : ℂ) * kk13 + (c13 : ℂ) * kk04
    rcases mul_eq_zero.mp hx with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · norm_num at y2
      · exact absurd y2 h.hs
    · exact y
  have haf3 : c01 * c24 + c02 * c14 + c04 * c12 = 0 := by
    have hx : (2 : ℂ) * s * (c01 * c24 + c02 * c14 + c04 * c12) = 0 := by
      linear_combination (-1 : ℂ) * h.hf3 + (c01 : ℂ) * kk24 + (c24 : ℂ) * kk01 + (c02 : ℂ) * kk14 + (c14 : ℂ) * kk02 + (c04 : ℂ) * kk12 + (c12 : ℂ) * kk04
    rcases mul_eq_zero.mp hx with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · norm_num at y2
      · exact absurd y2 h.hs
    · exact y
  have haf4 : c01 * c23 + c02 * c13 + c03 * c12 = 0 := by
    have hx : (2 : ℂ) * s * (c01 * c23 + c02 * c13 + c03 * c12) = 0 := by
      linear_combination (-1 : ℂ) * h.hf4 + (c01 : ℂ) * kk23 + (c23 : ℂ) * kk01 + (c02 : ℂ) * kk13 + (c13 : ℂ) * kk02 + (c03 : ℂ) * kk12 + (c12 : ℂ) * kk03
    rcases mul_eq_zero.mp hx with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · norm_num at y2
      · exact absurd y2 h.hs
    · exact y
  have dg_0_1 : c02 = 0 → c03 = 0 → c04 = 0 → False := by
    intro z1 z2 z3
    have hij : c01 = 0 := by
      have hx : b1 * c01 = 0 := by linear_combination h.st0 - (b2 : ℂ) * z1 - (b3 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p1
      · exact y
    have hd := h.dg0
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b0]
  have dg_0_2 : c01 = 0 → c03 = 0 → c04 = 0 → False := by
    intro z1 z2 z3
    have hij : c02 = 0 := by
      have hx : b2 * c02 = 0 := by linear_combination h.st0 - (b1 : ℂ) * z1 - (b3 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p2
      · exact y
    have hd := h.dg0
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b0]
  have dg_0_3 : c01 = 0 → c02 = 0 → c04 = 0 → False := by
    intro z1 z2 z3
    have hij : c03 = 0 := by
      have hx : b3 * c03 = 0 := by linear_combination h.st0 - (b1 : ℂ) * z1 - (b2 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p3
      · exact y
    have hd := h.dg0
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b0]
  have dg_0_4 : c01 = 0 → c02 = 0 → c03 = 0 → False := by
    intro z1 z2 z3
    have hij : c04 = 0 := by
      have hx : b4 * c04 = 0 := by linear_combination h.st0 - (b1 : ℂ) * z1 - (b2 : ℂ) * z2 - (b3 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p4
      · exact y
    have hd := h.dg0
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b0]
  have dg_1_0 : c12 = 0 → c13 = 0 → c14 = 0 → False := by
    intro z1 z2 z3
    have hd1 := h.dg1
    have hd2 := h.dg0
    rw [z1, z2, z3, Complex.normSq_zero] at hd1
    rw [p0, Complex.normSq_zero] at hd2
    have hz : Complex.normSq b1 = 0 := by linarith only [hd1, hd2, Complex.normSq_nonneg b1, Complex.normSq_nonneg c02, Complex.normSq_nonneg c03, Complex.normSq_nonneg c04]
    exact p1 (Complex.normSq_eq_zero.mp hz)
  have dg_1_2 : c01 = 0 → c13 = 0 → c14 = 0 → False := by
    intro z1 z2 z3
    have hij : c12 = 0 := by
      have hx : b2 * c12 = 0 := by linear_combination h.st1 - (b0 : ℂ) * z1 - (b3 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p2
      · exact y
    have hd := h.dg1
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b1]
  have dg_1_3 : c01 = 0 → c12 = 0 → c14 = 0 → False := by
    intro z1 z2 z3
    have hij : c13 = 0 := by
      have hx : b3 * c13 = 0 := by linear_combination h.st1 - (b0 : ℂ) * z1 - (b2 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p3
      · exact y
    have hd := h.dg1
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b1]
  have dg_1_4 : c01 = 0 → c12 = 0 → c13 = 0 → False := by
    intro z1 z2 z3
    have hij : c14 = 0 := by
      have hx : b4 * c14 = 0 := by linear_combination h.st1 - (b0 : ℂ) * z1 - (b2 : ℂ) * z2 - (b3 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p4
      · exact y
    have hd := h.dg1
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b1]
  have dg_2_0 : c12 = 0 → c23 = 0 → c24 = 0 → False := by
    intro z1 z2 z3
    have hd1 := h.dg2
    have hd2 := h.dg0
    rw [z1, z2, z3, Complex.normSq_zero] at hd1
    rw [p0, Complex.normSq_zero] at hd2
    have hz : Complex.normSq b2 = 0 := by linarith only [hd1, hd2, Complex.normSq_nonneg b2, Complex.normSq_nonneg c01, Complex.normSq_nonneg c03, Complex.normSq_nonneg c04]
    exact p2 (Complex.normSq_eq_zero.mp hz)
  have dg_2_1 : c02 = 0 → c23 = 0 → c24 = 0 → False := by
    intro z1 z2 z3
    have hij : c12 = 0 := by
      have hx : b1 * c12 = 0 := by linear_combination h.st2 - (b0 : ℂ) * z1 - (b3 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p1
      · exact y
    have hd := h.dg2
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b2]
  have dg_2_3 : c02 = 0 → c12 = 0 → c24 = 0 → False := by
    intro z1 z2 z3
    have hij : c23 = 0 := by
      have hx : b3 * c23 = 0 := by linear_combination h.st2 - (b0 : ℂ) * z1 - (b1 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p3
      · exact y
    have hd := h.dg2
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b2]
  have dg_2_4 : c02 = 0 → c12 = 0 → c23 = 0 → False := by
    intro z1 z2 z3
    have hij : c24 = 0 := by
      have hx : b4 * c24 = 0 := by linear_combination h.st2 - (b0 : ℂ) * z1 - (b1 : ℂ) * z2 - (b3 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p4
      · exact y
    have hd := h.dg2
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b2]
  have dg_3_0 : c13 = 0 → c23 = 0 → c34 = 0 → False := by
    intro z1 z2 z3
    have hd1 := h.dg3
    have hd2 := h.dg0
    rw [z1, z2, z3, Complex.normSq_zero] at hd1
    rw [p0, Complex.normSq_zero] at hd2
    have hz : Complex.normSq b3 = 0 := by linarith only [hd1, hd2, Complex.normSq_nonneg b3, Complex.normSq_nonneg c01, Complex.normSq_nonneg c02, Complex.normSq_nonneg c04]
    exact p3 (Complex.normSq_eq_zero.mp hz)
  have dg_3_1 : c03 = 0 → c23 = 0 → c34 = 0 → False := by
    intro z1 z2 z3
    have hij : c13 = 0 := by
      have hx : b1 * c13 = 0 := by linear_combination h.st3 - (b0 : ℂ) * z1 - (b2 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p1
      · exact y
    have hd := h.dg3
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b3]
  have dg_3_2 : c03 = 0 → c13 = 0 → c34 = 0 → False := by
    intro z1 z2 z3
    have hij : c23 = 0 := by
      have hx : b2 * c23 = 0 := by linear_combination h.st3 - (b0 : ℂ) * z1 - (b1 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p2
      · exact y
    have hd := h.dg3
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b3]
  have dg_3_4 : c03 = 0 → c13 = 0 → c23 = 0 → False := by
    intro z1 z2 z3
    have hij : c34 = 0 := by
      have hx : b4 * c34 = 0 := by linear_combination h.st3 - (b0 : ℂ) * z1 - (b1 : ℂ) * z2 - (b2 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p4
      · exact y
    have hd := h.dg3
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b3]
  have dg_4_0 : c14 = 0 → c24 = 0 → c34 = 0 → False := by
    intro z1 z2 z3
    have hd1 := h.dg4
    have hd2 := h.dg0
    rw [z1, z2, z3, Complex.normSq_zero] at hd1
    rw [p0, Complex.normSq_zero] at hd2
    have hz : Complex.normSq b4 = 0 := by linarith only [hd1, hd2, Complex.normSq_nonneg b4, Complex.normSq_nonneg c01, Complex.normSq_nonneg c02, Complex.normSq_nonneg c03]
    exact p4 (Complex.normSq_eq_zero.mp hz)
  have dg_4_1 : c04 = 0 → c24 = 0 → c34 = 0 → False := by
    intro z1 z2 z3
    have hij : c14 = 0 := by
      have hx : b1 * c14 = 0 := by linear_combination h.st4 - (b0 : ℂ) * z1 - (b2 : ℂ) * z2 - (b3 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p1
      · exact y
    have hd := h.dg4
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b4]
  have dg_4_2 : c04 = 0 → c14 = 0 → c34 = 0 → False := by
    intro z1 z2 z3
    have hij : c24 = 0 := by
      have hx : b2 * c24 = 0 := by linear_combination h.st4 - (b0 : ℂ) * z1 - (b1 : ℂ) * z2 - (b3 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p2
      · exact y
    have hd := h.dg4
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b4]
  have dg_4_3 : c04 = 0 → c14 = 0 → c24 = 0 → False := by
    intro z1 z2 z3
    have hij : c34 = 0 := by
      have hx : b3 * c34 = 0 := by linear_combination h.st4 - (b0 : ℂ) * z1 - (b1 : ℂ) * z2 - (b2 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p3
      · exact y
    have hd := h.dg4
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b4]
  obtain ⟨d01, d02, d03, d04, d12, d13, d14, d23, d24, d34⟩ := dets1 h.st0 h.st1 h.st2 h.st3 h.st4 haf0 haf1 haf2 haf3 haf4 p1
  exact graph haf0 haf1 haf2 haf3 haf4 dg_0_1 dg_0_2 dg_0_3 dg_0_4 dg_1_0 dg_1_2 dg_1_3 dg_1_4 dg_2_0 dg_2_1 dg_2_3 dg_2_4 dg_3_0 dg_3_1 dg_3_2 dg_3_4 dg_4_0 dg_4_1 dg_4_2 dg_4_3 d01 d02 d03 d04 d12 d13 d14 d23 d24 d34

/-- The branch in which exactly the point amplitudes b0, b1, b2, b3, b4 are nonzero. -/
theorem case31 {s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34 : ℂ} (h : Sys s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34)
    (p0 : b0 ≠ 0) (p1 : b1 ≠ 0) (p2 : b2 ≠ 0) (p3 : b3 ≠ 0) (p4 : b4 ≠ 0) : False := by
  have kk01 : k01 = 0 := by
    rcases mul_eq_zero.mp h.kb01_0 with y | y
    · exact absurd y p0
    · exact y
  have kk02 : k02 = 0 := by
    rcases mul_eq_zero.mp h.kb02_0 with y | y
    · exact absurd y p0
    · exact y
  have kk03 : k03 = 0 := by
    rcases mul_eq_zero.mp h.kb03_0 with y | y
    · exact absurd y p0
    · exact y
  have kk04 : k04 = 0 := by
    rcases mul_eq_zero.mp h.kb04_0 with y | y
    · exact absurd y p0
    · exact y
  have kk12 : k12 = 0 := by
    rcases mul_eq_zero.mp h.kb12_1 with y | y
    · exact absurd y p1
    · exact y
  have kk13 : k13 = 0 := by
    rcases mul_eq_zero.mp h.kb13_1 with y | y
    · exact absurd y p1
    · exact y
  have kk14 : k14 = 0 := by
    rcases mul_eq_zero.mp h.kb14_1 with y | y
    · exact absurd y p1
    · exact y
  have kk23 : k23 = 0 := by
    rcases mul_eq_zero.mp h.kb23_2 with y | y
    · exact absurd y p2
    · exact y
  have kk24 : k24 = 0 := by
    rcases mul_eq_zero.mp h.kb24_2 with y | y
    · exact absurd y p2
    · exact y
  have kk34 : k34 = 0 := by
    rcases mul_eq_zero.mp h.kb34_3 with y | y
    · exact absurd y p3
    · exact y
  have haf0 : c12 * c34 + c13 * c24 + c14 * c23 = 0 := by
    have hx : (2 : ℂ) * s * (c12 * c34 + c13 * c24 + c14 * c23) = 0 := by
      linear_combination (-1 : ℂ) * h.hf0 + (c12 : ℂ) * kk34 + (c34 : ℂ) * kk12 + (c13 : ℂ) * kk24 + (c24 : ℂ) * kk13 + (c14 : ℂ) * kk23 + (c23 : ℂ) * kk14
    rcases mul_eq_zero.mp hx with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · norm_num at y2
      · exact absurd y2 h.hs
    · exact y
  have haf1 : c02 * c34 + c03 * c24 + c04 * c23 = 0 := by
    have hx : (2 : ℂ) * s * (c02 * c34 + c03 * c24 + c04 * c23) = 0 := by
      linear_combination (-1 : ℂ) * h.hf1 + (c02 : ℂ) * kk34 + (c34 : ℂ) * kk02 + (c03 : ℂ) * kk24 + (c24 : ℂ) * kk03 + (c04 : ℂ) * kk23 + (c23 : ℂ) * kk04
    rcases mul_eq_zero.mp hx with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · norm_num at y2
      · exact absurd y2 h.hs
    · exact y
  have haf2 : c01 * c34 + c03 * c14 + c04 * c13 = 0 := by
    have hx : (2 : ℂ) * s * (c01 * c34 + c03 * c14 + c04 * c13) = 0 := by
      linear_combination (-1 : ℂ) * h.hf2 + (c01 : ℂ) * kk34 + (c34 : ℂ) * kk01 + (c03 : ℂ) * kk14 + (c14 : ℂ) * kk03 + (c04 : ℂ) * kk13 + (c13 : ℂ) * kk04
    rcases mul_eq_zero.mp hx with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · norm_num at y2
      · exact absurd y2 h.hs
    · exact y
  have haf3 : c01 * c24 + c02 * c14 + c04 * c12 = 0 := by
    have hx : (2 : ℂ) * s * (c01 * c24 + c02 * c14 + c04 * c12) = 0 := by
      linear_combination (-1 : ℂ) * h.hf3 + (c01 : ℂ) * kk24 + (c24 : ℂ) * kk01 + (c02 : ℂ) * kk14 + (c14 : ℂ) * kk02 + (c04 : ℂ) * kk12 + (c12 : ℂ) * kk04
    rcases mul_eq_zero.mp hx with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · norm_num at y2
      · exact absurd y2 h.hs
    · exact y
  have haf4 : c01 * c23 + c02 * c13 + c03 * c12 = 0 := by
    have hx : (2 : ℂ) * s * (c01 * c23 + c02 * c13 + c03 * c12) = 0 := by
      linear_combination (-1 : ℂ) * h.hf4 + (c01 : ℂ) * kk23 + (c23 : ℂ) * kk01 + (c02 : ℂ) * kk13 + (c13 : ℂ) * kk02 + (c03 : ℂ) * kk12 + (c12 : ℂ) * kk03
    rcases mul_eq_zero.mp hx with y | y
    · rcases mul_eq_zero.mp y with y2 | y2
      · norm_num at y2
      · exact absurd y2 h.hs
    · exact y
  have dg_0_1 : c02 = 0 → c03 = 0 → c04 = 0 → False := by
    intro z1 z2 z3
    have hij : c01 = 0 := by
      have hx : b1 * c01 = 0 := by linear_combination h.st0 - (b2 : ℂ) * z1 - (b3 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p1
      · exact y
    have hd := h.dg0
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b0]
  have dg_0_2 : c01 = 0 → c03 = 0 → c04 = 0 → False := by
    intro z1 z2 z3
    have hij : c02 = 0 := by
      have hx : b2 * c02 = 0 := by linear_combination h.st0 - (b1 : ℂ) * z1 - (b3 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p2
      · exact y
    have hd := h.dg0
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b0]
  have dg_0_3 : c01 = 0 → c02 = 0 → c04 = 0 → False := by
    intro z1 z2 z3
    have hij : c03 = 0 := by
      have hx : b3 * c03 = 0 := by linear_combination h.st0 - (b1 : ℂ) * z1 - (b2 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p3
      · exact y
    have hd := h.dg0
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b0]
  have dg_0_4 : c01 = 0 → c02 = 0 → c03 = 0 → False := by
    intro z1 z2 z3
    have hij : c04 = 0 := by
      have hx : b4 * c04 = 0 := by linear_combination h.st0 - (b1 : ℂ) * z1 - (b2 : ℂ) * z2 - (b3 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p4
      · exact y
    have hd := h.dg0
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b0]
  have dg_1_0 : c12 = 0 → c13 = 0 → c14 = 0 → False := by
    intro z1 z2 z3
    have hij : c01 = 0 := by
      have hx : b0 * c01 = 0 := by linear_combination h.st1 - (b2 : ℂ) * z1 - (b3 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p0
      · exact y
    have hd := h.dg1
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b1]
  have dg_1_2 : c01 = 0 → c13 = 0 → c14 = 0 → False := by
    intro z1 z2 z3
    have hij : c12 = 0 := by
      have hx : b2 * c12 = 0 := by linear_combination h.st1 - (b0 : ℂ) * z1 - (b3 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p2
      · exact y
    have hd := h.dg1
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b1]
  have dg_1_3 : c01 = 0 → c12 = 0 → c14 = 0 → False := by
    intro z1 z2 z3
    have hij : c13 = 0 := by
      have hx : b3 * c13 = 0 := by linear_combination h.st1 - (b0 : ℂ) * z1 - (b2 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p3
      · exact y
    have hd := h.dg1
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b1]
  have dg_1_4 : c01 = 0 → c12 = 0 → c13 = 0 → False := by
    intro z1 z2 z3
    have hij : c14 = 0 := by
      have hx : b4 * c14 = 0 := by linear_combination h.st1 - (b0 : ℂ) * z1 - (b2 : ℂ) * z2 - (b3 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p4
      · exact y
    have hd := h.dg1
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b1]
  have dg_2_0 : c12 = 0 → c23 = 0 → c24 = 0 → False := by
    intro z1 z2 z3
    have hij : c02 = 0 := by
      have hx : b0 * c02 = 0 := by linear_combination h.st2 - (b1 : ℂ) * z1 - (b3 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p0
      · exact y
    have hd := h.dg2
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b2]
  have dg_2_1 : c02 = 0 → c23 = 0 → c24 = 0 → False := by
    intro z1 z2 z3
    have hij : c12 = 0 := by
      have hx : b1 * c12 = 0 := by linear_combination h.st2 - (b0 : ℂ) * z1 - (b3 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p1
      · exact y
    have hd := h.dg2
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b2]
  have dg_2_3 : c02 = 0 → c12 = 0 → c24 = 0 → False := by
    intro z1 z2 z3
    have hij : c23 = 0 := by
      have hx : b3 * c23 = 0 := by linear_combination h.st2 - (b0 : ℂ) * z1 - (b1 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p3
      · exact y
    have hd := h.dg2
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b2]
  have dg_2_4 : c02 = 0 → c12 = 0 → c23 = 0 → False := by
    intro z1 z2 z3
    have hij : c24 = 0 := by
      have hx : b4 * c24 = 0 := by linear_combination h.st2 - (b0 : ℂ) * z1 - (b1 : ℂ) * z2 - (b3 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p4
      · exact y
    have hd := h.dg2
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b2]
  have dg_3_0 : c13 = 0 → c23 = 0 → c34 = 0 → False := by
    intro z1 z2 z3
    have hij : c03 = 0 := by
      have hx : b0 * c03 = 0 := by linear_combination h.st3 - (b1 : ℂ) * z1 - (b2 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p0
      · exact y
    have hd := h.dg3
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b3]
  have dg_3_1 : c03 = 0 → c23 = 0 → c34 = 0 → False := by
    intro z1 z2 z3
    have hij : c13 = 0 := by
      have hx : b1 * c13 = 0 := by linear_combination h.st3 - (b0 : ℂ) * z1 - (b2 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p1
      · exact y
    have hd := h.dg3
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b3]
  have dg_3_2 : c03 = 0 → c13 = 0 → c34 = 0 → False := by
    intro z1 z2 z3
    have hij : c23 = 0 := by
      have hx : b2 * c23 = 0 := by linear_combination h.st3 - (b0 : ℂ) * z1 - (b1 : ℂ) * z2 - (b4 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p2
      · exact y
    have hd := h.dg3
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b3]
  have dg_3_4 : c03 = 0 → c13 = 0 → c23 = 0 → False := by
    intro z1 z2 z3
    have hij : c34 = 0 := by
      have hx : b4 * c34 = 0 := by linear_combination h.st3 - (b0 : ℂ) * z1 - (b1 : ℂ) * z2 - (b2 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p4
      · exact y
    have hd := h.dg3
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b3]
  have dg_4_0 : c14 = 0 → c24 = 0 → c34 = 0 → False := by
    intro z1 z2 z3
    have hij : c04 = 0 := by
      have hx : b0 * c04 = 0 := by linear_combination h.st4 - (b1 : ℂ) * z1 - (b2 : ℂ) * z2 - (b3 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p0
      · exact y
    have hd := h.dg4
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b4]
  have dg_4_1 : c04 = 0 → c24 = 0 → c34 = 0 → False := by
    intro z1 z2 z3
    have hij : c14 = 0 := by
      have hx : b1 * c14 = 0 := by linear_combination h.st4 - (b0 : ℂ) * z1 - (b2 : ℂ) * z2 - (b3 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p1
      · exact y
    have hd := h.dg4
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b4]
  have dg_4_2 : c04 = 0 → c14 = 0 → c34 = 0 → False := by
    intro z1 z2 z3
    have hij : c24 = 0 := by
      have hx : b2 * c24 = 0 := by linear_combination h.st4 - (b0 : ℂ) * z1 - (b1 : ℂ) * z2 - (b3 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p2
      · exact y
    have hd := h.dg4
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b4]
  have dg_4_3 : c04 = 0 → c14 = 0 → c24 = 0 → False := by
    intro z1 z2 z3
    have hij : c34 = 0 := by
      have hx : b3 * c34 = 0 := by linear_combination h.st4 - (b0 : ℂ) * z1 - (b1 : ℂ) * z2 - (b2 : ℂ) * z3
      rcases mul_eq_zero.mp hx with y | y
      · exact absurd y p3
      · exact y
    have hd := h.dg4
    rw [hij, z1, z2, z3, Complex.normSq_zero] at hd
    linarith only [hd, Complex.normSq_nonneg b4]
  obtain ⟨d01, d02, d03, d04, d12, d13, d14, d23, d24, d34⟩ := dets0 h.st0 h.st1 h.st2 h.st3 h.st4 haf0 haf1 haf2 haf3 haf4 p0
  exact graph haf0 haf1 haf2 haf3 haf4 dg_0_1 dg_0_2 dg_0_3 dg_0_4 dg_1_0 dg_1_2 dg_1_3 dg_1_4 dg_2_0 dg_2_1 dg_2_3 dg_2_4 dg_3_0 dg_3_1 dg_3_2 dg_3_4 dg_4_0 dg_4_1 dg_4_2 dg_4_3 d01 d02 d03 d04 d12 d13 d14 d23 d24 d34

/-- **The K_5 system is contradictory.** -/
theorem no_go {s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34 : ℂ} (h : Sys s b0 b1 b2 b3 b4 c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 k01 k02 k03 k04 k12 k13 k14 k23 k24 k34) : False := by
  rcases eq_or_ne b0 0 with p0 | p0
  · rcases eq_or_ne b1 0 with p1 | p1
    · rcases eq_or_ne b2 0 with p2 | p2
      · rcases eq_or_ne b3 0 with p3 | p3
        · rcases eq_or_ne b4 0 with p4 | p4
          · exact case0 h p0 p1 p2 p3 p4
          · exact case16 h p0 p1 p2 p3 p4
        · rcases eq_or_ne b4 0 with p4 | p4
          · exact case8 h p0 p1 p2 p3 p4
          · exact case24 h p0 p1 p2 p3 p4
      · rcases eq_or_ne b3 0 with p3 | p3
        · rcases eq_or_ne b4 0 with p4 | p4
          · exact case4 h p0 p1 p2 p3 p4
          · exact case20 h p0 p1 p2 p3 p4
        · rcases eq_or_ne b4 0 with p4 | p4
          · exact case12 h p0 p1 p2 p3 p4
          · exact case28 h p0 p1 p2 p3 p4
    · rcases eq_or_ne b2 0 with p2 | p2
      · rcases eq_or_ne b3 0 with p3 | p3
        · rcases eq_or_ne b4 0 with p4 | p4
          · exact case2 h p0 p1 p2 p3 p4
          · exact case18 h p0 p1 p2 p3 p4
        · rcases eq_or_ne b4 0 with p4 | p4
          · exact case10 h p0 p1 p2 p3 p4
          · exact case26 h p0 p1 p2 p3 p4
      · rcases eq_or_ne b3 0 with p3 | p3
        · rcases eq_or_ne b4 0 with p4 | p4
          · exact case6 h p0 p1 p2 p3 p4
          · exact case22 h p0 p1 p2 p3 p4
        · rcases eq_or_ne b4 0 with p4 | p4
          · exact case14 h p0 p1 p2 p3 p4
          · exact case30 h p0 p1 p2 p3 p4
  · rcases eq_or_ne b1 0 with p1 | p1
    · rcases eq_or_ne b2 0 with p2 | p2
      · rcases eq_or_ne b3 0 with p3 | p3
        · rcases eq_or_ne b4 0 with p4 | p4
          · exact case1 h p0 p1 p2 p3 p4
          · exact case17 h p0 p1 p2 p3 p4
        · rcases eq_or_ne b4 0 with p4 | p4
          · exact case9 h p0 p1 p2 p3 p4
          · exact case25 h p0 p1 p2 p3 p4
      · rcases eq_or_ne b3 0 with p3 | p3
        · rcases eq_or_ne b4 0 with p4 | p4
          · exact case5 h p0 p1 p2 p3 p4
          · exact case21 h p0 p1 p2 p3 p4
        · rcases eq_or_ne b4 0 with p4 | p4
          · exact case13 h p0 p1 p2 p3 p4
          · exact case29 h p0 p1 p2 p3 p4
    · rcases eq_or_ne b2 0 with p2 | p2
      · rcases eq_or_ne b3 0 with p3 | p3
        · rcases eq_or_ne b4 0 with p4 | p4
          · exact case3 h p0 p1 p2 p3 p4
          · exact case19 h p0 p1 p2 p3 p4
        · rcases eq_or_ne b4 0 with p4 | p4
          · exact case11 h p0 p1 p2 p3 p4
          · exact case27 h p0 p1 p2 p3 p4
      · rcases eq_or_ne b3 0 with p3 | p3
        · rcases eq_or_ne b4 0 with p4 | p4
          · exact case7 h p0 p1 p2 p3 p4
          · exact case23 h p0 p1 p2 p3 p4
        · rcases eq_or_ne b4 0 with p4 | p4
          · exact case15 h p0 p1 p2 p3 p4
          · exact case31 h p0 p1 p2 p3 p4

end

end SixQubit.K5
