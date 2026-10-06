import Mathlib

import SS.FullKL
import SixQubit.Common

/-!
# Vanishing hafnians on the six-vertex support graph

Orbit 17 of `six_qubit_sslp.tex` reduces to the following purely algebraic
configuration.  Fifteen complex numbers `c_ij` are indexed by the edges of
`K_6`.  Every four-set carries a *hafnian* equation

```
c_ij c_kl + c_ik c_jl + c_il c_jk = 0 ,
```

and the squared moduli form a scaled fractional perfect matching:
`sum_{e ni v} |c_e|^2 = 1/4` at every vertex `v`.  The two families are
contradictory.

The proof never divides.  Three facts do all the work.

* `deg4`: the single monomial identity
  `c01 c02 c03 c45 = (c04 c05 / 3) H_0123 - (c03 c05 / 6) H_0124 - ...`,
  found by eliminating in the ten hafnians through one vertex.  It says a
  vertex with three active edges forces the complementary edge to vanish.
* `tri`: the odd-triangle elimination `uc * va * vb = 0`, reused from the
  shape already met by several orbits.
* the degree equations, which forbid an isolated vertex and forbid a star.

Because the whole hypothesis bundle `Sys` is stable under vertex relabelling
(`swap01`, ..., `swap45`), each combinatorial case is proved once in a
canonical labelling and transported by a word in those five lemmas.

`native_decide` is not used, and the module mentions no bit strings.
-/

namespace SixQubit.Hafnian

open scoped ComplexConjugate

noncomputable section

/-! ## The hypothesis bundle -/

/-- The fifteen four-set hafnian equations together with the six weighted
degree equations of the fractional perfect matching. -/
structure Sys (c01 c02 c03 c04 c05 c12 c13 c14 c15 c23 c24 c25 c34 c35 c45 : ℂ) : Prop where
  h0123 : c01 * c23 + c02 * c13 + c03 * c12 = 0
  h0124 : c01 * c24 + c02 * c14 + c04 * c12 = 0
  h0125 : c01 * c25 + c02 * c15 + c05 * c12 = 0
  h0134 : c01 * c34 + c03 * c14 + c04 * c13 = 0
  h0135 : c01 * c35 + c03 * c15 + c05 * c13 = 0
  h0145 : c01 * c45 + c04 * c15 + c05 * c14 = 0
  h0234 : c02 * c34 + c03 * c24 + c04 * c23 = 0
  h0235 : c02 * c35 + c03 * c25 + c05 * c23 = 0
  h0245 : c02 * c45 + c04 * c25 + c05 * c24 = 0
  h0345 : c03 * c45 + c04 * c35 + c05 * c34 = 0
  h1234 : c12 * c34 + c13 * c24 + c14 * c23 = 0
  h1235 : c12 * c35 + c13 * c25 + c15 * c23 = 0
  h1245 : c12 * c45 + c14 * c25 + c15 * c24 = 0
  h1345 : c13 * c45 + c14 * c35 + c15 * c34 = 0
  h2345 : c23 * c45 + c24 * c35 + c25 * c34 = 0
  d0 : Complex.normSq c01 + Complex.normSq c02 + Complex.normSq c03 + Complex.normSq c04 + Complex.normSq c05 = 1/4
  d1 : Complex.normSq c01 + Complex.normSq c12 + Complex.normSq c13 + Complex.normSq c14 + Complex.normSq c15 = 1/4
  d2 : Complex.normSq c02 + Complex.normSq c12 + Complex.normSq c23 + Complex.normSq c24 + Complex.normSq c25 = 1/4
  d3 : Complex.normSq c03 + Complex.normSq c13 + Complex.normSq c23 + Complex.normSq c34 + Complex.normSq c35 = 1/4
  d4 : Complex.normSq c04 + Complex.normSq c14 + Complex.normSq c24 + Complex.normSq c34 + Complex.normSq c45 = 1/4
  d5 : Complex.normSq c05 + Complex.normSq c15 + Complex.normSq c25 + Complex.normSq c35 + Complex.normSq c45 = 1/4

variable {c01 c02 c03 c04 c05 c12 c13 c14 c15 c23 c24 c25 c34 c35 c45 : ℂ}

/-! ## Elementary helpers -/

/-- Cancel three nonzero factors from a four-fold product. -/
theorem mul4 {a b c d : ℂ} (h : a * b * c * d = 0)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) : d = 0 := by
  rcases mul_eq_zero.mp h with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd h3 ha
      · exact absurd h3 hb
    · exact absurd h2 hc
  · exact h1

/-- Cancel two nonzero factors from a threefold product. -/
theorem mul3 {a b c : ℂ} (h : a * b * c = 0) (hb : b ≠ 0) (hc : c ≠ 0) : a = 0 := by
  rcases mul_eq_zero.mp h with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact h2
    · exact absurd h2 hb
  · exact absurd h1 hc

/-- The odd-triangle elimination: three reciprocal relations force a single
product to vanish, with no division and no nonvanishing side condition. -/
theorem tri {ua ub uc va vb vc : ℂ}
    (h1 : ua * vb + ub * va = 0)
    (h2 : ua * vc + uc * va = 0)
    (h3 : ub * vc + uc * vb = 0) : uc * va * vb = 0 := by
  linear_combination (-vc / 2) * h1 + (vb / 2) * h2 + (va / 2) * h3

/-! ## Vertex relabelling -/

/-- Relabelling the two vertices 0 and 1 preserves the system. -/
theorem swap01 (h : Sys c01 c02 c03 c04 c05 c12 c13 c14 c15 c23 c24 c25 c34 c35 c45) :
    Sys c01 c12 c13 c14 c15 c02 c03 c04 c05 c23 c24 c25 c34 c35 c45 :=
  ⟨by linear_combination h.h0123,
   by linear_combination h.h0124,
   by linear_combination h.h0125,
   by linear_combination h.h0134,
   by linear_combination h.h0135,
   by linear_combination h.h0145,
   by linear_combination h.h1234,
   by linear_combination h.h1235,
   by linear_combination h.h1245,
   by linear_combination h.h1345,
   by linear_combination h.h0234,
   by linear_combination h.h0235,
   by linear_combination h.h0245,
   by linear_combination h.h0345,
   by linear_combination h.h2345,
   by linear_combination h.d1,
   by linear_combination h.d0,
   by linear_combination h.d2,
   by linear_combination h.d3,
   by linear_combination h.d4,
   by linear_combination h.d5⟩

/-- Relabelling the two vertices 1 and 2 preserves the system. -/
theorem swap12 (h : Sys c01 c02 c03 c04 c05 c12 c13 c14 c15 c23 c24 c25 c34 c35 c45) :
    Sys c02 c01 c03 c04 c05 c12 c23 c24 c25 c13 c14 c15 c34 c35 c45 :=
  ⟨by linear_combination h.h0123,
   by linear_combination h.h0124,
   by linear_combination h.h0125,
   by linear_combination h.h0234,
   by linear_combination h.h0235,
   by linear_combination h.h0245,
   by linear_combination h.h0134,
   by linear_combination h.h0135,
   by linear_combination h.h0145,
   by linear_combination h.h0345,
   by linear_combination h.h1234,
   by linear_combination h.h1235,
   by linear_combination h.h1245,
   by linear_combination h.h2345,
   by linear_combination h.h1345,
   by linear_combination h.d0,
   by linear_combination h.d2,
   by linear_combination h.d1,
   by linear_combination h.d3,
   by linear_combination h.d4,
   by linear_combination h.d5⟩

/-- Relabelling the two vertices 2 and 3 preserves the system. -/
theorem swap23 (h : Sys c01 c02 c03 c04 c05 c12 c13 c14 c15 c23 c24 c25 c34 c35 c45) :
    Sys c01 c03 c02 c04 c05 c13 c12 c14 c15 c23 c34 c35 c24 c25 c45 :=
  ⟨by linear_combination h.h0123,
   by linear_combination h.h0134,
   by linear_combination h.h0135,
   by linear_combination h.h0124,
   by linear_combination h.h0125,
   by linear_combination h.h0145,
   by linear_combination h.h0234,
   by linear_combination h.h0235,
   by linear_combination h.h0345,
   by linear_combination h.h0245,
   by linear_combination h.h1234,
   by linear_combination h.h1235,
   by linear_combination h.h1345,
   by linear_combination h.h1245,
   by linear_combination h.h2345,
   by linear_combination h.d0,
   by linear_combination h.d1,
   by linear_combination h.d3,
   by linear_combination h.d2,
   by linear_combination h.d4,
   by linear_combination h.d5⟩

/-- Relabelling the two vertices 3 and 4 preserves the system. -/
theorem swap34 (h : Sys c01 c02 c03 c04 c05 c12 c13 c14 c15 c23 c24 c25 c34 c35 c45) :
    Sys c01 c02 c04 c03 c05 c12 c14 c13 c15 c24 c23 c25 c34 c45 c35 :=
  ⟨by linear_combination h.h0124,
   by linear_combination h.h0123,
   by linear_combination h.h0125,
   by linear_combination h.h0134,
   by linear_combination h.h0145,
   by linear_combination h.h0135,
   by linear_combination h.h0234,
   by linear_combination h.h0245,
   by linear_combination h.h0235,
   by linear_combination h.h0345,
   by linear_combination h.h1234,
   by linear_combination h.h1245,
   by linear_combination h.h1235,
   by linear_combination h.h1345,
   by linear_combination h.h2345,
   by linear_combination h.d0,
   by linear_combination h.d1,
   by linear_combination h.d2,
   by linear_combination h.d4,
   by linear_combination h.d3,
   by linear_combination h.d5⟩

/-- Relabelling the two vertices 4 and 5 preserves the system. -/
theorem swap45 (h : Sys c01 c02 c03 c04 c05 c12 c13 c14 c15 c23 c24 c25 c34 c35 c45) :
    Sys c01 c02 c03 c05 c04 c12 c13 c15 c14 c23 c25 c24 c35 c34 c45 :=
  ⟨by linear_combination h.h0123,
   by linear_combination h.h0125,
   by linear_combination h.h0124,
   by linear_combination h.h0135,
   by linear_combination h.h0134,
   by linear_combination h.h0145,
   by linear_combination h.h0235,
   by linear_combination h.h0234,
   by linear_combination h.h0245,
   by linear_combination h.h0345,
   by linear_combination h.h1235,
   by linear_combination h.h1234,
   by linear_combination h.h1245,
   by linear_combination h.h1345,
   by linear_combination h.h2345,
   by linear_combination h.d0,
   by linear_combination h.d1,
   by linear_combination h.d2,
   by linear_combination h.d3,
   by linear_combination h.d5,
   by linear_combination h.d4⟩

/-! ## The degree-four monomial certificate -/

/-- **Three active edges at a vertex kill the complementary edge.**  The
identity is a rational combination of the ten hafnians through vertex `0`;
it was obtained by eliminating the ten edges of the opposite `K_5`. -/
theorem deg4 (h : Sys c01 c02 c03 c04 c05 c12 c13 c14 c15 c23 c24 c25 c34 c35 c45) :
    c01 * c02 * c03 * c45 = 0 := by
  linear_combination (c04 * c05 / 3) * h.h0123 - (c03 * c05 / 6) * h.h0124
    - (c03 * c04 / 6) * h.h0125 - (c02 * c05 / 6) * h.h0134
    - (c02 * c04 / 6) * h.h0135 + (c02 * c03 / 3) * h.h0145
    - (c01 * c05 / 6) * h.h0234 - (c01 * c04 / 6) * h.h0235
    + (c01 * c03 / 3) * h.h0245 + (c01 * c02 / 3) * h.h0345

/-! ## Isolated vertices and stars -/

/-- A vertex with no active edge contradicts its degree equation. -/
theorem iso (h : Sys c01 c02 c03 c04 c05 c12 c13 c14 c15 c23 c24 c25 c34 c35 c45)
    (z1 : c01 = 0) (z2 : c02 = 0) (z3 : c03 = 0) (z4 : c04 = 0) (z5 : c05 = 0) :
    False := by
  have hd := h.d0
  rw [z1, z2, z3, z4, z5] at hd
  norm_num at hd

/-- A star has a leaf mass of `1/4` on every one of its five edges, so its
centre carries weighted degree `5/4`. -/
theorem star (h : Sys c01 c02 c03 c04 c05 c12 c13 c14 c15 c23 c24 c25 c34 c35 c45)
    (z12 : c12 = 0) (z13 : c13 = 0) (z14 : c14 = 0) (z15 : c15 = 0) (z23 : c23 = 0) (z24 : c24 = 0) (z25 : c25 = 0) (z34 : c34 = 0) (z35 : c35 = 0) (z45 : c45 = 0) :
    False := by
  have k1 : Complex.normSq c01 = 1/4 := by
    have hd := h.d1
    rw [z12, z13, z14, z15] at hd
    simpa using hd
  have k2 : Complex.normSq c02 = 1/4 := by
    have hd := h.d2
    rw [z12, z23, z24, z25] at hd
    simpa using hd
  have k3 : Complex.normSq c03 = 1/4 := by
    have hd := h.d3
    rw [z13, z23, z34, z35] at hd
    simpa using hd
  have k4 : Complex.normSq c04 = 1/4 := by
    have hd := h.d4
    rw [z14, z24, z34, z45] at hd
    simpa using hd
  have k5 : Complex.normSq c05 = 1/4 := by
    have hd := h.d5
    rw [z15, z25, z35, z45] at hd
    simpa using hd
  linarith [h.d0, k1, k2, k3, k4, k5]

/-! ## No vertex carries three active edges -/

/-- **The key lemma.**  If three edges at a vertex are all active the system
collapses: the complementary edge dies by `deg4`, and then either the odd
triangle isolates one of the two remaining vertices, or the vertex becomes
universal and the support is a star. -/
theorem key (h : Sys c01 c02 c03 c04 c05 c12 c13 c14 c15 c23 c24 c25 c34 c35 c45)
    (n1 : c01 ≠ 0) (n2 : c02 ≠ 0) (n3 : c03 ≠ 0) : False := by
  have e45 : c45 = 0 := mul4 (deg4 h) n1 n2 n3
  by_cases h04 : c04 = 0
  · -- vertex 4 is not joined to 0: the odd triangle kills its other edges
    have t1 : c14 * c02 + c24 * c01 = 0 := by linear_combination h.h0124 - c12 * h04
    have t2 : c14 * c03 + c34 * c01 = 0 := by linear_combination h.h0134 - c13 * h04
    have t3 : c24 * c03 + c34 * c02 = 0 := by linear_combination h.h0234 - c23 * h04
    have z34 : c34 = 0 := mul3 (tri t1 t2 t3) n1 n2
    have z24 : c24 = 0 := mul3 (tri t2 t1 (by linear_combination t3)) n1 n3
    have t4 : c24 * c01 + c14 * c02 = 0 := by linear_combination t1
    have z14 : c14 = 0 := mul3 (tri t3 t4 (by linear_combination t2)) n2 n3
    exact iso (swap01 (swap12 (swap23 (swap34 h)))) h04 z14 z24 z34 e45
  · -- vertex 0 also reaches 4
    have e35 : c35 = 0 := mul4 (deg4 (swap34 h)) n1 n2 h04
    have e25 : c25 = 0 := mul4 (deg4 (swap34 (swap23 h))) n1 n3 h04
    have e15 : c15 = 0 := mul4 (deg4 (swap34 (swap23 (swap12 h)))) n2 n3 h04
    by_cases h05 : c05 = 0
    · exact iso (swap01 (swap12 (swap23 (swap34 (swap45 h))))) h05 e15 e25 e35 e45
    · -- vertex 0 is universal, so every other edge dies and the support is a star
      have z34 : c34 = 0 := mul4 (deg4 (swap34 (swap45 h))) n1 n2 h05
      have z24 : c24 = 0 := mul4 (deg4 (swap34 (swap45 (swap23 h)))) n1 n3 h05
      have z14 : c14 = 0 := mul4 (deg4 (swap34 (swap45 (swap23 (swap12 h))))) n2 n3 h05
      have z23 : c23 = 0 := mul4 (deg4 (swap34 (swap45 (swap23 (swap34 h))))) n1 h04 h05
      have z13 : c13 = 0 := mul4 (deg4 (swap34 (swap45 (swap23 (swap34 (swap12 h)))))) n2 h04 h05
      have z12 : c12 = 0 := mul4 (deg4 (swap34 (swap45 (swap23 (swap34 (swap12 (swap23 h))))))) n3 h04 h05
      exact star h z12 z13 z14 e15 z23 z24 e25 z34 e35 e45

/-! ## Two disjoint active edges -/

/-- The four-cycle case: with `c01`, `c23`, `c02`, `c13` all active every
vertex of `{0,1,2,3}` already carries two edges, so `key` empties the eight
crossing edges, the two remaining vertices are joined, and the hafnian of
`{0,1,4,5}` is the single monomial `c01 * c45`. -/
theorem disjA (h : Sys c01 c02 c03 c04 c05 c12 c13 c14 c15 c23 c24 c25 c34 c35 c45)
    (n01 : c01 ≠ 0) (n23 : c23 ≠ 0) (n02 : c02 ≠ 0) (n13 : c13 ≠ 0) : False := by
  have z03 : c03 = 0 := by
    by_contra hx
    exact key (h) n01 n02 hx
  have z04 : c04 = 0 := by
    by_contra hx
    exact key (swap34 h) n01 n02 hx
  have z05 : c05 = 0 := by
    by_contra hx
    exact key (swap34 (swap45 h)) n01 n02 hx
  have z12 : c12 = 0 := by
    by_contra hx
    exact key (swap23 (swap01 h)) n01 n13 hx
  have z14 : c14 = 0 := by
    by_contra hx
    exact key (swap34 (swap23 (swap01 h))) n01 n13 hx
  have z15 : c15 = 0 := by
    by_contra hx
    exact key (swap34 (swap45 (swap23 (swap01 h)))) n01 n13 hx
  have z24 : c24 = 0 := by
    by_contra hx
    exact key (swap34 (swap23 (swap01 (swap12 h)))) n02 n23 hx
  have z25 : c25 = 0 := by
    by_contra hx
    exact key (swap34 (swap45 (swap23 (swap01 (swap12 h))))) n02 n23 hx
  have z34 : c34 = 0 := by
    by_contra hx
    exact key (swap34 (swap01 (swap12 (swap23 (swap12 (swap01 h)))))) n13 n23 hx
  have z35 : c35 = 0 := by
    by_contra hx
    exact key (swap34 (swap45 (swap01 (swap12 (swap23 (swap12 (swap01 h))))))) n13 n23 hx
  have n45 : c45 ≠ 0 := by
    intro hx
    exact iso (swap01 (swap12 (swap23 (swap34 h)))) z04 z14 z24 z34 hx
  have hz : c01 * c45 = 0 := by linear_combination h.h0145 - c15 * z04 - c14 * z05
  rcases mul_eq_zero.mp hz with hh | hh
  · exact n01 hh
  · exact n45 hh

/-- **Two disjoint active edges are impossible.**  The hafnian of their
four-set has to activate a second matching, and that is the four-cycle. -/
theorem disj (h : Sys c01 c02 c03 c04 c05 c12 c13 c14 c15 c23 c24 c25 c34 c35 c45)
    (n01 : c01 ≠ 0) (n23 : c23 ≠ 0) : False := by
  have hb : c02 * c13 ≠ 0 ∨ c03 * c12 ≠ 0 := by
    by_contra hc
    push_neg at hc
    obtain ⟨p, q⟩ := hc
    have hz : c01 * c23 = 0 := by linear_combination h.h0123 - p - q
    rcases mul_eq_zero.mp hz with hh | hh
    · exact n01 hh
    · exact n23 hh
  rcases hb with hm | hm
  · exact disjA h n01 n23 (left_ne_zero_of_mul hm) (right_ne_zero_of_mul hm)
  · exact disjA (swap23 h) n01 n23 (left_ne_zero_of_mul hm) (right_ne_zero_of_mul hm)

/-! ## The headline -/

/-- With one active edge at vertex `0` fixed, every way of not being isolated
at a second vertex either produces two disjoint active edges or three active
edges at one vertex. -/
theorem main1 (h : Sys c01 c02 c03 c04 c05 c12 c13 c14 c15 c23 c24 c25 c34 c35 c45) (n01 : c01 ≠ 0) : False := by
  by_cases n02 : c02 = 0
  · by_cases n12 : c12 = 0
    · by_cases n23 : c23 = 0
      · by_cases n24 : c24 = 0
        · by_cases n25 : c25 = 0
          · exact iso (swap01 (swap12 h)) n02 n12 n23 n24 n25
          · exact disj (swap34 (swap45 h)) n01 n25
        · exact disj (swap34 h) n01 n24
      · exact disj h n01 n23
    · by_cases m03 : c03 = 0
      · by_cases m13 : c13 = 0
        · by_cases m23 : c23 = 0
          · by_cases m34 : c34 = 0
            · by_cases m35 : c35 = 0
              · exact iso (swap01 (swap12 (swap23 h))) m03 m13 m23 m34 m35
              · exact disj (swap34 (swap45 (swap23 h))) n01 m35
            · exact disj (swap34 (swap23 h)) n01 m34
          · exact disj (h) n01 m23
        · exact key (swap01 h) n01 n12 m13
      · exact disj (swap12 (swap23 h)) m03 n12
  · by_cases m03 : c03 = 0
    · by_cases m13 : c13 = 0
      · by_cases m23 : c23 = 0
        · by_cases m34 : c34 = 0
          · by_cases m35 : c35 = 0
            · exact iso (swap01 (swap12 (swap23 h))) m03 m13 m23 m34 m35
            · exact disj (swap34 (swap45 (swap23 h))) n01 m35
          · exact disj (swap34 (swap23 h)) n01 m34
        · exact disj (h) n01 m23
      · exact disj (swap12 h) n02 m13
    · exact key h n01 n02 m03

/-- **The hafnian system has no fractional perfect matching.**  This is the
whole combinatorial content of the orbit 17 no-go. -/
theorem no_go (h : Sys c01 c02 c03 c04 c05 c12 c13 c14 c15 c23 c24 c25 c34 c35 c45) : False := by
  by_cases n01 : c01 = 0
  · by_cases n02 : c02 = 0
    · by_cases n03 : c03 = 0
      · by_cases n04 : c04 = 0
        · by_cases n05 : c05 = 0
          · exact iso h n01 n02 n03 n04 n05
          · exact main1 (swap12 (swap23 (swap34 (swap45 h)))) n05
        · exact main1 (swap12 (swap23 (swap34 h))) n04
      · exact main1 (swap12 (swap23 h)) n03
    · exact main1 (swap12 h) n02
  · exact main1 h n01

end

end SixQubit.Hafnian
