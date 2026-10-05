import Mathlib

/-!
# The table algebra behind the orbit 31 no-go

Orbit 31 (`a = (1,1,1,2,2,2)`, `q = 4`) has both fibers stabilised by the Klein
four-group on the last three qubits, so each splits into FOUR cosets of size
four.  The sixteen positions form a `4 x 4` table with rows `A, B_1, B_2, B_3`
and columns `e_0..e_3`.  The moment system pins `p_1(v-bar) = p_0(v)` at every
position, so each active position admits `d_{v-bar} = rho_v conj(c_v)` with
`|rho_v| = 1`. In each column with nonzero `A`, the twelve two-term relations
synchronize its active `B` phase ratios with the `A` ratio. Substituting turns
the Knill-Laflamme conditions into statements
about the four bottom columns, viewed as vectors in `C^3` (the `B` rows) plus the
`A` row.

`kernel_identity` is the engine.  Family one says the vector
`v_e = conj(rho_e) a_e` is annihilated by every `B` row, so

    0 = sum_i |(B v)_i|^2 = sum_{e,f} v_e conj(v_f) M_{ef},
    M_{ef} = sum_i b_{i,e} conj(b_{i,f}).

Family three (the diagonal conditions on the Klein masks) forces
`M_{ef} = conj(v_e) v_f` for every pair of columns with DIFFERENT phases, while
`M_{ee} = alpha_e + 1/8`.  Feeding those into the identity kills each branch of
the phase partition.

`all_distinct` is the branch where no two columns share a phase: the identity
evaluates to `3/32`.  `partition31` is the `(3,1)` branch in its covering-A
form, where the three same-phase columns have disjoint supports and the identity
becomes a sum of nonnegative reals plus `1/32`.

These elementary identities are used by `SixQubit.Orbit31`; the physical
distance-three no-go is `SixQubit.Orbit31.no_code` in `CodeOrbit31.lean`.
The current SI's support enumeration and representative certificates are in
`MainTheory.Orbit31*` and `MainTheory.Generated.Orbit31*`. Their individual
manuscript correspondence is tracked separately in the current claims ledger.
-/

namespace SixQubit.Table31

open scoped ComplexConjugate


/-- `z * star z` is the squared modulus. -/
theorem sq (z : ℂ) : z * star z = (Complex.normSq z : ℂ) := by
  rw [mul_comm, Complex.normSq_eq_conj_mul_self]; rfl

/-- The kernel identity.  Family one says the vector `v` is annihilated by each
row of the bottom block, so the Gram form of the columns against `v` vanishes. -/
theorem kernel_identity
    (b10 b11 b12 b13 b20 b21 b22 b23 b30 b31 b32 b33 : ℂ)
    (v0 v1 v2 v3 : ℂ)
    (h1 : b10 * v0 + b11 * v1 + b12 * v2 + b13 * v3 = 0)
    (h2 : b20 * v0 + b21 * v1 + b22 * v2 + b23 * v3 = 0)
    (h3 : b30 * v0 + b31 * v1 + b32 * v2 + b33 * v3 = 0)
    (M00 M01 M02 M03 M10 M11 M12 M13 M20 M21 M22 M23 M30 M31 M32 M33 : ℂ)
    (e00 : M00 = b10 * star b10 + b20 * star b20 + b30 * star b30)
    (e01 : M01 = b10 * star b11 + b20 * star b21 + b30 * star b31)
    (e02 : M02 = b10 * star b12 + b20 * star b22 + b30 * star b32)
    (e03 : M03 = b10 * star b13 + b20 * star b23 + b30 * star b33)
    (e10 : M10 = b11 * star b10 + b21 * star b20 + b31 * star b30)
    (e11 : M11 = b11 * star b11 + b21 * star b21 + b31 * star b31)
    (e12 : M12 = b11 * star b12 + b21 * star b22 + b31 * star b32)
    (e13 : M13 = b11 * star b13 + b21 * star b23 + b31 * star b33)
    (e20 : M20 = b12 * star b10 + b22 * star b20 + b32 * star b30)
    (e21 : M21 = b12 * star b11 + b22 * star b21 + b32 * star b31)
    (e22 : M22 = b12 * star b12 + b22 * star b22 + b32 * star b32)
    (e23 : M23 = b12 * star b13 + b22 * star b23 + b32 * star b33)
    (e30 : M30 = b13 * star b10 + b23 * star b20 + b33 * star b30)
    (e31 : M31 = b13 * star b11 + b23 * star b21 + b33 * star b31)
    (e32 : M32 = b13 * star b12 + b23 * star b22 + b33 * star b32)
    (e33 : M33 = b13 * star b13 + b23 * star b23 + b33 * star b33)
    : v0 * star v0 * M00 + v0 * star v1 * M01 + v0 * star v2 * M02 + v0 * star v3 * M03
    + v1 * star v0 * M10 + v1 * star v1 * M11 + v1 * star v2 * M12 + v1 * star v3 * M13
    + v2 * star v0 * M20 + v2 * star v1 * M21 + v2 * star v2 * M22 + v2 * star v3 * M23
    + v3 * star v0 * M30 + v3 * star v1 * M31 + v3 * star v2 * M32 + v3 * star v3 * M33
      = 0 := by
  have s1 := congrArg star h1
  have s2 := congrArg star h2
  have s3 := congrArg star h3
  simp only [star_add, star_mul', star_zero] at s1 s2 s3
  subst e00 e01 e02 e03 e10 e11 e12 e13 e20 e21 e22 e23 e30 e31 e32 e33
  linear_combination (star b10 * star v0 + star b11 * star v1 + star b12 * star v2
      + star b13 * star v3) * h1
    + (star b20 * star v0 + star b21 * star v1 + star b22 * star v2
      + star b23 * star v3) * h2
    + (star b30 * star v0 + star b31 * star v1 + star b32 * star v2
      + star b33 * star v3) * h3

/-- All four column phases distinct: every off-diagonal entry of the Gram matrix
is `conj(v_e) v_f`, and the kernel identity then evaluates to `3/32`. -/
theorem all_distinct (v0 v1 v2 v3 : ℂ)
    (hS : v0 * star v0 + v1 * star v1 + v2 * star v2 + v3 * star v3 = (1/4 : ℂ))
    (hid : v0 * star v0 * (v0 * star v0 + 1/8) + v0 * star v1 * (star v0 * v1) + v0 * star v2 * (star v0 * v2) + v0 * star v3 * (star v0 * v3)
    + v1 * star v0 * (star v1 * v0) + v1 * star v1 * (v1 * star v1 + 1/8) + v1 * star v2 * (star v1 * v2) + v1 * star v3 * (star v1 * v3)
    + v2 * star v0 * (star v2 * v0) + v2 * star v1 * (star v2 * v1) + v2 * star v2 * (v2 * star v2 + 1/8) + v2 * star v3 * (star v2 * v3)
    + v3 * star v0 * (star v3 * v0) + v3 * star v1 * (star v3 * v1) + v3 * star v2 * (star v3 * v2) + v3 * star v3 * (v3 * star v3 + 1/8)
      = 0) : False := by
  have hval : v0 * star v0 * (v0 * star v0 + 1/8) + v0 * star v1 * (star v0 * v1) + v0 * star v2 * (star v0 * v2) + v0 * star v3 * (star v0 * v3)
    + v1 * star v0 * (star v1 * v0) + v1 * star v1 * (v1 * star v1 + 1/8) + v1 * star v2 * (star v1 * v2) + v1 * star v3 * (star v1 * v3)
    + v2 * star v0 * (star v2 * v0) + v2 * star v1 * (star v2 * v1) + v2 * star v2 * (v2 * star v2 + 1/8) + v2 * star v3 * (star v2 * v3)
    + v3 * star v0 * (star v3 * v0) + v3 * star v1 * (star v3 * v1) + v3 * star v2 * (star v3 * v2) + v3 * star v3 * (v3 * star v3 + 1/8)
      = (3/32 : ℂ) := by
    linear_combination (v0 * star v0 + v1 * star v1 + v2 * star v2 + v3 * star v3
      + 3/8) * hS
  rw [hid] at hval
  norm_num at hval

/-- The `(3,1)` partition, covering A: the three same-phase columns have disjoint
supports, so their mutual Gram entries vanish and the identity becomes a sum of
nonnegative reals with a strictly positive constant. -/
theorem partition31 (a0 a1 a2 a3 : Real)
    (n0 : 0 ≤ a0) (n1 : 0 ≤ a1) (n2 : 0 ≤ a2) (n3 : 0 ≤ a3)
    (hS : a0 + a1 + a2 + a3 = 1/4)
    (hid : a0 * a0 + a1 * a1 + a2 * a2 + a3 * a3 + (1/8) * (a0 + a1 + a2 + a3)
      + 2 * a3 * (a0 + a1 + a2) = 0) : False := by
  nlinarith [sq_nonneg a0, sq_nonneg a1, sq_nonneg a2, sq_nonneg a3,
    mul_nonneg n3 (by linarith : (0:Real) ≤ a0 + a1 + a2)]

/-- The column relation.  Family one says `sum_e v_e X_e = 0` in `ℂ³`; pairing
against `X_f` gives one scalar equation per column. -/
theorem gram_eq (b0 b1 b2 : ℂ) (c0 c1 c2 : ℂ) (d0 d1 d2 : ℂ) (e0 e1 e2 : ℂ)
    (v0 v1 v2 v3 : ℂ) (f0 f1 f2 : ℂ)
    (h0 : b0 * v0 + c0 * v1 + d0 * v2 + e0 * v3 = 0)
    (h1 : b1 * v0 + c1 * v1 + d1 * v2 + e1 * v3 = 0)
    (h2 : b2 * v0 + c2 * v1 + d2 * v2 + e2 * v3 = 0)
    : v0 * (b0 * star f0 + b1 * star f1 + b2 * star f2)
    + v1 * (c0 * star f0 + c1 * star f1 + c2 * star f2)
    + v2 * (d0 * star f0 + d1 * star f1 + d2 * star f2)
    + v3 * (e0 * star f0 + e1 * star f1 + e2 * star f2) = 0 := by
  linear_combination (star f0) * h0 + (star f1) * h1 + (star f2) * h2

/-- A column that is alone in its phase class is killed outright: its equation
reduces to `(3/8) v_f = 0`. -/
theorem lone_column (vf : ℂ) (af S : Real) (hS : S = 1/4)
    (h : vf * ((af : ℂ) + 1/8 + ((S : ℂ) - (af : ℂ))) = 0) : vf = 0 := by
  have h3 : vf * ((3/8 : ℂ)) = 0 := by rw [hS] at h; push_cast at h ⊢; linear_combination h
  rcases mul_eq_zero.mp h3 with h | h
  · exact h
  · norm_num at h

/-- A two-column class forces its `2 x 2` system to be singular, hence
Cauchy-Schwarz to be tight. -/
theorem pair_class (v0 v1 M01 M10 : ℂ) (a0 a1 s : Real)
    (hv : ¬ (v0 = 0 ∧ v1 = 0))
    (h0 : v0 * ((a0 : ℂ) + 1/8 + ((1/4 : ℂ) - (s : ℂ))) + v1 * M10 = 0)
    (h1 : v1 * ((a1 : ℂ) + 1/8 + ((1/4 : ℂ) - (s : ℂ))) + v0 * M01 = 0)
    : ((a0 : ℂ) + 1/8 + (1/4 - (s : ℂ))) * ((a1 : ℂ) + 1/8 + (1/4 - (s : ℂ)))
      = M01 * M10 := by
  by_cases hz : v0 = 0
  · have hv1 : v1 ≠ 0 := by
      intro h; exact hv ⟨hz, h⟩
    rw [hz] at h0 h1
    simp only [zero_mul, zero_add, add_zero] at h0 h1
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hv1
    · rw [h]; rcases mul_eq_zero.mp h1 with g | g
      · exact absurd g hv1
      · rw [g]; ring
  · have key : v0 * (((a0 : ℂ) + 1/8 + (1/4 - (s : ℂ)))
        * ((a1 : ℂ) + 1/8 + (1/4 - (s : ℂ))) - M01 * M10) = 0 := by
      linear_combination ((a1 : ℂ) + 1/8 + (1/4 - (s : ℂ))) * h0 - M10 * h1
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h hz
    · linear_combination h

/-- The `(2,2)` gap: with `s = a0 + a1 <= 1/4` the singular determinant beats the
Cauchy-Schwarz bound unless `s = 1/4`. -/
theorem pair_gap (a0 a1 s : Real) (hs : s = a0 + a1)
    : (a0 + 1/8 + (1/4 - s)) * (a1 + 1/8 + (1/4 - s))
      - (a0 + 1/8) * (a1 + 1/8) = 1/8 - s/2 := by
  rw [hs]; ring

/-- Tight Cauchy-Schwarz together with the vanishing permanent puts both columns
on a single row, whose budget they then exceed.

`p i` and `q i` are the squared moduli in the two columns; `p i * q j = 0` for
`i != j` is what the two conditions give jointly. -/
theorem tight_pair (p0 p1 p2 q0 q1 q2 A B : Real)
    (_np0 : 0 ≤ p0) (_np1 : 0 ≤ p1) (_np2 : 0 ≤ p2)
    (_nq0 : 0 ≤ q0) (_nq1 : 0 ≤ q1) (_nq2 : 0 ≤ q2)
    (z01 : p0 * q1 = 0) (z02 : p0 * q2 = 0)
    (z10 : p1 * q0 = 0) (z12 : p1 * q2 = 0)
    (z20 : p2 * q0 = 0) (z21 : p2 * q1 = 0)
    (hA : p0 + p1 + p2 = A) (hB : q0 + q1 + q2 = B)
    (hApos : 0 < A) (hBpos : 0 < B)
    (r0 : p0 + q0 ≤ 1/4) (r1 : p1 + q1 ≤ 1/4) (r2 : p2 + q2 ≤ 1/4)
    : A + B ≤ 1/4 := by
  have hp : p0 ≠ 0 ∨ p1 ≠ 0 ∨ p2 ≠ 0 := by
    by_contra h
    push_neg at h
    obtain ⟨e0, e1, e2⟩ := h
    rw [e0, e1, e2] at hA; simp at hA; linarith
  rcases hp with h | h | h
  · have q1z : q1 = 0 := by rcases mul_eq_zero.mp z01 with g | g; exact absurd g h; exact g
    have q2z : q2 = 0 := by rcases mul_eq_zero.mp z02 with g | g; exact absurd g h; exact g
    have q0p : q0 ≠ 0 := by
      intro g; rw [g, q1z, q2z] at hB; simp at hB; linarith
    have p1z : p1 = 0 := by rcases mul_eq_zero.mp z10 with g | g; exact g; exact absurd g q0p
    have p2z : p2 = 0 := by rcases mul_eq_zero.mp z20 with g | g; exact g; exact absurd g q0p
    rw [p1z, p2z] at hA; rw [q1z, q2z] at hB; linarith
  · have q0z : q0 = 0 := by rcases mul_eq_zero.mp z10 with g | g; exact absurd g h; exact g
    have q2z : q2 = 0 := by rcases mul_eq_zero.mp z12 with g | g; exact absurd g h; exact g
    have q1p : q1 ≠ 0 := by
      intro g; rw [g, q0z, q2z] at hB; simp at hB; linarith
    have p0z : p0 = 0 := by rcases mul_eq_zero.mp z01 with g | g; exact g; exact absurd g q1p
    have p2z : p2 = 0 := by rcases mul_eq_zero.mp z21 with g | g; exact g; exact absurd g q1p
    rw [p0z, p2z] at hA; rw [q0z, q2z] at hB; linarith
  · have q0z : q0 = 0 := by rcases mul_eq_zero.mp z20 with g | g; exact absurd g h; exact g
    have q1z : q1 = 0 := by rcases mul_eq_zero.mp z21 with g | g; exact absurd g h; exact g
    have q2p : q2 ≠ 0 := by
      intro g; rw [g, q0z, q1z] at hB; simp at hB; linarith
    have p0z : p0 = 0 := by rcases mul_eq_zero.mp z02 with g | g; exact g; exact absurd g q2p
    have p1z : p1 = 0 := by rcases mul_eq_zero.mp z12 with g | g; exact g; exact absurd g q2p
    rw [p0z, p1z] at hA; rw [q0z, q1z] at hB; linarith

/-- Vanishing determinant and vanishing permanent together kill each product. -/
theorem det_perm_zero (x y z w : ℂ)
    (hd : x * w - y * z = 0) (hp : x * w + y * z = 0)
    : x * w = 0 ∧ y * z = 0 := by
  constructor
  · linear_combination (1/2 : ℂ) * hd + (1/2 : ℂ) * hp
  · linear_combination (1/2 : ℂ) * hp - (1/2 : ℂ) * hd

/-- Three vanishing permanents on one row pair, over three distinct columns,
give a vanishing triple product.  Division-free. -/
theorem perm_triple (be bf bg se sf sg : ℂ)
    (pef : be * sf + bf * se = 0)
    (peg : be * sg + bg * se = 0)
    (pfg : bf * sg + bg * sf = 0)
    : bf * bg * se = 0 := by
  have key : (-2 : ℂ) * (bf * bg * se) = 0 := by
    linear_combination be * pfg - bf * peg - bg * pef
  rcases mul_eq_zero.mp key with h | h
  · norm_num at h
  · exact h

/-- If a row pair has one row nonzero at a column where the other vanishes, the
other row vanishes everywhere. -/
theorem perm_support (be bf se sf : ℂ) (hbe : be ≠ 0) (hse : se = 0)
    (pef : be * sf + bf * se = 0) : sf = 0 := by
  rw [hse, mul_zero, add_zero] at pef
  rcases mul_eq_zero.mp pef with h | h
  · exact absurd h hbe
  · exact h

/-! ## Bridging the transcription to the algebra -/

/-- Conjugating a four-term vanishing sum.  Family one arrives as
`sum_e star(b_e) * dA_e = 0`; the algebra wants `sum_e b_e * star(dA_e) = 0`,
and `v_e = star(dA_e)`. -/
theorem conj4 (b0 b1 b2 b3 x0 x1 x2 x3 : ℂ)
    (h : star b0 * x0 + star b1 * x1 + star b2 * x2 + star b3 * x3 = 0)
    : b0 * star x0 + b1 * star x1 + b2 * star x2 + b3 * star x3 = 0 := by
  have h2 := congrArg star h
  simp only [star_add, star_mul', star_star, star_zero] at h2
  linear_combination h2

/-- Two columns share a phase exactly when this division-free product is
symmetric; this is the test the branch split runs on. -/
def SamePhase (ve af vf ae : ℂ) : Prop := ve * af = vf * ae

/-- The squared modulus of the kernel entry equals that of the `A` amplitude,
because the moment system pairs the two fibers position by position. -/
theorem kernel_norm (a v : ℂ) (al : Real)
    (hv : Complex.normSq v = al) (ha : Complex.normSq a = al)
    : v * star v = a * star a := by
  rw [sq, sq, hv, ha]

/-- A vanishing kernel entry forces its `A` amplitude to vanish too. -/
theorem kernel_zero (a v : ℂ) (al : Real)
    (hv : Complex.normSq v = al) (ha : Complex.normSq a = al) (h : v = 0)
    : Complex.normSq a = 0 := by
  rw [ha, ← hv, h]; simp

/-!
# Orbit 31, family three: a division-free pin for `M_ef = conj (v_e) * v_f`

Everything below is stated over `ℂ` with `star`, and every hypothesis and
conclusion is **polynomial**: no `rho`, no inverses, no nonvanishing side
conditions except in the final extraction corollaries.

Notation.  For the column pair `{e, f}` of the 4x4 orbit-31 table:

* `ae`, `af`            bottom amplitudes at the `A` row of columns `e`, `f`;
* `be1 be2 be3`         bottom amplitudes at the `B` rows of column `e`;
* `bf1 bf2 bf3`         bottom amplitudes at the `B` rows of column `f`;
* `ve`, `vf`            `conj (d at the complement of A_e)`, resp. of `A_f`;
* `ue1 ue2 ue3`         `conj (d at the complement of B_{i,e})`;
* `uf1 uf2 uf3`         likewise for column `f`;
* `M_ef = be1 * star bf1 + be2 * star bf2 + be3 * star bf3`  the `B`-column Gram.

The chain is
`row_key`  (fully general, one row of each column chosen)
  -> `key_of_raw` (the `A` rows)  -> `M_eq_of_raw`,
and separately the already-cleared `(a, v, M)`-only form `key` -> `M_eq`,
linked to the raw form by `hH3_of_raw`.
-/



/-! ## 1.  The general identity, one bottom row chosen in each column -/

/-- **The family-three identity.**

`p, q` are the bottom and top amplitude at *any* chosen position of column `e`
(so `(p, q) = (ae, ve)` on the `A` row and `(p, q) = (be i, ue i)` on a `B` row),
and `p', q'` likewise for column `f`.

Hypotheses, all division free:

* `hFam` : the raw family-three relation for the pair `{e, f}` — "b-Gram plus
  conjugate a-Gram equals u-Gram plus conjugate v-Gram";
* `hColE i`, `hColF i` : the column relations (`rho` constant along a column) in
  cross-multiplied form, anchored at the chosen position;
* `hPe`, `hPf` : the phase-transfer facts at the chosen positions.  On the `A`
  rows these are literally the moment facts `|v| = |a|`.

The conclusion carries the factor `q * star q' - p * star p'` and is
**unconditionally true**; it degenerates to `0 = 0` exactly when that factor
vanishes, which is where `M_ef` genuinely is not determined. -/
theorem row_key
    (ae af ve vf p q p' q' be1 be2 be3 bf1 bf2 bf3 ue1 ue2 ue3 uf1 uf2 uf3 : ℂ)
    (hFam : (be1 * star bf1 + be2 * star bf2 + be3 * star bf3) + star ae * af
              = (ue1 * star uf1 + ue2 * star uf2 + ue3 * star uf3) + star ve * vf)
    (hColE1 : ue1 * p = q * be1)
    (hColE2 : ue2 * p = q * be2)
    (hColE3 : ue3 * p = q * be3)
    (hColF1 : uf1 * p' = q' * bf1)
    (hColF2 : uf2 * p' = q' * bf2)
    (hColF3 : uf3 * p' = q' * bf3)
    (hPe : star ve * q = star ae * p)
    (hPf : vf * star q' = af * star p') :
    ((be1 * star bf1 + be2 * star bf2 + be3 * star bf3) - star ve * vf)
      * (q * star q' - p * star p') = 0 := by
  have hC1 : star uf1 * star p' = star q' * star bf1 := by
    rw [← star_mul', ← star_mul', hColF1]
  have hC2 : star uf2 * star p' = star q' * star bf2 := by
    rw [← star_mul', ← star_mul', hColF2]
  have hC3 : star uf3 * star p' = star q' * star bf3 := by
    rw [← star_mul', ← star_mul', hColF3]
  linear_combination
    (-(p * star p')) * hFam
      - (star bf1 * star q') * hColE1 - (star bf2 * star q') * hColE2
      - (star bf3 * star q') * hColE3
      - (ue1 * p) * hC1 - (ue2 * p) * hC2 - (ue3 * p) * hC3
      - (star ae * p) * hPf - (vf * star q') * hPe

/-! ## 2.  The `A`-row specialisation -/

/-- The `A`-row case of `row_key`.  Here the phase-transfer hypotheses are
exactly the verified moment facts `p_1 (v-bar) = p_0 (v)` at `A_e` and `A_f`,
stated multiplicatively so that they stay division free. -/
theorem key_of_raw
    (ae af ve vf be1 be2 be3 bf1 bf2 bf3 ue1 ue2 ue3 uf1 uf2 uf3 : ℂ)
    (hFam : (be1 * star bf1 + be2 * star bf2 + be3 * star bf3) + star ae * af
              = (ue1 * star uf1 + ue2 * star uf2 + ue3 * star uf3) + star ve * vf)
    (hColE1 : ue1 * ae = ve * be1)
    (hColE2 : ue2 * ae = ve * be2)
    (hColE3 : ue3 * ae = ve * be3)
    (hColF1 : uf1 * af = vf * bf1)
    (hColF2 : uf2 * af = vf * bf2)
    (hColF3 : uf3 * af = vf * bf3)
    (hKe : ve * star ve = ae * star ae)
    (hKf : vf * star vf = af * star af) :
    ((be1 * star bf1 + be2 * star bf2 + be3 * star bf3) - star ve * vf)
      * (ve * star vf - ae * star af) = 0 :=
  row_key ae af ve vf ae ve af vf be1 be2 be3 bf1 bf2 bf3 ue1 ue2 ue3 uf1 uf2 uf3
    hFam hColE1 hColE2 hColE3 hColF1 hColF2 hColF3
    (by linear_combination hKe) hKf

/-- Extraction of `M_ef` from the `A`-row identity.  The single division-free
side condition `ve * star vf ≠ ae * star af` packages all three nondegeneracy
requirements at once: `ae ≠ 0`, `af ≠ 0` and `rho_e ≠ rho_f`. -/
theorem M_eq_of_raw
    (ae af ve vf be1 be2 be3 bf1 bf2 bf3 ue1 ue2 ue3 uf1 uf2 uf3 : ℂ)
    (hFam : (be1 * star bf1 + be2 * star bf2 + be3 * star bf3) + star ae * af
              = (ue1 * star uf1 + ue2 * star uf2 + ue3 * star uf3) + star ve * vf)
    (hColE1 : ue1 * ae = ve * be1)
    (hColE2 : ue2 * ae = ve * be2)
    (hColE3 : ue3 * ae = ve * be3)
    (hColF1 : uf1 * af = vf * bf1)
    (hColF2 : uf2 * af = vf * bf2)
    (hColF3 : uf3 * af = vf * bf3)
    (hKe : ve * star ve = ae * star ae)
    (hKf : vf * star vf = af * star af)
    (hT : ve * star vf - ae * star af ≠ 0) :
    be1 * star bf1 + be2 * star bf2 + be3 * star bf3 = star ve * vf := by
  rcases mul_eq_zero.mp
      (key_of_raw ae af ve vf be1 be2 be3 bf1 bf2 bf3 ue1 ue2 ue3 uf1 uf2 uf3
        hFam hColE1 hColE2 hColE3 hColF1 hColF2 hColF3 hKe hKf) with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hT

/-! ## 3.  The `(a, v, M)`-only form, and the bridge to it -/

/-- The bridge: the raw family-three relation together with the column
relations already implies the *cleared* relation `hH3`, which is the original
`M_ef * t_ef = - star (N_ef * t_ef)` multiplied through by `N_ef = ae * star af`.
No moment fact and no nonvanishing hypothesis is needed here. -/
theorem hH3_of_raw
    (ae af ve vf be1 be2 be3 bf1 bf2 bf3 ue1 ue2 ue3 uf1 uf2 uf3 : ℂ)
    (hFam : (be1 * star bf1 + be2 * star bf2 + be3 * star bf3) + star ae * af
              = (ue1 * star uf1 + ue2 * star uf2 + ue3 * star uf3) + star ve * vf)
    (hColE1 : ue1 * ae = ve * be1)
    (hColE2 : ue2 * ae = ve * be2)
    (hColE3 : ue3 * ae = ve * be3)
    (hColF1 : uf1 * af = vf * bf1)
    (hColF2 : uf2 * af = vf * bf2)
    (hColF3 : uf3 * af = vf * bf3) :
    (be1 * star bf1 + be2 * star bf2 + be3 * star bf3)
        * (star vf * ve - star af * ae)
      = -(ae * star af) * (vf * star ve - af * star ae) := by
  have hC1 : star uf1 * star af = star vf * star bf1 := by
    rw [← star_mul', ← star_mul', hColF1]
  have hC2 : star uf2 * star af = star vf * star bf2 := by
    rw [← star_mul', ← star_mul', hColF2]
  have hC3 : star uf3 * star af = star vf * star bf3 := by
    rw [← star_mul', ← star_mul', hColF3]
  linear_combination
    (-(ae * star af)) * hFam
      - (star bf1 * star vf) * hColE1 - (star bf2 * star vf) * hColE2
      - (star bf3 * star vf) * hColE3
      - (ue1 * ae) * hC1 - (ue2 * ae) * hC2 - (ue3 * ae) * hC3

/-- **The `(a, v, M)`-only identity.**  Division free: no `rho`, no inverses,
no side conditions.  `star vf * ve - star af * ae` is the division-free stand-in
for `t_ef * star af * ae`. -/
theorem key (ae af ve vf M : ℂ)
    (hKe : ve * star ve = ae * star ae)
    (hKf : vf * star vf = af * star af)
    (hH3 : M * (star vf * ve - star af * ae)
             = -(ae * star af) * (vf * star ve - af * star ae)) :
    (M - star ve * vf) * (star vf * ve - star af * ae) = 0 := by
  linear_combination hH3 - (star vf * vf) * hKe - (ae * star ae) * hKf

/-- The usable corollary of `key`. -/
theorem M_eq (ae af ve vf M : ℂ)
    (hKe : ve * star ve = ae * star ae)
    (hKf : vf * star vf = af * star af)
    (hH3 : M * (star vf * ve - star af * ae)
             = -(ae * star af) * (vf * star ve - af * star ae))
    (hT : star vf * ve - star af * ae ≠ 0) :
    M = star ve * vf := by
  rcases mul_eq_zero.mp (key ae af ve vf M hKe hKf hH3) with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hT

/-! ## 4.  Phase transfer, which feeds `row_key` on a `B` row -/

/-- On a `B` row the phase-transfer hypothesis of `row_key` is itself a
consequence of that row's column relation and moment fact, provided the bottom
amplitude there is nonzero.  This is what rescues the `ae = 0` branch, at the
price of assuming `b ≠ 0` instead. -/
theorem phase_transfer (ae ve b u : ℂ)
    (hCol : u * ae = ve * b)
    (hMom : u * star u = b * star b)
    (hb : b ≠ 0) :
    star ve * u = star ae * b := by
  have hCb : star u * star ae = star ve * star b := by
    rw [← star_mul', ← star_mul', hCol]
  have h : (star ve * u - star ae * b) * star b = 0 := by
    linear_combination (-u) * hCb + (star ae) * hMom
  rcases mul_eq_zero.mp h with h' | h'
  · exact sub_eq_zero.mp h'
  · exact absurd (star_eq_zero.mp h') hb

/-! ## 5.  The degenerate branches -/

/-- If `ae = 0` then the moment fact forces the whole `A`-row factor to vanish,
so the `A`-row identity is vacuous and `M_ef` is genuinely undetermined by it. -/
theorem T_eq_zero_of_ae (ae af ve vf : ℂ) (h0 : ae = 0)
    (hKe : ve * star ve = ae * star ae) :
    star vf * ve - star af * ae = 0 := by
  have hv : ve = 0 := by
    rcases mul_eq_zero.mp (by rw [hKe, h0]; ring : ve * star ve = 0) with h | h
    · exact h
    · exact star_eq_zero.mp h
  rw [hv, h0]; simp

/-- Symmetrically for `af = 0`. -/
theorem T_eq_zero_of_af (ae af ve vf : ℂ) (h0 : af = 0)
    (hKf : vf * star vf = af * star af) :
    star vf * ve - star af * ae = 0 := by
  have hv : vf = 0 := by
    rcases mul_eq_zero.mp (by rw [hKf, h0]; ring : vf * star vf = 0) with h | h
    · exact h
    · exact star_eq_zero.mp h
  rw [hv, h0]; simp

end SixQubit.Table31
