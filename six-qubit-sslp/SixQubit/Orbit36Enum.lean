import Mathlib

import SS.FullKL
import SS.HilbertKL
import SixQubit.Common
import SixQubit.K4Kernel
import SixQubit.Orbit36
import SixQubit.Orbit36Phase

/-!
# The unique Shor--Laflamme weight enumerator of orbit 36

`SixQubit.Orbit36` forces every magnitude of an exact orbit-36 solution and
`SixQubit.Orbit36Phase` forces the six edge phases into the unique proper
three-edge-colouring of `K_4`.  This module closes the chapter: it evaluates the
Shor--Laflamme coefficients

    A_j = (1/4) * sum over weight-j Paulis of |Tr (E Pi)|^2

for `j = 0, 1, 2, 3` on an *arbitrary* exact orbit-36 solution -- not only on the
canonical representative -- and combines them with the MacWilliams normal form
into the unique enumerator

    (A_0, ..., A_6) = (1, 0, 21/25, 0, 291/25, 384/25, 79/25).

## How each coefficient is obtained

*The top word is a mirror of the bottom word.*  `top_form` produces a single unit
phase `tau` with

    d z0 = tau * conj (c y0),    d z1 = tau * conj (c y1),
    d zk = -(tau * conj (c yk))  for the four vertex and six edge amplitudes.

That is the chapter's antiunitary `Theta = Z_5 Z_6 X^{(x)6} K`, read off from the
four `X_i X_5` rows, the `X_1 X_6` row and the `X_i Z_j` pair relations.  Because
`|tau| = 1` every top expectation mirrors the bottom one, and the `+`/`-` pattern
is exactly the chapter's sign `epsilon(E)`.

*`A_0 = 1` and `A_1 = 0`* need only the moment data.

*`A_2 = 21/25`.*  Only eight flip masks join two points of a fiber: the trivial
mask, the six `K_4` edge masks on the first four qubits, and `{5,6}`.  The
trivial mask contributes the fifteen `Z_i Z_j` scalars, which the forced
magnitudes evaluate outright.  Each remaining mask carries four dressings whose
projector traces are `+-2 (G + conj G)` and `+-2 (G - conj G)` for a single
complex number `G`, so that mask contributes `32 * normSq G`.  For the edge mask
on `{V, W}` the colouring forces `3 G = conj (r_W) * r_V`, hence
`normSq G = 1/900`; for `{5,6}`, `G = conj b * a` and `normSq G = 1/100`.  The
fifteen diagonal scalars together with `6 * 32/900 + 32/100` give `84/25`, and
`A_2` is a quarter of that.

The individual weight-two scalars of the chapter's table are *not* invariant on
the orbit -- a local diagonal unitary rotates `X_i` into `Y_i` -- but the sum of
their squares over each mask is, and that is what is proved here.

*`A_3 = 0`.*  Sixteen weight-three masks have incidences.  Twelve pair a
last-coordinate anchor with an edge; there the two amplitudes carry opposite
`Theta`-signs, so the top pair is the negative of the bottom pair and the four
terms cancel (`twoSum`).  The remaining four are the chapter's exceptional masks
`f = {i,5,6}`, whose three incidences carry a common Walsh sign on each side; the
bracket is then the sum of the three edge phases of the triangle opposite `i`,
which `Orbit36Phase.triangle_sum` kills (`sixSum`).

Every headline theorem below obeys the discipline of the rest of the chapter: its
hypotheses are the two support conditions, one `MomentSystem`, and vanishing
Knill--Laflamme rows -- twenty-two of them, the twenty-one of
`Orbit36.magnitudes_forced` together with the `X_1 X_6` row.
-/

namespace SixQubit.Orbit36Enum

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

open SixQubit.K4Kernel (rho rho_quadratic rho_pow_three)
open SixQubit.Orbit36
open SixQubit.Orbit36Phase

set_option maxRecDepth 40000

/-! ## 1.  Elementary helpers -/

/-- The Pauli prefactor `i^{#Y}` is a unit, so it never changes a modulus.  This
is why no `numY` is ever computed below. -/
theorem normSq_I_pow_mul (k : ℕ) (t : ℂ) :
    Complex.normSq (Complex.I ^ k * t) = Complex.normSq t := by
  rw [map_mul, map_pow, Complex.normSq_I, one_pow, one_mul]

theorem normSq_two_mul (t : ℂ) : Complex.normSq (2 * t) = 4 * Complex.normSq t := by
  rw [map_mul]
  norm_num [Complex.normSq_apply]

theorem normSq_star (t : ℂ) : Complex.normSq (star t) = Complex.normSq t := by
  simp

theorem signC_neg (b : Bool) (t : ℂ) : SS.signC b (-t) = -SS.signC b t := by
  cases b <;> simp

/-- **The real/imaginary split.**  `t + conj t` and `t - conj t` carry the two
real degrees of freedom of `t`. -/
theorem normSq_split (t : ℂ) :
    Complex.normSq (t + star t) + Complex.normSq (t - star t) = 4 * Complex.normSq t := by
  simp only [Complex.star_def, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  ring

theorem signC_not (b : Bool) (t : ℂ) : SS.signC (!b) t = -SS.signC b t := by
  cases b <;> simp

/-- **The triangle cancellation.**  Three incidences whose bottom Walsh signs
agree and whose top Walsh signs agree collapse onto the two triangle sums. -/
theorem sixSum (b1 b2 : Bool) {X1 X2 X3 Y1 Y2 Y3 : ℂ}
    (hX : X1 + X2 + X3 = 0) (hY : Y1 + Y2 + Y3 = 0) :
    SS.signC b1 X1 + SS.signC b2 Y1 + SS.signC b1 X2 + SS.signC b2 Y2
      + SS.signC b1 X3 + SS.signC b2 Y3 = 0 := by
  cases b1 <;> cases b2 <;> simp only [SS.signC_true, SS.signC_false]
  · linear_combination hX + hY
  · linear_combination hX - hY
  · linear_combination -hX + hY
  · linear_combination -hX - hY

/-! ## 2.  The cube roots of unity as phases -/

/-- `rho` is a unit, so conjugation is inversion: `conj rho = rho^2`. -/
theorem star_rho : star rho = rho ^ 2 := by
  have h : star rho = -1 - rho := by
    rw [rho]
    simp only [Complex.star_def, map_div₀, map_add, map_neg, map_one, map_mul,
      Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    ring
  linear_combination h - rho_quadratic

/-- The other primitive cube root satisfies the same two identities, which is why
both branches of the colouring disjunction share every proof below. -/
theorem star_rho_sq : star (rho ^ 2) = (rho ^ 2) ^ 2 := by
  rw [star_pow, star_rho]

theorem rho_sq_quadratic : (rho ^ 2) ^ 2 + rho ^ 2 + 1 = 0 := by
  linear_combination rho * rho_pow_three + rho_quadratic

/-- Two different colours of the three-edge-colouring pair up to `-1`.  This is
the only place the colouring enters the weight-two count. -/
theorem colourPair_01 {w mu : ℂ} (hw : w ^ 2 + w + 1 = 0) (hs : star w = w ^ 2) :
    star mu * (w * mu) + star (w * mu) * mu = -(star mu * mu) := by
  simp only [star_mul']
  linear_combination (star mu * mu) * hs + (star mu * mu) * hw

theorem colourPair_02 {w mu : ℂ} (hw : w ^ 2 + w + 1 = 0) (hs : star w = w ^ 2) :
    star mu * (w ^ 2 * mu) + star (w ^ 2 * mu) * mu = -(star mu * mu) := by
  have h3 : w ^ 3 = 1 := by linear_combination (w - 1) * hw
  simp only [star_mul', star_pow]
  linear_combination (star mu * mu * (star w + w ^ 2)) * hs + (star mu * mu * w) * h3
    + (star mu * mu) * hw

theorem colourPair_12 {w mu : ℂ} (hw : w ^ 2 + w + 1 = 0) (hs : star w = w ^ 2) :
    star (w * mu) * (w ^ 2 * mu) + star (w ^ 2 * mu) * (w * mu) = -(star mu * mu) := by
  have h3 : w ^ 3 = 1 := by linear_combination (w - 1) * hw
  simp only [star_mul', star_pow]
  linear_combination (star mu * mu * (w ^ 2 + w * star w + w ^ 3)) * hs
    + (star mu * mu * (w + w ^ 2)) * h3 + (star mu * mu) * hw

/-! ## 3.  The weight-two identity on a `K_4` edge -/

/-- **`3 G = conj (r_W) r_V`.**  For the flip mask joining the two vertices `V, W`
of `K_4` the three incidence pairs contribute

    G = conj (r_W) r_V + conj (c_VK) c_WK + conj (c_VL) c_WL,

and the two cross terms are a common factor times the two colours of the edge
colouring other than the colour of `VW`.  Their sum is `-1/1500`, which pins `G`
to a third of the vertex term.  Division-free: the identity is multiplied through
by `conj (r_V) r_W`. -/
theorem edge_G {rV rW rK rL cVK cWK cVL cWL : ℂ}
    (pV : Complex.normSq rV = 1/10) (pW : Complex.normSq rW = 1/10)
    (pK : Complex.normSq rK = 1/10) (pL : Complex.normSq rL = 1/10)
    (hcross : star (rV * rK * cVK) * (rW * rK * cWK)
        + star (rV * rL * cVL) * (rW * rL * cWL) = -(1/1500 : ℂ))
    (hV : rV ≠ 0) (hW : rW ≠ 0) :
    3 * (star rW * rV + star cVK * cWK + star cVL * cWL) = star rW * rV := by
  have uV : star rV * rV = (1/10 : ℂ) := by rw [SixQubit.star_mul_self, pV]; norm_num
  have uW : star rW * rW = (1/10 : ℂ) := by rw [SixQubit.star_mul_self, pW]; norm_num
  have uK : star rK * rK = (1/10 : ℂ) := by rw [SixQubit.star_mul_self, pK]; norm_num
  have uL : star rL * rL = (1/10 : ℂ) := by rw [SixQubit.star_mul_self, pL]; norm_num
  simp only [star_mul'] at hcross
  have hPQ : (star rV * rW) * (star cVK * cWK + star cVL * cWL) = -(1/150 : ℂ) := by
    linear_combination 10 * hcross
      - (10 * (star rV * rW) * (star cVK * cWK)) * uK
      - (10 * (star rV * rW) * (star cVL * cWL)) * uL
  have key : (star rV * rW)
      * (3 * (star rW * rV + star cVK * cWK + star cVL * cWL) - star rW * rV) = 0 := by
    linear_combination 3 * hPQ + (2 * (star rW * rW)) * uV + ((1 : ℂ)/5) * uW
  have hne : star rV * rW ≠ 0 := mul_ne_zero (star_ne_zero.mpr hV) hW
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hne)

/-- `normSq G = 1/900` whenever `3 G` is a product of two amplitudes of modulus
squared `1/10`. -/
theorem normSq_of_triple {G t : ℂ} (h : 3 * G = t) (ht : Complex.normSq t = 1/100) :
    Complex.normSq G = 1/900 := by
  have h9 : (9 : ℝ) * Complex.normSq G = 1/100 := by
    rw [← ht, ← h, map_mul]
    norm_num [Complex.normSq_apply]
  linarith

/-! ## 4.  The six weight-two moduli, from the edge colouring -/

/-- **Every `K_4` edge mask has `normSq G = 1/900`.**  Stated for an abstract
primitive cube root `w`, so that it applies verbatim to both branches of the
colouring disjunction of `Orbit36Phase.phase_rigidity`. -/
theorem edges_of_colouring {r1 r2 r3 r4 c12 c13 c14 c23 c24 c34 mu w : ℂ}
    (hw : w ^ 2 + w + 1 = 0) (hs : star w = w ^ 2)
    (p1 : Complex.normSq r1 = 1/10) (p2 : Complex.normSq r2 = 1/10)
    (p3 : Complex.normSq r3 = 1/10) (p4 : Complex.normSq r4 = 1/10)
    (hmu : Complex.normSq mu = 1/1500)
    (n1 : r1 ≠ 0) (n2 : r2 ≠ 0) (n3 : r3 ≠ 0) (n4 : r4 ≠ 0)
    (h12 : r1 * r2 * c12 = mu) (h34 : r3 * r4 * c34 = mu)
    (h13 : r1 * r3 * c13 = w * mu) (h24 : r2 * r4 * c24 = w * mu)
    (h14 : r1 * r4 * c14 = w ^ 2 * mu) (h23 : r2 * r3 * c23 = w ^ 2 * mu) :
    Complex.normSq (star r2 * r1 + star c13 * c23 + star c14 * c24) = 1/900
      ∧ Complex.normSq (star r3 * r1 + star c12 * c23 + star c14 * c34) = 1/900
      ∧ Complex.normSq (star r4 * r1 + star c12 * c24 + star c13 * c34) = 1/900
      ∧ Complex.normSq (star r3 * r2 + star c12 * c13 + star c24 * c34) = 1/900
      ∧ Complex.normSq (star r4 * r2 + star c12 * c14 + star c23 * c34) = 1/900
      ∧ Complex.normSq (star r4 * r3 + star c13 * c14 + star c23 * c24) = 1/900 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hVK : r1 * r3 * c13 = w * mu := by linear_combination h13
    have hWK : r2 * r3 * c23 = w ^ 2 * mu := by linear_combination h23
    have hVL : r1 * r4 * c14 = w ^ 2 * mu := by linear_combination h14
    have hWL : r2 * r4 * c24 = w * mu := by linear_combination h24
    have hcross : star (r1 * r3 * c13) * (r2 * r3 * c23) + star (r1 * r4 * c14) * (r2 * r4 * c24) = -(1/1500 : ℂ) := by
      rw [hVK, hWK, hVL, hWL, colourPair_12 hw hs, SixQubit.star_mul_self, hmu]
      norm_num
    refine normSq_of_triple (edge_G p1 p2 p3 p4 hcross n1 n2) ?_
    rw [map_mul, normSq_star, p2, p1]
    norm_num
  · have hVK : r1 * r2 * c12 = mu := by linear_combination h12
    have hWK : r3 * r2 * c23 = w ^ 2 * mu := by linear_combination h23
    have hVL : r1 * r4 * c14 = w ^ 2 * mu := by linear_combination h14
    have hWL : r3 * r4 * c34 = mu := by linear_combination h34
    have hcross : star (r1 * r2 * c12) * (r3 * r2 * c23) + star (r1 * r4 * c14) * (r3 * r4 * c34) = -(1/1500 : ℂ) := by
      rw [hVK, hWK, hVL, hWL, colourPair_02 hw hs, SixQubit.star_mul_self, hmu]
      norm_num
    refine normSq_of_triple (edge_G p1 p3 p2 p4 hcross n1 n3) ?_
    rw [map_mul, normSq_star, p3, p1]
    norm_num
  · have hVK : r1 * r2 * c12 = mu := by linear_combination h12
    have hWK : r4 * r2 * c24 = w * mu := by linear_combination h24
    have hVL : r1 * r3 * c13 = w * mu := by linear_combination h13
    have hWL : r4 * r3 * c34 = mu := by linear_combination h34
    have hcross : star (r1 * r2 * c12) * (r4 * r2 * c24) + star (r1 * r3 * c13) * (r4 * r3 * c34) = -(1/1500 : ℂ) := by
      rw [hVK, hWK, hVL, hWL, colourPair_01 hw hs, SixQubit.star_mul_self, hmu]
      norm_num
    refine normSq_of_triple (edge_G p1 p4 p2 p3 hcross n1 n4) ?_
    rw [map_mul, normSq_star, p4, p1]
    norm_num
  · have hVK : r2 * r1 * c12 = mu := by linear_combination h12
    have hWK : r3 * r1 * c13 = w * mu := by linear_combination h13
    have hVL : r2 * r4 * c24 = w * mu := by linear_combination h24
    have hWL : r3 * r4 * c34 = mu := by linear_combination h34
    have hcross : star (r2 * r1 * c12) * (r3 * r1 * c13) + star (r2 * r4 * c24) * (r3 * r4 * c34) = -(1/1500 : ℂ) := by
      rw [hVK, hWK, hVL, hWL, colourPair_01 hw hs, SixQubit.star_mul_self, hmu]
      norm_num
    refine normSq_of_triple (edge_G p2 p3 p1 p4 hcross n2 n3) ?_
    rw [map_mul, normSq_star, p3, p2]
    norm_num
  · have hVK : r2 * r1 * c12 = mu := by linear_combination h12
    have hWK : r4 * r1 * c14 = w ^ 2 * mu := by linear_combination h14
    have hVL : r2 * r3 * c23 = w ^ 2 * mu := by linear_combination h23
    have hWL : r4 * r3 * c34 = mu := by linear_combination h34
    have hcross : star (r2 * r1 * c12) * (r4 * r1 * c14) + star (r2 * r3 * c23) * (r4 * r3 * c34) = -(1/1500 : ℂ) := by
      rw [hVK, hWK, hVL, hWL, colourPair_02 hw hs, SixQubit.star_mul_self, hmu]
      norm_num
    refine normSq_of_triple (edge_G p2 p4 p1 p3 hcross n2 n4) ?_
    rw [map_mul, normSq_star, p4, p2]
    norm_num
  · have hVK : r3 * r1 * c13 = w * mu := by linear_combination h13
    have hWK : r4 * r1 * c14 = w ^ 2 * mu := by linear_combination h14
    have hVL : r3 * r2 * c23 = w ^ 2 * mu := by linear_combination h23
    have hWL : r4 * r2 * c24 = w * mu := by linear_combination h24
    have hcross : star (r3 * r1 * c13) * (r4 * r1 * c14) + star (r3 * r2 * c23) * (r4 * r2 * c24) = -(1/1500 : ℂ) := by
      rw [hVK, hWK, hVL, hWL, colourPair_12 hw hs, SixQubit.star_mul_self, hmu]
      norm_num
    refine normSq_of_triple (edge_G p3 p4 p1 p2 hcross n3 n4) ?_
    rw [map_mul, normSq_star, p4, p3]
    norm_num

/-! ## 5.  The flip masks and dressings that occur -/

def bt000000 : SS.BitString 6 := bs false false false false false false
def bt000001 : SS.BitString 6 := bs false false false false false true
def bt000010 : SS.BitString 6 := bs false false false false true false
def bt000011 : SS.BitString 6 := bs false false false false true true
def bt000100 : SS.BitString 6 := bs false false false true false false
def bt000101 : SS.BitString 6 := bs false false false true false true
def bt000110 : SS.BitString 6 := bs false false false true true false
def bt000111 : SS.BitString 6 := bs false false false true true true
def bt001000 : SS.BitString 6 := bs false false true false false false
def bt001001 : SS.BitString 6 := bs false false true false false true
def bt001010 : SS.BitString 6 := bs false false true false true false
def bt001011 : SS.BitString 6 := bs false false true false true true
def bt001100 : SS.BitString 6 := bs false false true true false false
def bt001101 : SS.BitString 6 := bs false false true true false true
def bt001110 : SS.BitString 6 := bs false false true true true false
def bt010000 : SS.BitString 6 := bs false true false false false false
def bt010001 : SS.BitString 6 := bs false true false false false true
def bt010010 : SS.BitString 6 := bs false true false false true false
def bt010011 : SS.BitString 6 := bs false true false false true true
def bt010100 : SS.BitString 6 := bs false true false true false false
def bt010101 : SS.BitString 6 := bs false true false true false true
def bt010110 : SS.BitString 6 := bs false true false true true false
def bt011000 : SS.BitString 6 := bs false true true false false false
def bt011001 : SS.BitString 6 := bs false true true false false true
def bt011010 : SS.BitString 6 := bs false true true false true false
def bt100000 : SS.BitString 6 := bs true false false false false false
def bt100001 : SS.BitString 6 := bs true false false false false true
def bt100010 : SS.BitString 6 := bs true false false false true false
def bt100011 : SS.BitString 6 := bs true false false false true true
def bt100100 : SS.BitString 6 := bs true false false true false false
def bt100101 : SS.BitString 6 := bs true false false true false true
def bt100110 : SS.BitString 6 := bs true false false true true false
def bt101000 : SS.BitString 6 := bs true false true false false false
def bt101001 : SS.BitString 6 := bs true false true false false true
def bt101010 : SS.BitString 6 := bs true false true false true false
def bt110000 : SS.BitString 6 := bs true true false false false false
def bt110001 : SS.BitString 6 := bs true true false false false true
def bt110010 : SS.BitString 6 := bs true true false false true false

/-! ## 6.  The `X_1 X_6` row and the antiunitary normal form -/

/-- The flip mask of `X_1 X_6`.  This is the one Knill--Laflamme row beyond the
twenty-one of `Orbit36.magnitudes_forced` that the enumerator needs: it ties the
top anchor `A` to the bottom anchor `a`. -/
def ex16 : SS.BitString 6 := bs true false false false false true

theorem inc_ex16 : S1.filter (fun y => SS.bxor y ex16 ∈ S0) = {z0, z2} := by decide
theorem flip_ex16_0 : SS.bxor z0 ex16 = y2 := by decide
theorem flip_ex16_2 : SS.bxor z2 ex16 = y0 := by decide
theorem sg_ex16_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg_ex16_w0_2 : SS.bdot w0 z2 = false := by decide

theorem ex_ex16_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ex16 w0 = star (c y2) * d z0 + star (c y0) * d z2 := by
  unfold offSum
  rw [inc_ex16]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [flip_ex16_0, flip_ex16_2]
  simp only [sg_ex16_w0_0, sg_ex16_w0_2, SixQubit.signMul_false]

/-- **The antiunitary normal form.**  A single unit phase `tau` relates every top
amplitude to the conjugate of the corresponding bottom amplitude, with a minus
sign on the four vertex and six edge amplitudes and a plus sign on the two
last-coordinate anchors.  This is `|1_L> = Z_5 Z_6 X^{(x)6} K |0_L>` up to the
logical basis phase `tau`. -/
structure TopForm (c d : SS.BitString 6 -> ℂ) (tau : ℂ) : Prop where
  unit : star tau * tau = 1
  t0 : d z0 = tau * star (c y0)
  t1 : d z1 = tau * star (c y1)
  t2 : d z2 = -(tau * star (c y2))
  t3 : d z3 = -(tau * star (c y3))
  t4 : d z4 = -(tau * star (c y4))
  t5 : d z5 = -(tau * star (c y5))
  t6 : d z6 = -(tau * star (c y6))
  t7 : d z7 = -(tau * star (c y7))
  t8 : d z8 = -(tau * star (c y8))
  t9 : d z9 = -(tau * star (c y9))
  t10 : d z10 = -(tau * star (c y10))
  t11 : d z11 = -(tau * star (c y11))

set_option maxHeartbeats 1600000 in
/-- **Every exact orbit-36 solution is in antiunitary normal form.**  The four
`X_i X_5` rows produce `tau` and the four vertex relations, the `X_1 X_6` row
propagates it to the anchor `a`, and the `X_i Z_j` pair relations propagate it to
the six edges. -/
theorem top_form (c d : SS.BitString 6 -> ℂ)
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
    (ho20 : offSum c d ex56 w0 = 0)
    (ho21 : offSum c d ex16 w0 = 0) :
    ∃ tau : ℂ, TopForm c d tau := by
  obtain ⟨-, k1, -, -, -, -, -, -, -, -, -, -, -, l1, -, -, -, -, -, -, -, -, -, -⟩ :=
    magnitudes_forced c d hm ho0 ho1 ho2 ho3 ho4 ho5 ho6 ho7 ho8 ho9 ho10 ho11 ho12 ho13 ho14 ho15 ho16 ho17 ho18 ho19 ho20
  obtain ⟨-, n1, n2, n3, n4, n5, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    full_support c d hm ho0 ho1 ho2 ho3 ho4 ho5 ho6 ho7 ho8 ho9 ho10 ho11 ho12 ho13 ho14 ho15 ho16 ho17 ho18 ho19 ho20
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
  rw [ex_ex16_w0] at ho21
  obtain ⟨q1, q2, q3, -⟩ :=
    SixQubit.K4Kernel.starSum_of_dressings (c1 := c y6) (c2 := c y7)
      (c3 := c y8) (r1 := c y3) (r2 := c y4) (r3 := c y5) (R1 := d z3)
      (R2 := d z4) (R3 := d z5) (C1 := d z6) (C2 := d z7) (C3 := d z8)
      (by linear_combination ho0) (by linear_combination ho1)
      (by linear_combination ho2) (by linear_combination ho3)
  obtain ⟨-, q4, q5, -⟩ :=
    SixQubit.K4Kernel.starSum_of_dressings (c1 := c y6) (c2 := c y9)
      (c3 := c y10) (r1 := c y2) (r2 := c y4) (r3 := c y5) (R1 := d z2)
      (R2 := d z4) (R3 := d z5) (C1 := d z6) (C2 := d z9) (C3 := d z10)
      (by linear_combination ho4) (by linear_combination ho5)
      (by linear_combination ho6) (by linear_combination ho7)
  obtain ⟨-, -, q6, -⟩ :=
    SixQubit.K4Kernel.starSum_of_dressings (c1 := c y7) (c2 := c y9)
      (c3 := c y11) (r1 := c y2) (r2 := c y3) (r3 := c y5) (R1 := d z2)
      (R2 := d z3) (R3 := d z5) (C1 := d z7) (C2 := d z9) (C3 := d z11)
      (by linear_combination ho8) (by linear_combination ho9)
      (by linear_combination ho10) (by linear_combination ho11)
  have s1 : star (c y1) ≠ 0 := star_ne_zero.mpr n1
  have s2 : star (c y2) ≠ 0 := star_ne_zero.mpr n2
  have s3 : star (c y3) ≠ 0 := star_ne_zero.mpr n3
  have s4 : star (c y4) ≠ 0 := star_ne_zero.mpr n4
  have s5 : star (c y5) ≠ 0 := star_ne_zero.mpr n5
  obtain ⟨tau, hB⟩ : ∃ t : ℂ, d z1 = t * star (c y1) :=
    ⟨d z1 / star (c y1), (div_mul_cancel₀ _ s1).symm⟩
  have hu : Complex.normSq tau = 1 := by
    have hq := congrArg Complex.normSq hB
    rw [map_mul, normSq_star, k1, l1] at hq
    linarith
  have hunit : star tau * tau = 1 := by
    rw [SixQubit.star_mul_self, hu]; norm_num
  have t2 : d z2 = -(tau * star (c y2)) := by
    have h : star (c y1) * (d z2 + tau * star (c y2)) = 0 := by
      linear_combination ho16 - star (c y2) * hB
    linear_combination (mul_eq_zero.mp h).resolve_left s1
  have t3 : d z3 = -(tau * star (c y3)) := by
    have h : star (c y1) * (d z3 + tau * star (c y3)) = 0 := by
      linear_combination ho17 - star (c y3) * hB
    linear_combination (mul_eq_zero.mp h).resolve_left s1
  have t4 : d z4 = -(tau * star (c y4)) := by
    have h : star (c y1) * (d z4 + tau * star (c y4)) = 0 := by
      linear_combination ho18 - star (c y4) * hB
    linear_combination (mul_eq_zero.mp h).resolve_left s1
  have t5 : d z5 = -(tau * star (c y5)) := by
    have h : star (c y1) * (d z5 + tau * star (c y5)) = 0 := by
      linear_combination ho19 - star (c y5) * hB
    linear_combination (mul_eq_zero.mp h).resolve_left s1
  have t0 : d z0 = tau * star (c y0) := by
    have h : star (c y2) * (d z0 - tau * star (c y0)) = 0 := by
      linear_combination ho21 - star (c y0) * t2
    linear_combination (mul_eq_zero.mp h).resolve_left s2
  have t6 : d z6 = -(tau * star (c y6)) := by
    have h : star (c y3) * (d z6 + tau * star (c y6)) = 0 := by
      linear_combination -q1 + star (c y6) * t3
    linear_combination (mul_eq_zero.mp h).resolve_left s3
  have t7 : d z7 = -(tau * star (c y7)) := by
    have h : star (c y4) * (d z7 + tau * star (c y7)) = 0 := by
      linear_combination -q2 + star (c y7) * t4
    linear_combination (mul_eq_zero.mp h).resolve_left s4
  have t8 : d z8 = -(tau * star (c y8)) := by
    have h : star (c y5) * (d z8 + tau * star (c y8)) = 0 := by
      linear_combination -q3 + star (c y8) * t5
    linear_combination (mul_eq_zero.mp h).resolve_left s5
  have t9 : d z9 = -(tau * star (c y9)) := by
    have h : star (c y4) * (d z9 + tau * star (c y9)) = 0 := by
      linear_combination -q4 + star (c y9) * t4
    linear_combination (mul_eq_zero.mp h).resolve_left s4
  have t10 : d z10 = -(tau * star (c y10)) := by
    have h : star (c y5) * (d z10 + tau * star (c y10)) = 0 := by
      linear_combination -q5 + star (c y10) * t5
    linear_combination (mul_eq_zero.mp h).resolve_left s5
  have t11 : d z11 = -(tau * star (c y11)) := by
    have h : star (c y5) * (d z11 + tau * star (c y11)) = 0 := by
      linear_combination -q6 + star (c y11) * t5
    linear_combination (mul_eq_zero.mp h).resolve_left s5
  exact ⟨tau, hunit, t0, hB, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11⟩

/-! ## 7.  Fiber incidences, and the projector trace of each incident mask -/

theorem incB_mk000000 : S0.filter (fun s => SS.bxor s bt000000 ∈ S0) = {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11} := by decide
theorem incT_mk000000 : S1.filter (fun s => SS.bxor s bt000000 ∈ S1) = {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11} := by decide
theorem flB_mk000000_0 : SS.bxor y0 bt000000 = y0 := by decide
theorem flT_mk000000_0 : SS.bxor z0 bt000000 = z0 := by decide
theorem flB_mk000000_1 : SS.bxor y1 bt000000 = y1 := by decide
theorem flT_mk000000_1 : SS.bxor z1 bt000000 = z1 := by decide
theorem flB_mk000000_2 : SS.bxor y2 bt000000 = y2 := by decide
theorem flT_mk000000_2 : SS.bxor z2 bt000000 = z2 := by decide
theorem flB_mk000000_3 : SS.bxor y3 bt000000 = y3 := by decide
theorem flT_mk000000_3 : SS.bxor z3 bt000000 = z3 := by decide
theorem flB_mk000000_4 : SS.bxor y4 bt000000 = y4 := by decide
theorem flT_mk000000_4 : SS.bxor z4 bt000000 = z4 := by decide
theorem flB_mk000000_5 : SS.bxor y5 bt000000 = y5 := by decide
theorem flT_mk000000_5 : SS.bxor z5 bt000000 = z5 := by decide
theorem flB_mk000000_6 : SS.bxor y6 bt000000 = y6 := by decide
theorem flT_mk000000_6 : SS.bxor z6 bt000000 = z6 := by decide
theorem flB_mk000000_7 : SS.bxor y7 bt000000 = y7 := by decide
theorem flT_mk000000_7 : SS.bxor z7 bt000000 = z7 := by decide
theorem flB_mk000000_8 : SS.bxor y8 bt000000 = y8 := by decide
theorem flT_mk000000_8 : SS.bxor z8 bt000000 = z8 := by decide
theorem flB_mk000000_9 : SS.bxor y9 bt000000 = y9 := by decide
theorem flT_mk000000_9 : SS.bxor z9 bt000000 = z9 := by decide
theorem flB_mk000000_10 : SS.bxor y10 bt000000 = y10 := by decide
theorem flT_mk000000_10 : SS.bxor z10 bt000000 = z10 := by decide
theorem flB_mk000000_11 : SS.bxor y11 bt000000 = y11 := by decide
theorem flT_mk000000_11 : SS.bxor z11 bt000000 = z11 := by decide

/-- The projector trace of every Pauli with flip mask `000000`, as a bottom
bracket and a top bracket over the incidences of that mask. -/
theorem split_mk000000 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (zz : SS.BitString 6) :
    projTrace c d ⟨bt000000, zz⟩
      = Complex.I ^ (SS.PauliString.mk bt000000 zz).numY
          * (SS.signC (SS.bdot zz y0) (star (c y0) * c y0) + (SS.signC (SS.bdot zz y1) (star (c y1) * c y1) + (SS.signC (SS.bdot zz y2) (star (c y2) * c y2) + (SS.signC (SS.bdot zz y3) (star (c y3) * c y3) + (SS.signC (SS.bdot zz y4) (star (c y4) * c y4) + (SS.signC (SS.bdot zz y5) (star (c y5) * c y5) + (SS.signC (SS.bdot zz y6) (star (c y6) * c y6) + (SS.signC (SS.bdot zz y7) (star (c y7) * c y7) + (SS.signC (SS.bdot zz y8) (star (c y8) * c y8) + (SS.signC (SS.bdot zz y9) (star (c y9) * c y9) + (SS.signC (SS.bdot zz y10) (star (c y10) * c y10) + (SS.signC (SS.bdot zz y11) (star (c y11) * c y11)))))))))))))
        + Complex.I ^ (SS.PauliString.mk bt000000 zz).numY
          * (SS.signC (SS.bdot zz z0) (star (d z0) * d z0) + (SS.signC (SS.bdot zz z1) (star (d z1) * d z1) + (SS.signC (SS.bdot zz z2) (star (d z2) * d z2) + (SS.signC (SS.bdot zz z3) (star (d z3) * d z3) + (SS.signC (SS.bdot zz z4) (star (d z4) * d z4) + (SS.signC (SS.bdot zz z5) (star (d z5) * d z5) + (SS.signC (SS.bdot zz z6) (star (d z6) * d z6) + (SS.signC (SS.bdot zz z7) (star (d z7) * d z7) + (SS.signC (SS.bdot zz z8) (star (d z8) * d z8) + (SS.signC (SS.bdot zz z9) (star (d z9) * d z9) + (SS.signC (SS.bdot zz z10) (star (d z10) * d z10) + (SS.signC (SS.bdot zz z11) (star (d z11) * d z11))))))))))))) := by
  rw [projTrace, SS.innerC_pauliAct_support S0 S0 c c _ hc hc,
    SS.innerC_pauliAct_support S1 S1 d d _ hd hd]
  rw [show (SS.PauliString.mk bt000000 zz).x = bt000000 from rfl, incB_mk000000, incT_mk000000]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show (SS.PauliString.mk bt000000 zz).z = zz from rfl]
  rw [flB_mk000000_0, flB_mk000000_1, flB_mk000000_2, flB_mk000000_3, flB_mk000000_4, flB_mk000000_5, flB_mk000000_6, flB_mk000000_7, flB_mk000000_8, flB_mk000000_9, flB_mk000000_10, flB_mk000000_11, flT_mk000000_0, flT_mk000000_1, flT_mk000000_2, flT_mk000000_3, flT_mk000000_4, flT_mk000000_5, flT_mk000000_6, flT_mk000000_7, flT_mk000000_8, flT_mk000000_9, flT_mk000000_10, flT_mk000000_11]

theorem incB_mk110000 : S0.filter (fun s => SS.bxor s bt110000 ∈ S0) = {y2, y3, y7, y9, y8, y10} := by decide
theorem incT_mk110000 : S1.filter (fun s => SS.bxor s bt110000 ∈ S1) = {z2, z3, z7, z9, z8, z10} := by decide
theorem flB_mk110000_2 : SS.bxor y2 bt110000 = y3 := by decide
theorem flT_mk110000_2 : SS.bxor z2 bt110000 = z3 := by decide
theorem flB_mk110000_3 : SS.bxor y3 bt110000 = y2 := by decide
theorem flT_mk110000_3 : SS.bxor z3 bt110000 = z2 := by decide
theorem flB_mk110000_7 : SS.bxor y7 bt110000 = y9 := by decide
theorem flT_mk110000_7 : SS.bxor z7 bt110000 = z9 := by decide
theorem flB_mk110000_9 : SS.bxor y9 bt110000 = y7 := by decide
theorem flT_mk110000_9 : SS.bxor z9 bt110000 = z7 := by decide
theorem flB_mk110000_8 : SS.bxor y8 bt110000 = y10 := by decide
theorem flT_mk110000_8 : SS.bxor z8 bt110000 = z10 := by decide
theorem flB_mk110000_10 : SS.bxor y10 bt110000 = y8 := by decide
theorem flT_mk110000_10 : SS.bxor z10 bt110000 = z8 := by decide

/-- The projector trace of every Pauli with flip mask `110000`, as a bottom
bracket and a top bracket over the incidences of that mask. -/
theorem split_mk110000 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (zz : SS.BitString 6) :
    projTrace c d ⟨bt110000, zz⟩
      = Complex.I ^ (SS.PauliString.mk bt110000 zz).numY
          * (SS.signC (SS.bdot zz y2) (star (c y3) * c y2) + (SS.signC (SS.bdot zz y3) (star (c y2) * c y3) + (SS.signC (SS.bdot zz y7) (star (c y9) * c y7) + (SS.signC (SS.bdot zz y9) (star (c y7) * c y9) + (SS.signC (SS.bdot zz y8) (star (c y10) * c y8) + (SS.signC (SS.bdot zz y10) (star (c y8) * c y10)))))))
        + Complex.I ^ (SS.PauliString.mk bt110000 zz).numY
          * (SS.signC (SS.bdot zz z2) (star (d z3) * d z2) + (SS.signC (SS.bdot zz z3) (star (d z2) * d z3) + (SS.signC (SS.bdot zz z7) (star (d z9) * d z7) + (SS.signC (SS.bdot zz z9) (star (d z7) * d z9) + (SS.signC (SS.bdot zz z8) (star (d z10) * d z8) + (SS.signC (SS.bdot zz z10) (star (d z8) * d z10))))))) := by
  rw [projTrace, SS.innerC_pauliAct_support S0 S0 c c _ hc hc,
    SS.innerC_pauliAct_support S1 S1 d d _ hd hd]
  rw [show (SS.PauliString.mk bt110000 zz).x = bt110000 from rfl, incB_mk110000, incT_mk110000]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show (SS.PauliString.mk bt110000 zz).z = zz from rfl]
  rw [flB_mk110000_2, flB_mk110000_3, flB_mk110000_7, flB_mk110000_9, flB_mk110000_8, flB_mk110000_10, flT_mk110000_2, flT_mk110000_3, flT_mk110000_7, flT_mk110000_9, flT_mk110000_8, flT_mk110000_10]

theorem incB_mk101000 : S0.filter (fun s => SS.bxor s bt101000 ∈ S0) = {y2, y4, y6, y9, y8, y11} := by decide
theorem incT_mk101000 : S1.filter (fun s => SS.bxor s bt101000 ∈ S1) = {z2, z4, z6, z9, z8, z11} := by decide
theorem flB_mk101000_2 : SS.bxor y2 bt101000 = y4 := by decide
theorem flT_mk101000_2 : SS.bxor z2 bt101000 = z4 := by decide
theorem flB_mk101000_4 : SS.bxor y4 bt101000 = y2 := by decide
theorem flT_mk101000_4 : SS.bxor z4 bt101000 = z2 := by decide
theorem flB_mk101000_6 : SS.bxor y6 bt101000 = y9 := by decide
theorem flT_mk101000_6 : SS.bxor z6 bt101000 = z9 := by decide
theorem flB_mk101000_9 : SS.bxor y9 bt101000 = y6 := by decide
theorem flT_mk101000_9 : SS.bxor z9 bt101000 = z6 := by decide
theorem flB_mk101000_8 : SS.bxor y8 bt101000 = y11 := by decide
theorem flT_mk101000_8 : SS.bxor z8 bt101000 = z11 := by decide
theorem flB_mk101000_11 : SS.bxor y11 bt101000 = y8 := by decide
theorem flT_mk101000_11 : SS.bxor z11 bt101000 = z8 := by decide

/-- The projector trace of every Pauli with flip mask `101000`, as a bottom
bracket and a top bracket over the incidences of that mask. -/
theorem split_mk101000 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (zz : SS.BitString 6) :
    projTrace c d ⟨bt101000, zz⟩
      = Complex.I ^ (SS.PauliString.mk bt101000 zz).numY
          * (SS.signC (SS.bdot zz y2) (star (c y4) * c y2) + (SS.signC (SS.bdot zz y4) (star (c y2) * c y4) + (SS.signC (SS.bdot zz y6) (star (c y9) * c y6) + (SS.signC (SS.bdot zz y9) (star (c y6) * c y9) + (SS.signC (SS.bdot zz y8) (star (c y11) * c y8) + (SS.signC (SS.bdot zz y11) (star (c y8) * c y11)))))))
        + Complex.I ^ (SS.PauliString.mk bt101000 zz).numY
          * (SS.signC (SS.bdot zz z2) (star (d z4) * d z2) + (SS.signC (SS.bdot zz z4) (star (d z2) * d z4) + (SS.signC (SS.bdot zz z6) (star (d z9) * d z6) + (SS.signC (SS.bdot zz z9) (star (d z6) * d z9) + (SS.signC (SS.bdot zz z8) (star (d z11) * d z8) + (SS.signC (SS.bdot zz z11) (star (d z8) * d z11))))))) := by
  rw [projTrace, SS.innerC_pauliAct_support S0 S0 c c _ hc hc,
    SS.innerC_pauliAct_support S1 S1 d d _ hd hd]
  rw [show (SS.PauliString.mk bt101000 zz).x = bt101000 from rfl, incB_mk101000, incT_mk101000]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show (SS.PauliString.mk bt101000 zz).z = zz from rfl]
  rw [flB_mk101000_2, flB_mk101000_4, flB_mk101000_6, flB_mk101000_9, flB_mk101000_8, flB_mk101000_11, flT_mk101000_2, flT_mk101000_4, flT_mk101000_6, flT_mk101000_9, flT_mk101000_8, flT_mk101000_11]

theorem incB_mk100100 : S0.filter (fun s => SS.bxor s bt100100 ∈ S0) = {y2, y5, y6, y10, y7, y11} := by decide
theorem incT_mk100100 : S1.filter (fun s => SS.bxor s bt100100 ∈ S1) = {z2, z5, z6, z10, z7, z11} := by decide
theorem flB_mk100100_2 : SS.bxor y2 bt100100 = y5 := by decide
theorem flT_mk100100_2 : SS.bxor z2 bt100100 = z5 := by decide
theorem flB_mk100100_5 : SS.bxor y5 bt100100 = y2 := by decide
theorem flT_mk100100_5 : SS.bxor z5 bt100100 = z2 := by decide
theorem flB_mk100100_6 : SS.bxor y6 bt100100 = y10 := by decide
theorem flT_mk100100_6 : SS.bxor z6 bt100100 = z10 := by decide
theorem flB_mk100100_10 : SS.bxor y10 bt100100 = y6 := by decide
theorem flT_mk100100_10 : SS.bxor z10 bt100100 = z6 := by decide
theorem flB_mk100100_7 : SS.bxor y7 bt100100 = y11 := by decide
theorem flT_mk100100_7 : SS.bxor z7 bt100100 = z11 := by decide
theorem flB_mk100100_11 : SS.bxor y11 bt100100 = y7 := by decide
theorem flT_mk100100_11 : SS.bxor z11 bt100100 = z7 := by decide

/-- The projector trace of every Pauli with flip mask `100100`, as a bottom
bracket and a top bracket over the incidences of that mask. -/
theorem split_mk100100 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (zz : SS.BitString 6) :
    projTrace c d ⟨bt100100, zz⟩
      = Complex.I ^ (SS.PauliString.mk bt100100 zz).numY
          * (SS.signC (SS.bdot zz y2) (star (c y5) * c y2) + (SS.signC (SS.bdot zz y5) (star (c y2) * c y5) + (SS.signC (SS.bdot zz y6) (star (c y10) * c y6) + (SS.signC (SS.bdot zz y10) (star (c y6) * c y10) + (SS.signC (SS.bdot zz y7) (star (c y11) * c y7) + (SS.signC (SS.bdot zz y11) (star (c y7) * c y11)))))))
        + Complex.I ^ (SS.PauliString.mk bt100100 zz).numY
          * (SS.signC (SS.bdot zz z2) (star (d z5) * d z2) + (SS.signC (SS.bdot zz z5) (star (d z2) * d z5) + (SS.signC (SS.bdot zz z6) (star (d z10) * d z6) + (SS.signC (SS.bdot zz z10) (star (d z6) * d z10) + (SS.signC (SS.bdot zz z7) (star (d z11) * d z7) + (SS.signC (SS.bdot zz z11) (star (d z7) * d z11))))))) := by
  rw [projTrace, SS.innerC_pauliAct_support S0 S0 c c _ hc hc,
    SS.innerC_pauliAct_support S1 S1 d d _ hd hd]
  rw [show (SS.PauliString.mk bt100100 zz).x = bt100100 from rfl, incB_mk100100, incT_mk100100]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show (SS.PauliString.mk bt100100 zz).z = zz from rfl]
  rw [flB_mk100100_2, flB_mk100100_5, flB_mk100100_6, flB_mk100100_10, flB_mk100100_7, flB_mk100100_11, flT_mk100100_2, flT_mk100100_5, flT_mk100100_6, flT_mk100100_10, flT_mk100100_7, flT_mk100100_11]

theorem incB_mk011000 : S0.filter (fun s => SS.bxor s bt011000 ∈ S0) = {y3, y4, y6, y7, y10, y11} := by decide
theorem incT_mk011000 : S1.filter (fun s => SS.bxor s bt011000 ∈ S1) = {z3, z4, z6, z7, z10, z11} := by decide
theorem flB_mk011000_3 : SS.bxor y3 bt011000 = y4 := by decide
theorem flT_mk011000_3 : SS.bxor z3 bt011000 = z4 := by decide
theorem flB_mk011000_4 : SS.bxor y4 bt011000 = y3 := by decide
theorem flT_mk011000_4 : SS.bxor z4 bt011000 = z3 := by decide
theorem flB_mk011000_6 : SS.bxor y6 bt011000 = y7 := by decide
theorem flT_mk011000_6 : SS.bxor z6 bt011000 = z7 := by decide
theorem flB_mk011000_7 : SS.bxor y7 bt011000 = y6 := by decide
theorem flT_mk011000_7 : SS.bxor z7 bt011000 = z6 := by decide
theorem flB_mk011000_10 : SS.bxor y10 bt011000 = y11 := by decide
theorem flT_mk011000_10 : SS.bxor z10 bt011000 = z11 := by decide
theorem flB_mk011000_11 : SS.bxor y11 bt011000 = y10 := by decide
theorem flT_mk011000_11 : SS.bxor z11 bt011000 = z10 := by decide

/-- The projector trace of every Pauli with flip mask `011000`, as a bottom
bracket and a top bracket over the incidences of that mask. -/
theorem split_mk011000 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (zz : SS.BitString 6) :
    projTrace c d ⟨bt011000, zz⟩
      = Complex.I ^ (SS.PauliString.mk bt011000 zz).numY
          * (SS.signC (SS.bdot zz y3) (star (c y4) * c y3) + (SS.signC (SS.bdot zz y4) (star (c y3) * c y4) + (SS.signC (SS.bdot zz y6) (star (c y7) * c y6) + (SS.signC (SS.bdot zz y7) (star (c y6) * c y7) + (SS.signC (SS.bdot zz y10) (star (c y11) * c y10) + (SS.signC (SS.bdot zz y11) (star (c y10) * c y11)))))))
        + Complex.I ^ (SS.PauliString.mk bt011000 zz).numY
          * (SS.signC (SS.bdot zz z3) (star (d z4) * d z3) + (SS.signC (SS.bdot zz z4) (star (d z3) * d z4) + (SS.signC (SS.bdot zz z6) (star (d z7) * d z6) + (SS.signC (SS.bdot zz z7) (star (d z6) * d z7) + (SS.signC (SS.bdot zz z10) (star (d z11) * d z10) + (SS.signC (SS.bdot zz z11) (star (d z10) * d z11))))))) := by
  rw [projTrace, SS.innerC_pauliAct_support S0 S0 c c _ hc hc,
    SS.innerC_pauliAct_support S1 S1 d d _ hd hd]
  rw [show (SS.PauliString.mk bt011000 zz).x = bt011000 from rfl, incB_mk011000, incT_mk011000]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show (SS.PauliString.mk bt011000 zz).z = zz from rfl]
  rw [flB_mk011000_3, flB_mk011000_4, flB_mk011000_6, flB_mk011000_7, flB_mk011000_10, flB_mk011000_11, flT_mk011000_3, flT_mk011000_4, flT_mk011000_6, flT_mk011000_7, flT_mk011000_10, flT_mk011000_11]

theorem incB_mk010100 : S0.filter (fun s => SS.bxor s bt010100 ∈ S0) = {y3, y5, y6, y8, y9, y11} := by decide
theorem incT_mk010100 : S1.filter (fun s => SS.bxor s bt010100 ∈ S1) = {z3, z5, z6, z8, z9, z11} := by decide
theorem flB_mk010100_3 : SS.bxor y3 bt010100 = y5 := by decide
theorem flT_mk010100_3 : SS.bxor z3 bt010100 = z5 := by decide
theorem flB_mk010100_5 : SS.bxor y5 bt010100 = y3 := by decide
theorem flT_mk010100_5 : SS.bxor z5 bt010100 = z3 := by decide
theorem flB_mk010100_6 : SS.bxor y6 bt010100 = y8 := by decide
theorem flT_mk010100_6 : SS.bxor z6 bt010100 = z8 := by decide
theorem flB_mk010100_8 : SS.bxor y8 bt010100 = y6 := by decide
theorem flT_mk010100_8 : SS.bxor z8 bt010100 = z6 := by decide
theorem flB_mk010100_9 : SS.bxor y9 bt010100 = y11 := by decide
theorem flT_mk010100_9 : SS.bxor z9 bt010100 = z11 := by decide
theorem flB_mk010100_11 : SS.bxor y11 bt010100 = y9 := by decide
theorem flT_mk010100_11 : SS.bxor z11 bt010100 = z9 := by decide

/-- The projector trace of every Pauli with flip mask `010100`, as a bottom
bracket and a top bracket over the incidences of that mask. -/
theorem split_mk010100 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (zz : SS.BitString 6) :
    projTrace c d ⟨bt010100, zz⟩
      = Complex.I ^ (SS.PauliString.mk bt010100 zz).numY
          * (SS.signC (SS.bdot zz y3) (star (c y5) * c y3) + (SS.signC (SS.bdot zz y5) (star (c y3) * c y5) + (SS.signC (SS.bdot zz y6) (star (c y8) * c y6) + (SS.signC (SS.bdot zz y8) (star (c y6) * c y8) + (SS.signC (SS.bdot zz y9) (star (c y11) * c y9) + (SS.signC (SS.bdot zz y11) (star (c y9) * c y11)))))))
        + Complex.I ^ (SS.PauliString.mk bt010100 zz).numY
          * (SS.signC (SS.bdot zz z3) (star (d z5) * d z3) + (SS.signC (SS.bdot zz z5) (star (d z3) * d z5) + (SS.signC (SS.bdot zz z6) (star (d z8) * d z6) + (SS.signC (SS.bdot zz z8) (star (d z6) * d z8) + (SS.signC (SS.bdot zz z9) (star (d z11) * d z9) + (SS.signC (SS.bdot zz z11) (star (d z9) * d z11))))))) := by
  rw [projTrace, SS.innerC_pauliAct_support S0 S0 c c _ hc hc,
    SS.innerC_pauliAct_support S1 S1 d d _ hd hd]
  rw [show (SS.PauliString.mk bt010100 zz).x = bt010100 from rfl, incB_mk010100, incT_mk010100]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show (SS.PauliString.mk bt010100 zz).z = zz from rfl]
  rw [flB_mk010100_3, flB_mk010100_5, flB_mk010100_6, flB_mk010100_8, flB_mk010100_9, flB_mk010100_11, flT_mk010100_3, flT_mk010100_5, flT_mk010100_6, flT_mk010100_8, flT_mk010100_9, flT_mk010100_11]

theorem incB_mk001100 : S0.filter (fun s => SS.bxor s bt001100 ∈ S0) = {y4, y5, y7, y8, y9, y10} := by decide
theorem incT_mk001100 : S1.filter (fun s => SS.bxor s bt001100 ∈ S1) = {z4, z5, z7, z8, z9, z10} := by decide
theorem flB_mk001100_4 : SS.bxor y4 bt001100 = y5 := by decide
theorem flT_mk001100_4 : SS.bxor z4 bt001100 = z5 := by decide
theorem flB_mk001100_5 : SS.bxor y5 bt001100 = y4 := by decide
theorem flT_mk001100_5 : SS.bxor z5 bt001100 = z4 := by decide
theorem flB_mk001100_7 : SS.bxor y7 bt001100 = y8 := by decide
theorem flT_mk001100_7 : SS.bxor z7 bt001100 = z8 := by decide
theorem flB_mk001100_8 : SS.bxor y8 bt001100 = y7 := by decide
theorem flT_mk001100_8 : SS.bxor z8 bt001100 = z7 := by decide
theorem flB_mk001100_9 : SS.bxor y9 bt001100 = y10 := by decide
theorem flT_mk001100_9 : SS.bxor z9 bt001100 = z10 := by decide
theorem flB_mk001100_10 : SS.bxor y10 bt001100 = y9 := by decide
theorem flT_mk001100_10 : SS.bxor z10 bt001100 = z9 := by decide

/-- The projector trace of every Pauli with flip mask `001100`, as a bottom
bracket and a top bracket over the incidences of that mask. -/
theorem split_mk001100 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (zz : SS.BitString 6) :
    projTrace c d ⟨bt001100, zz⟩
      = Complex.I ^ (SS.PauliString.mk bt001100 zz).numY
          * (SS.signC (SS.bdot zz y4) (star (c y5) * c y4) + (SS.signC (SS.bdot zz y5) (star (c y4) * c y5) + (SS.signC (SS.bdot zz y7) (star (c y8) * c y7) + (SS.signC (SS.bdot zz y8) (star (c y7) * c y8) + (SS.signC (SS.bdot zz y9) (star (c y10) * c y9) + (SS.signC (SS.bdot zz y10) (star (c y9) * c y10)))))))
        + Complex.I ^ (SS.PauliString.mk bt001100 zz).numY
          * (SS.signC (SS.bdot zz z4) (star (d z5) * d z4) + (SS.signC (SS.bdot zz z5) (star (d z4) * d z5) + (SS.signC (SS.bdot zz z7) (star (d z8) * d z7) + (SS.signC (SS.bdot zz z8) (star (d z7) * d z8) + (SS.signC (SS.bdot zz z9) (star (d z10) * d z9) + (SS.signC (SS.bdot zz z10) (star (d z9) * d z10))))))) := by
  rw [projTrace, SS.innerC_pauliAct_support S0 S0 c c _ hc hc,
    SS.innerC_pauliAct_support S1 S1 d d _ hd hd]
  rw [show (SS.PauliString.mk bt001100 zz).x = bt001100 from rfl, incB_mk001100, incT_mk001100]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show (SS.PauliString.mk bt001100 zz).z = zz from rfl]
  rw [flB_mk001100_4, flB_mk001100_5, flB_mk001100_7, flB_mk001100_8, flB_mk001100_9, flB_mk001100_10, flT_mk001100_4, flT_mk001100_5, flT_mk001100_7, flT_mk001100_8, flT_mk001100_9, flT_mk001100_10]

theorem incB_mk000011 : S0.filter (fun s => SS.bxor s bt000011 ∈ S0) = {y0, y1} := by decide
theorem incT_mk000011 : S1.filter (fun s => SS.bxor s bt000011 ∈ S1) = {z0, z1} := by decide
theorem flB_mk000011_0 : SS.bxor y0 bt000011 = y1 := by decide
theorem flT_mk000011_0 : SS.bxor z0 bt000011 = z1 := by decide
theorem flB_mk000011_1 : SS.bxor y1 bt000011 = y0 := by decide
theorem flT_mk000011_1 : SS.bxor z1 bt000011 = z0 := by decide

/-- The projector trace of every Pauli with flip mask `000011`, as a bottom
bracket and a top bracket over the incidences of that mask. -/
theorem split_mk000011 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (zz : SS.BitString 6) :
    projTrace c d ⟨bt000011, zz⟩
      = Complex.I ^ (SS.PauliString.mk bt000011 zz).numY
          * (SS.signC (SS.bdot zz y0) (star (c y1) * c y0) + (SS.signC (SS.bdot zz y1) (star (c y0) * c y1)))
        + Complex.I ^ (SS.PauliString.mk bt000011 zz).numY
          * (SS.signC (SS.bdot zz z0) (star (d z1) * d z0) + (SS.signC (SS.bdot zz z1) (star (d z0) * d z1))) := by
  rw [projTrace, SS.innerC_pauliAct_support S0 S0 c c _ hc hc,
    SS.innerC_pauliAct_support S1 S1 d d _ hd hd]
  rw [show (SS.PauliString.mk bt000011 zz).x = bt000011 from rfl, incB_mk000011, incT_mk000011]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show (SS.PauliString.mk bt000011 zz).z = zz from rfl]
  rw [flB_mk000011_0, flB_mk000011_1, flT_mk000011_0, flT_mk000011_1]

theorem incB_mk001101 : S0.filter (fun s => SS.bxor s bt001101 ∈ S0) = {y0, y11} := by decide
theorem incT_mk001101 : S1.filter (fun s => SS.bxor s bt001101 ∈ S1) = {z0, z11} := by decide
theorem flB_mk001101_0 : SS.bxor y0 bt001101 = y11 := by decide
theorem flT_mk001101_0 : SS.bxor z0 bt001101 = z11 := by decide
theorem flB_mk001101_11 : SS.bxor y11 bt001101 = y0 := by decide
theorem flT_mk001101_11 : SS.bxor z11 bt001101 = z0 := by decide

/-- The projector trace of every Pauli with flip mask `001101`, as a bottom
bracket and a top bracket over the incidences of that mask. -/
theorem split_mk001101 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (zz : SS.BitString 6) :
    projTrace c d ⟨bt001101, zz⟩
      = Complex.I ^ (SS.PauliString.mk bt001101 zz).numY
          * (SS.signC (SS.bdot zz y0) (star (c y11) * c y0) + (SS.signC (SS.bdot zz y11) (star (c y0) * c y11)))
        + Complex.I ^ (SS.PauliString.mk bt001101 zz).numY
          * (SS.signC (SS.bdot zz z0) (star (d z11) * d z0) + (SS.signC (SS.bdot zz z11) (star (d z0) * d z11))) := by
  rw [projTrace, SS.innerC_pauliAct_support S0 S0 c c _ hc hc,
    SS.innerC_pauliAct_support S1 S1 d d _ hd hd]
  rw [show (SS.PauliString.mk bt001101 zz).x = bt001101 from rfl, incB_mk001101, incT_mk001101]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show (SS.PauliString.mk bt001101 zz).z = zz from rfl]
  rw [flB_mk001101_0, flB_mk001101_11, flT_mk001101_0, flT_mk001101_11]

theorem incB_mk001110 : S0.filter (fun s => SS.bxor s bt001110 ∈ S0) = {y1, y11} := by decide
theorem incT_mk001110 : S1.filter (fun s => SS.bxor s bt001110 ∈ S1) = {z1, z11} := by decide
theorem flB_mk001110_1 : SS.bxor y1 bt001110 = y11 := by decide
theorem flT_mk001110_1 : SS.bxor z1 bt001110 = z11 := by decide
theorem flB_mk001110_11 : SS.bxor y11 bt001110 = y1 := by decide
theorem flT_mk001110_11 : SS.bxor z11 bt001110 = z1 := by decide

/-- The projector trace of every Pauli with flip mask `001110`, as a bottom
bracket and a top bracket over the incidences of that mask. -/
theorem split_mk001110 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (zz : SS.BitString 6) :
    projTrace c d ⟨bt001110, zz⟩
      = Complex.I ^ (SS.PauliString.mk bt001110 zz).numY
          * (SS.signC (SS.bdot zz y1) (star (c y11) * c y1) + (SS.signC (SS.bdot zz y11) (star (c y1) * c y11)))
        + Complex.I ^ (SS.PauliString.mk bt001110 zz).numY
          * (SS.signC (SS.bdot zz z1) (star (d z11) * d z1) + (SS.signC (SS.bdot zz z11) (star (d z1) * d z11))) := by
  rw [projTrace, SS.innerC_pauliAct_support S0 S0 c c _ hc hc,
    SS.innerC_pauliAct_support S1 S1 d d _ hd hd]
  rw [show (SS.PauliString.mk bt001110 zz).x = bt001110 from rfl, incB_mk001110, incT_mk001110]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show (SS.PauliString.mk bt001110 zz).z = zz from rfl]
  rw [flB_mk001110_1, flB_mk001110_11, flT_mk001110_1, flT_mk001110_11]

theorem incB_mk010101 : S0.filter (fun s => SS.bxor s bt010101 ∈ S0) = {y0, y10} := by decide
theorem incT_mk010101 : S1.filter (fun s => SS.bxor s bt010101 ∈ S1) = {z0, z10} := by decide
theorem flB_mk010101_0 : SS.bxor y0 bt010101 = y10 := by decide
theorem flT_mk010101_0 : SS.bxor z0 bt010101 = z10 := by decide
theorem flB_mk010101_10 : SS.bxor y10 bt010101 = y0 := by decide
theorem flT_mk010101_10 : SS.bxor z10 bt010101 = z0 := by decide

/-- The projector trace of every Pauli with flip mask `010101`, as a bottom
bracket and a top bracket over the incidences of that mask. -/
theorem split_mk010101 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (zz : SS.BitString 6) :
    projTrace c d ⟨bt010101, zz⟩
      = Complex.I ^ (SS.PauliString.mk bt010101 zz).numY
          * (SS.signC (SS.bdot zz y0) (star (c y10) * c y0) + (SS.signC (SS.bdot zz y10) (star (c y0) * c y10)))
        + Complex.I ^ (SS.PauliString.mk bt010101 zz).numY
          * (SS.signC (SS.bdot zz z0) (star (d z10) * d z0) + (SS.signC (SS.bdot zz z10) (star (d z0) * d z10))) := by
  rw [projTrace, SS.innerC_pauliAct_support S0 S0 c c _ hc hc,
    SS.innerC_pauliAct_support S1 S1 d d _ hd hd]
  rw [show (SS.PauliString.mk bt010101 zz).x = bt010101 from rfl, incB_mk010101, incT_mk010101]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show (SS.PauliString.mk bt010101 zz).z = zz from rfl]
  rw [flB_mk010101_0, flB_mk010101_10, flT_mk010101_0, flT_mk010101_10]

theorem incB_mk010110 : S0.filter (fun s => SS.bxor s bt010110 ∈ S0) = {y1, y10} := by decide
theorem incT_mk010110 : S1.filter (fun s => SS.bxor s bt010110 ∈ S1) = {z1, z10} := by decide
theorem flB_mk010110_1 : SS.bxor y1 bt010110 = y10 := by decide
theorem flT_mk010110_1 : SS.bxor z1 bt010110 = z10 := by decide
theorem flB_mk010110_10 : SS.bxor y10 bt010110 = y1 := by decide
theorem flT_mk010110_10 : SS.bxor z10 bt010110 = z1 := by decide

/-- The projector trace of every Pauli with flip mask `010110`, as a bottom
bracket and a top bracket over the incidences of that mask. -/
theorem split_mk010110 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (zz : SS.BitString 6) :
    projTrace c d ⟨bt010110, zz⟩
      = Complex.I ^ (SS.PauliString.mk bt010110 zz).numY
          * (SS.signC (SS.bdot zz y1) (star (c y10) * c y1) + (SS.signC (SS.bdot zz y10) (star (c y1) * c y10)))
        + Complex.I ^ (SS.PauliString.mk bt010110 zz).numY
          * (SS.signC (SS.bdot zz z1) (star (d z10) * d z1) + (SS.signC (SS.bdot zz z10) (star (d z1) * d z10))) := by
  rw [projTrace, SS.innerC_pauliAct_support S0 S0 c c _ hc hc,
    SS.innerC_pauliAct_support S1 S1 d d _ hd hd]
  rw [show (SS.PauliString.mk bt010110 zz).x = bt010110 from rfl, incB_mk010110, incT_mk010110]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show (SS.PauliString.mk bt010110 zz).z = zz from rfl]
  rw [flB_mk010110_1, flB_mk010110_10, flT_mk010110_1, flT_mk010110_10]

theorem incB_mk011001 : S0.filter (fun s => SS.bxor s bt011001 ∈ S0) = {y0, y9} := by decide
theorem incT_mk011001 : S1.filter (fun s => SS.bxor s bt011001 ∈ S1) = {z0, z9} := by decide
theorem flB_mk011001_0 : SS.bxor y0 bt011001 = y9 := by decide
theorem flT_mk011001_0 : SS.bxor z0 bt011001 = z9 := by decide
theorem flB_mk011001_9 : SS.bxor y9 bt011001 = y0 := by decide
theorem flT_mk011001_9 : SS.bxor z9 bt011001 = z0 := by decide

/-- The projector trace of every Pauli with flip mask `011001`, as a bottom
bracket and a top bracket over the incidences of that mask. -/
theorem split_mk011001 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (zz : SS.BitString 6) :
    projTrace c d ⟨bt011001, zz⟩
      = Complex.I ^ (SS.PauliString.mk bt011001 zz).numY
          * (SS.signC (SS.bdot zz y0) (star (c y9) * c y0) + (SS.signC (SS.bdot zz y9) (star (c y0) * c y9)))
        + Complex.I ^ (SS.PauliString.mk bt011001 zz).numY
          * (SS.signC (SS.bdot zz z0) (star (d z9) * d z0) + (SS.signC (SS.bdot zz z9) (star (d z0) * d z9))) := by
  rw [projTrace, SS.innerC_pauliAct_support S0 S0 c c _ hc hc,
    SS.innerC_pauliAct_support S1 S1 d d _ hd hd]
  rw [show (SS.PauliString.mk bt011001 zz).x = bt011001 from rfl, incB_mk011001, incT_mk011001]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show (SS.PauliString.mk bt011001 zz).z = zz from rfl]
  rw [flB_mk011001_0, flB_mk011001_9, flT_mk011001_0, flT_mk011001_9]

theorem incB_mk011010 : S0.filter (fun s => SS.bxor s bt011010 ∈ S0) = {y1, y9} := by decide
theorem incT_mk011010 : S1.filter (fun s => SS.bxor s bt011010 ∈ S1) = {z1, z9} := by decide
theorem flB_mk011010_1 : SS.bxor y1 bt011010 = y9 := by decide
theorem flT_mk011010_1 : SS.bxor z1 bt011010 = z9 := by decide
theorem flB_mk011010_9 : SS.bxor y9 bt011010 = y1 := by decide
theorem flT_mk011010_9 : SS.bxor z9 bt011010 = z1 := by decide

/-- The projector trace of every Pauli with flip mask `011010`, as a bottom
bracket and a top bracket over the incidences of that mask. -/
theorem split_mk011010 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (zz : SS.BitString 6) :
    projTrace c d ⟨bt011010, zz⟩
      = Complex.I ^ (SS.PauliString.mk bt011010 zz).numY
          * (SS.signC (SS.bdot zz y1) (star (c y9) * c y1) + (SS.signC (SS.bdot zz y9) (star (c y1) * c y9)))
        + Complex.I ^ (SS.PauliString.mk bt011010 zz).numY
          * (SS.signC (SS.bdot zz z1) (star (d z9) * d z1) + (SS.signC (SS.bdot zz z9) (star (d z1) * d z9))) := by
  rw [projTrace, SS.innerC_pauliAct_support S0 S0 c c _ hc hc,
    SS.innerC_pauliAct_support S1 S1 d d _ hd hd]
  rw [show (SS.PauliString.mk bt011010 zz).x = bt011010 from rfl, incB_mk011010, incT_mk011010]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show (SS.PauliString.mk bt011010 zz).z = zz from rfl]
  rw [flB_mk011010_1, flB_mk011010_9, flT_mk011010_1, flT_mk011010_9]

theorem incB_mk100101 : S0.filter (fun s => SS.bxor s bt100101 ∈ S0) = {y0, y8} := by decide
theorem incT_mk100101 : S1.filter (fun s => SS.bxor s bt100101 ∈ S1) = {z0, z8} := by decide
theorem flB_mk100101_0 : SS.bxor y0 bt100101 = y8 := by decide
theorem flT_mk100101_0 : SS.bxor z0 bt100101 = z8 := by decide
theorem flB_mk100101_8 : SS.bxor y8 bt100101 = y0 := by decide
theorem flT_mk100101_8 : SS.bxor z8 bt100101 = z0 := by decide

/-- The projector trace of every Pauli with flip mask `100101`, as a bottom
bracket and a top bracket over the incidences of that mask. -/
theorem split_mk100101 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (zz : SS.BitString 6) :
    projTrace c d ⟨bt100101, zz⟩
      = Complex.I ^ (SS.PauliString.mk bt100101 zz).numY
          * (SS.signC (SS.bdot zz y0) (star (c y8) * c y0) + (SS.signC (SS.bdot zz y8) (star (c y0) * c y8)))
        + Complex.I ^ (SS.PauliString.mk bt100101 zz).numY
          * (SS.signC (SS.bdot zz z0) (star (d z8) * d z0) + (SS.signC (SS.bdot zz z8) (star (d z0) * d z8))) := by
  rw [projTrace, SS.innerC_pauliAct_support S0 S0 c c _ hc hc,
    SS.innerC_pauliAct_support S1 S1 d d _ hd hd]
  rw [show (SS.PauliString.mk bt100101 zz).x = bt100101 from rfl, incB_mk100101, incT_mk100101]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show (SS.PauliString.mk bt100101 zz).z = zz from rfl]
  rw [flB_mk100101_0, flB_mk100101_8, flT_mk100101_0, flT_mk100101_8]

theorem incB_mk100110 : S0.filter (fun s => SS.bxor s bt100110 ∈ S0) = {y1, y8} := by decide
theorem incT_mk100110 : S1.filter (fun s => SS.bxor s bt100110 ∈ S1) = {z1, z8} := by decide
theorem flB_mk100110_1 : SS.bxor y1 bt100110 = y8 := by decide
theorem flT_mk100110_1 : SS.bxor z1 bt100110 = z8 := by decide
theorem flB_mk100110_8 : SS.bxor y8 bt100110 = y1 := by decide
theorem flT_mk100110_8 : SS.bxor z8 bt100110 = z1 := by decide

/-- The projector trace of every Pauli with flip mask `100110`, as a bottom
bracket and a top bracket over the incidences of that mask. -/
theorem split_mk100110 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (zz : SS.BitString 6) :
    projTrace c d ⟨bt100110, zz⟩
      = Complex.I ^ (SS.PauliString.mk bt100110 zz).numY
          * (SS.signC (SS.bdot zz y1) (star (c y8) * c y1) + (SS.signC (SS.bdot zz y8) (star (c y1) * c y8)))
        + Complex.I ^ (SS.PauliString.mk bt100110 zz).numY
          * (SS.signC (SS.bdot zz z1) (star (d z8) * d z1) + (SS.signC (SS.bdot zz z8) (star (d z1) * d z8))) := by
  rw [projTrace, SS.innerC_pauliAct_support S0 S0 c c _ hc hc,
    SS.innerC_pauliAct_support S1 S1 d d _ hd hd]
  rw [show (SS.PauliString.mk bt100110 zz).x = bt100110 from rfl, incB_mk100110, incT_mk100110]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show (SS.PauliString.mk bt100110 zz).z = zz from rfl]
  rw [flB_mk100110_1, flB_mk100110_8, flT_mk100110_1, flT_mk100110_8]

theorem incB_mk101001 : S0.filter (fun s => SS.bxor s bt101001 ∈ S0) = {y0, y7} := by decide
theorem incT_mk101001 : S1.filter (fun s => SS.bxor s bt101001 ∈ S1) = {z0, z7} := by decide
theorem flB_mk101001_0 : SS.bxor y0 bt101001 = y7 := by decide
theorem flT_mk101001_0 : SS.bxor z0 bt101001 = z7 := by decide
theorem flB_mk101001_7 : SS.bxor y7 bt101001 = y0 := by decide
theorem flT_mk101001_7 : SS.bxor z7 bt101001 = z0 := by decide

/-- The projector trace of every Pauli with flip mask `101001`, as a bottom
bracket and a top bracket over the incidences of that mask. -/
theorem split_mk101001 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (zz : SS.BitString 6) :
    projTrace c d ⟨bt101001, zz⟩
      = Complex.I ^ (SS.PauliString.mk bt101001 zz).numY
          * (SS.signC (SS.bdot zz y0) (star (c y7) * c y0) + (SS.signC (SS.bdot zz y7) (star (c y0) * c y7)))
        + Complex.I ^ (SS.PauliString.mk bt101001 zz).numY
          * (SS.signC (SS.bdot zz z0) (star (d z7) * d z0) + (SS.signC (SS.bdot zz z7) (star (d z0) * d z7))) := by
  rw [projTrace, SS.innerC_pauliAct_support S0 S0 c c _ hc hc,
    SS.innerC_pauliAct_support S1 S1 d d _ hd hd]
  rw [show (SS.PauliString.mk bt101001 zz).x = bt101001 from rfl, incB_mk101001, incT_mk101001]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show (SS.PauliString.mk bt101001 zz).z = zz from rfl]
  rw [flB_mk101001_0, flB_mk101001_7, flT_mk101001_0, flT_mk101001_7]

theorem incB_mk101010 : S0.filter (fun s => SS.bxor s bt101010 ∈ S0) = {y1, y7} := by decide
theorem incT_mk101010 : S1.filter (fun s => SS.bxor s bt101010 ∈ S1) = {z1, z7} := by decide
theorem flB_mk101010_1 : SS.bxor y1 bt101010 = y7 := by decide
theorem flT_mk101010_1 : SS.bxor z1 bt101010 = z7 := by decide
theorem flB_mk101010_7 : SS.bxor y7 bt101010 = y1 := by decide
theorem flT_mk101010_7 : SS.bxor z7 bt101010 = z1 := by decide

/-- The projector trace of every Pauli with flip mask `101010`, as a bottom
bracket and a top bracket over the incidences of that mask. -/
theorem split_mk101010 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (zz : SS.BitString 6) :
    projTrace c d ⟨bt101010, zz⟩
      = Complex.I ^ (SS.PauliString.mk bt101010 zz).numY
          * (SS.signC (SS.bdot zz y1) (star (c y7) * c y1) + (SS.signC (SS.bdot zz y7) (star (c y1) * c y7)))
        + Complex.I ^ (SS.PauliString.mk bt101010 zz).numY
          * (SS.signC (SS.bdot zz z1) (star (d z7) * d z1) + (SS.signC (SS.bdot zz z7) (star (d z1) * d z7))) := by
  rw [projTrace, SS.innerC_pauliAct_support S0 S0 c c _ hc hc,
    SS.innerC_pauliAct_support S1 S1 d d _ hd hd]
  rw [show (SS.PauliString.mk bt101010 zz).x = bt101010 from rfl, incB_mk101010, incT_mk101010]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show (SS.PauliString.mk bt101010 zz).z = zz from rfl]
  rw [flB_mk101010_1, flB_mk101010_7, flT_mk101010_1, flT_mk101010_7]

theorem incB_mk110001 : S0.filter (fun s => SS.bxor s bt110001 ∈ S0) = {y0, y6} := by decide
theorem incT_mk110001 : S1.filter (fun s => SS.bxor s bt110001 ∈ S1) = {z0, z6} := by decide
theorem flB_mk110001_0 : SS.bxor y0 bt110001 = y6 := by decide
theorem flT_mk110001_0 : SS.bxor z0 bt110001 = z6 := by decide
theorem flB_mk110001_6 : SS.bxor y6 bt110001 = y0 := by decide
theorem flT_mk110001_6 : SS.bxor z6 bt110001 = z0 := by decide

/-- The projector trace of every Pauli with flip mask `110001`, as a bottom
bracket and a top bracket over the incidences of that mask. -/
theorem split_mk110001 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (zz : SS.BitString 6) :
    projTrace c d ⟨bt110001, zz⟩
      = Complex.I ^ (SS.PauliString.mk bt110001 zz).numY
          * (SS.signC (SS.bdot zz y0) (star (c y6) * c y0) + (SS.signC (SS.bdot zz y6) (star (c y0) * c y6)))
        + Complex.I ^ (SS.PauliString.mk bt110001 zz).numY
          * (SS.signC (SS.bdot zz z0) (star (d z6) * d z0) + (SS.signC (SS.bdot zz z6) (star (d z0) * d z6))) := by
  rw [projTrace, SS.innerC_pauliAct_support S0 S0 c c _ hc hc,
    SS.innerC_pauliAct_support S1 S1 d d _ hd hd]
  rw [show (SS.PauliString.mk bt110001 zz).x = bt110001 from rfl, incB_mk110001, incT_mk110001]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show (SS.PauliString.mk bt110001 zz).z = zz from rfl]
  rw [flB_mk110001_0, flB_mk110001_6, flT_mk110001_0, flT_mk110001_6]

theorem incB_mk110010 : S0.filter (fun s => SS.bxor s bt110010 ∈ S0) = {y1, y6} := by decide
theorem incT_mk110010 : S1.filter (fun s => SS.bxor s bt110010 ∈ S1) = {z1, z6} := by decide
theorem flB_mk110010_1 : SS.bxor y1 bt110010 = y6 := by decide
theorem flT_mk110010_1 : SS.bxor z1 bt110010 = z6 := by decide
theorem flB_mk110010_6 : SS.bxor y6 bt110010 = y1 := by decide
theorem flT_mk110010_6 : SS.bxor z6 bt110010 = z1 := by decide

/-- The projector trace of every Pauli with flip mask `110010`, as a bottom
bracket and a top bracket over the incidences of that mask. -/
theorem split_mk110010 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (zz : SS.BitString 6) :
    projTrace c d ⟨bt110010, zz⟩
      = Complex.I ^ (SS.PauliString.mk bt110010 zz).numY
          * (SS.signC (SS.bdot zz y1) (star (c y6) * c y1) + (SS.signC (SS.bdot zz y6) (star (c y1) * c y6)))
        + Complex.I ^ (SS.PauliString.mk bt110010 zz).numY
          * (SS.signC (SS.bdot zz z1) (star (d z6) * d z1) + (SS.signC (SS.bdot zz z6) (star (d z1) * d z6))) := by
  rw [projTrace, SS.innerC_pauliAct_support S0 S0 c c _ hc hc,
    SS.innerC_pauliAct_support S1 S1 d d _ hd hd]
  rw [show (SS.PauliString.mk bt110010 zz).x = bt110010 from rfl, incB_mk110010, incT_mk110010]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show (SS.PauliString.mk bt110010 zz).z = zz from rfl]
  rw [flB_mk110010_1, flB_mk110010_6, flT_mk110010_1, flT_mk110010_6]

theorem incB_mk000111 : S0.filter (fun s => SS.bxor s bt000111 ∈ S0) = {y2, y9, y3, y7, y4, y6} := by decide
theorem incT_mk000111 : S1.filter (fun s => SS.bxor s bt000111 ∈ S1) = {z2, z9, z3, z7, z4, z6} := by decide
theorem flB_mk000111_2 : SS.bxor y2 bt000111 = y9 := by decide
theorem flT_mk000111_2 : SS.bxor z2 bt000111 = z9 := by decide
theorem flB_mk000111_9 : SS.bxor y9 bt000111 = y2 := by decide
theorem flT_mk000111_9 : SS.bxor z9 bt000111 = z2 := by decide
theorem flB_mk000111_3 : SS.bxor y3 bt000111 = y7 := by decide
theorem flT_mk000111_3 : SS.bxor z3 bt000111 = z7 := by decide
theorem flB_mk000111_7 : SS.bxor y7 bt000111 = y3 := by decide
theorem flT_mk000111_7 : SS.bxor z7 bt000111 = z3 := by decide
theorem flB_mk000111_4 : SS.bxor y4 bt000111 = y6 := by decide
theorem flT_mk000111_4 : SS.bxor z4 bt000111 = z6 := by decide
theorem flB_mk000111_6 : SS.bxor y6 bt000111 = y4 := by decide
theorem flT_mk000111_6 : SS.bxor z6 bt000111 = z4 := by decide

/-- The projector trace of every Pauli with flip mask `000111`, as a bottom
bracket and a top bracket over the incidences of that mask. -/
theorem split_mk000111 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (zz : SS.BitString 6) :
    projTrace c d ⟨bt000111, zz⟩
      = Complex.I ^ (SS.PauliString.mk bt000111 zz).numY
          * (SS.signC (SS.bdot zz y2) (star (c y9) * c y2) + (SS.signC (SS.bdot zz y9) (star (c y2) * c y9) + (SS.signC (SS.bdot zz y3) (star (c y7) * c y3) + (SS.signC (SS.bdot zz y7) (star (c y3) * c y7) + (SS.signC (SS.bdot zz y4) (star (c y6) * c y4) + (SS.signC (SS.bdot zz y6) (star (c y4) * c y6)))))))
        + Complex.I ^ (SS.PauliString.mk bt000111 zz).numY
          * (SS.signC (SS.bdot zz z2) (star (d z9) * d z2) + (SS.signC (SS.bdot zz z9) (star (d z2) * d z9) + (SS.signC (SS.bdot zz z3) (star (d z7) * d z3) + (SS.signC (SS.bdot zz z7) (star (d z3) * d z7) + (SS.signC (SS.bdot zz z4) (star (d z6) * d z4) + (SS.signC (SS.bdot zz z6) (star (d z4) * d z6))))))) := by
  rw [projTrace, SS.innerC_pauliAct_support S0 S0 c c _ hc hc,
    SS.innerC_pauliAct_support S1 S1 d d _ hd hd]
  rw [show (SS.PauliString.mk bt000111 zz).x = bt000111 from rfl, incB_mk000111, incT_mk000111]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show (SS.PauliString.mk bt000111 zz).z = zz from rfl]
  rw [flB_mk000111_2, flB_mk000111_9, flB_mk000111_3, flB_mk000111_7, flB_mk000111_4, flB_mk000111_6, flT_mk000111_2, flT_mk000111_9, flT_mk000111_3, flT_mk000111_7, flT_mk000111_4, flT_mk000111_6]

theorem incB_mk001011 : S0.filter (fun s => SS.bxor s bt001011 ∈ S0) = {y2, y10, y3, y8, y5, y6} := by decide
theorem incT_mk001011 : S1.filter (fun s => SS.bxor s bt001011 ∈ S1) = {z2, z10, z3, z8, z5, z6} := by decide
theorem flB_mk001011_2 : SS.bxor y2 bt001011 = y10 := by decide
theorem flT_mk001011_2 : SS.bxor z2 bt001011 = z10 := by decide
theorem flB_mk001011_10 : SS.bxor y10 bt001011 = y2 := by decide
theorem flT_mk001011_10 : SS.bxor z10 bt001011 = z2 := by decide
theorem flB_mk001011_3 : SS.bxor y3 bt001011 = y8 := by decide
theorem flT_mk001011_3 : SS.bxor z3 bt001011 = z8 := by decide
theorem flB_mk001011_8 : SS.bxor y8 bt001011 = y3 := by decide
theorem flT_mk001011_8 : SS.bxor z8 bt001011 = z3 := by decide
theorem flB_mk001011_5 : SS.bxor y5 bt001011 = y6 := by decide
theorem flT_mk001011_5 : SS.bxor z5 bt001011 = z6 := by decide
theorem flB_mk001011_6 : SS.bxor y6 bt001011 = y5 := by decide
theorem flT_mk001011_6 : SS.bxor z6 bt001011 = z5 := by decide

/-- The projector trace of every Pauli with flip mask `001011`, as a bottom
bracket and a top bracket over the incidences of that mask. -/
theorem split_mk001011 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (zz : SS.BitString 6) :
    projTrace c d ⟨bt001011, zz⟩
      = Complex.I ^ (SS.PauliString.mk bt001011 zz).numY
          * (SS.signC (SS.bdot zz y2) (star (c y10) * c y2) + (SS.signC (SS.bdot zz y10) (star (c y2) * c y10) + (SS.signC (SS.bdot zz y3) (star (c y8) * c y3) + (SS.signC (SS.bdot zz y8) (star (c y3) * c y8) + (SS.signC (SS.bdot zz y5) (star (c y6) * c y5) + (SS.signC (SS.bdot zz y6) (star (c y5) * c y6)))))))
        + Complex.I ^ (SS.PauliString.mk bt001011 zz).numY
          * (SS.signC (SS.bdot zz z2) (star (d z10) * d z2) + (SS.signC (SS.bdot zz z10) (star (d z2) * d z10) + (SS.signC (SS.bdot zz z3) (star (d z8) * d z3) + (SS.signC (SS.bdot zz z8) (star (d z3) * d z8) + (SS.signC (SS.bdot zz z5) (star (d z6) * d z5) + (SS.signC (SS.bdot zz z6) (star (d z5) * d z6))))))) := by
  rw [projTrace, SS.innerC_pauliAct_support S0 S0 c c _ hc hc,
    SS.innerC_pauliAct_support S1 S1 d d _ hd hd]
  rw [show (SS.PauliString.mk bt001011 zz).x = bt001011 from rfl, incB_mk001011, incT_mk001011]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show (SS.PauliString.mk bt001011 zz).z = zz from rfl]
  rw [flB_mk001011_2, flB_mk001011_10, flB_mk001011_3, flB_mk001011_8, flB_mk001011_5, flB_mk001011_6, flT_mk001011_2, flT_mk001011_10, flT_mk001011_3, flT_mk001011_8, flT_mk001011_5, flT_mk001011_6]

theorem incB_mk010011 : S0.filter (fun s => SS.bxor s bt010011 ∈ S0) = {y2, y11, y4, y8, y5, y7} := by decide
theorem incT_mk010011 : S1.filter (fun s => SS.bxor s bt010011 ∈ S1) = {z2, z11, z4, z8, z5, z7} := by decide
theorem flB_mk010011_2 : SS.bxor y2 bt010011 = y11 := by decide
theorem flT_mk010011_2 : SS.bxor z2 bt010011 = z11 := by decide
theorem flB_mk010011_11 : SS.bxor y11 bt010011 = y2 := by decide
theorem flT_mk010011_11 : SS.bxor z11 bt010011 = z2 := by decide
theorem flB_mk010011_4 : SS.bxor y4 bt010011 = y8 := by decide
theorem flT_mk010011_4 : SS.bxor z4 bt010011 = z8 := by decide
theorem flB_mk010011_8 : SS.bxor y8 bt010011 = y4 := by decide
theorem flT_mk010011_8 : SS.bxor z8 bt010011 = z4 := by decide
theorem flB_mk010011_5 : SS.bxor y5 bt010011 = y7 := by decide
theorem flT_mk010011_5 : SS.bxor z5 bt010011 = z7 := by decide
theorem flB_mk010011_7 : SS.bxor y7 bt010011 = y5 := by decide
theorem flT_mk010011_7 : SS.bxor z7 bt010011 = z5 := by decide

/-- The projector trace of every Pauli with flip mask `010011`, as a bottom
bracket and a top bracket over the incidences of that mask. -/
theorem split_mk010011 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (zz : SS.BitString 6) :
    projTrace c d ⟨bt010011, zz⟩
      = Complex.I ^ (SS.PauliString.mk bt010011 zz).numY
          * (SS.signC (SS.bdot zz y2) (star (c y11) * c y2) + (SS.signC (SS.bdot zz y11) (star (c y2) * c y11) + (SS.signC (SS.bdot zz y4) (star (c y8) * c y4) + (SS.signC (SS.bdot zz y8) (star (c y4) * c y8) + (SS.signC (SS.bdot zz y5) (star (c y7) * c y5) + (SS.signC (SS.bdot zz y7) (star (c y5) * c y7)))))))
        + Complex.I ^ (SS.PauliString.mk bt010011 zz).numY
          * (SS.signC (SS.bdot zz z2) (star (d z11) * d z2) + (SS.signC (SS.bdot zz z11) (star (d z2) * d z11) + (SS.signC (SS.bdot zz z4) (star (d z8) * d z4) + (SS.signC (SS.bdot zz z8) (star (d z4) * d z8) + (SS.signC (SS.bdot zz z5) (star (d z7) * d z5) + (SS.signC (SS.bdot zz z7) (star (d z5) * d z7))))))) := by
  rw [projTrace, SS.innerC_pauliAct_support S0 S0 c c _ hc hc,
    SS.innerC_pauliAct_support S1 S1 d d _ hd hd]
  rw [show (SS.PauliString.mk bt010011 zz).x = bt010011 from rfl, incB_mk010011, incT_mk010011]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show (SS.PauliString.mk bt010011 zz).z = zz from rfl]
  rw [flB_mk010011_2, flB_mk010011_11, flB_mk010011_4, flB_mk010011_8, flB_mk010011_5, flB_mk010011_7, flT_mk010011_2, flT_mk010011_11, flT_mk010011_4, flT_mk010011_8, flT_mk010011_5, flT_mk010011_7]

theorem incB_mk100011 : S0.filter (fun s => SS.bxor s bt100011 ∈ S0) = {y3, y11, y4, y10, y5, y9} := by decide
theorem incT_mk100011 : S1.filter (fun s => SS.bxor s bt100011 ∈ S1) = {z3, z11, z4, z10, z5, z9} := by decide
theorem flB_mk100011_3 : SS.bxor y3 bt100011 = y11 := by decide
theorem flT_mk100011_3 : SS.bxor z3 bt100011 = z11 := by decide
theorem flB_mk100011_11 : SS.bxor y11 bt100011 = y3 := by decide
theorem flT_mk100011_11 : SS.bxor z11 bt100011 = z3 := by decide
theorem flB_mk100011_4 : SS.bxor y4 bt100011 = y10 := by decide
theorem flT_mk100011_4 : SS.bxor z4 bt100011 = z10 := by decide
theorem flB_mk100011_10 : SS.bxor y10 bt100011 = y4 := by decide
theorem flT_mk100011_10 : SS.bxor z10 bt100011 = z4 := by decide
theorem flB_mk100011_5 : SS.bxor y5 bt100011 = y9 := by decide
theorem flT_mk100011_5 : SS.bxor z5 bt100011 = z9 := by decide
theorem flB_mk100011_9 : SS.bxor y9 bt100011 = y5 := by decide
theorem flT_mk100011_9 : SS.bxor z9 bt100011 = z5 := by decide

/-- The projector trace of every Pauli with flip mask `100011`, as a bottom
bracket and a top bracket over the incidences of that mask. -/
theorem split_mk100011 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (zz : SS.BitString 6) :
    projTrace c d ⟨bt100011, zz⟩
      = Complex.I ^ (SS.PauliString.mk bt100011 zz).numY
          * (SS.signC (SS.bdot zz y3) (star (c y11) * c y3) + (SS.signC (SS.bdot zz y11) (star (c y3) * c y11) + (SS.signC (SS.bdot zz y4) (star (c y10) * c y4) + (SS.signC (SS.bdot zz y10) (star (c y4) * c y10) + (SS.signC (SS.bdot zz y5) (star (c y9) * c y5) + (SS.signC (SS.bdot zz y9) (star (c y5) * c y9)))))))
        + Complex.I ^ (SS.PauliString.mk bt100011 zz).numY
          * (SS.signC (SS.bdot zz z3) (star (d z11) * d z3) + (SS.signC (SS.bdot zz z11) (star (d z3) * d z11) + (SS.signC (SS.bdot zz z4) (star (d z10) * d z4) + (SS.signC (SS.bdot zz z10) (star (d z4) * d z10) + (SS.signC (SS.bdot zz z5) (star (d z9) * d z5) + (SS.signC (SS.bdot zz z9) (star (d z5) * d z9))))))) := by
  rw [projTrace, SS.innerC_pauliAct_support S0 S0 c c _ hc hc,
    SS.innerC_pauliAct_support S1 S1 d d _ hd hd]
  rw [show (SS.PauliString.mk bt100011 zz).x = bt100011 from rfl, incB_mk100011, incT_mk100011]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show (SS.PauliString.mk bt100011 zz).z = zz from rfl]
  rw [flB_mk100011_3, flB_mk100011_11, flB_mk100011_4, flB_mk100011_10, flB_mk100011_5, flB_mk100011_9, flT_mk100011_3, flT_mk100011_11, flT_mk100011_4, flT_mk100011_10, flT_mk100011_5, flT_mk100011_9]

/-! ## 8.  `A_3 = 0`: every weight-three projector trace vanishes -/

/-- The twenty-four flip masks of Hamming weight at most three that join two
points of a fiber.  Every weight-three Pauli has its flip mask here or has no
incidence at all. -/
def gm3 : Finset (SS.BitString 6) :=
  {bt000000, bt110000, bt101000, bt100100, bt011000, bt010100, bt001100, bt000011, bt001101, bt001110, bt010101, bt010110, bt011001, bt011010, bt100101, bt100110, bt101001, bt101010, bt110001, bt110010, bt000111, bt001011, bt010011, bt100011}

/-- Every other mask of Hamming weight at most three is inert on both fibers:
the chapter's residue condition, decided over all sixty-four masks. -/
theorem masks3 : ∀ f : SS.BitString 6, SS.hammingWt f ≤ 3 →
    f ∈ gm3 ∨ (S0.filter (fun s => SS.bxor s f ∈ S0) = ∅
        ∧ S1.filter (fun s => SS.bxor s f ∈ S1) = ∅) := by decide

theorem sgn3_mk000000 : ∀ zz : SS.BitString 6, (SS.PauliString.mk bt000000 zz).wt = 3 →
    SS.bdot zz z0 = !(SS.bdot zz y0)
      ∧ SS.bdot zz z1 = !(SS.bdot zz y1)
      ∧ SS.bdot zz z2 = !(SS.bdot zz y2)
      ∧ SS.bdot zz z3 = !(SS.bdot zz y3)
      ∧ SS.bdot zz z4 = !(SS.bdot zz y4)
      ∧ SS.bdot zz z5 = !(SS.bdot zz y5)
      ∧ SS.bdot zz z6 = !(SS.bdot zz y6)
      ∧ SS.bdot zz z7 = !(SS.bdot zz y7)
      ∧ SS.bdot zz z8 = !(SS.bdot zz y8)
      ∧ SS.bdot zz z9 = !(SS.bdot zz y9)
      ∧ SS.bdot zz z10 = !(SS.bdot zz y10)
      ∧ SS.bdot zz z11 = !(SS.bdot zz y11) := by decide

/-- A weight-three Pauli with trivial flip mask is diagonal with an odd
`z`-mask, and complementation reverses every one of its Walsh signs. -/
theorem a3_mk000000 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (tau : ℂ) (htf : TopForm c d tau) :
    ∀ zz : SS.BitString 6, (SS.PauliString.mk bt000000 zz).wt = 3 →
      projTrace c d ⟨bt000000, zz⟩ = 0 := by
  intro zz hz
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12⟩ := sgn3_mk000000 zz hz
  have uA0 : star (d z0) * d z0 = star (c y0) * c y0 := by
    rw [htf.t0]
    simp only [star_mul', star_star]
    linear_combination ((c y0 * star (c y0))) * htf.unit
  have uA1 : star (d z1) * d z1 = star (c y1) * c y1 := by
    rw [htf.t1]
    simp only [star_mul', star_star]
    linear_combination ((c y1 * star (c y1))) * htf.unit
  have uA2 : star (d z2) * d z2 = star (c y2) * c y2 := by
    rw [htf.t2]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y2 * star (c y2))) * htf.unit
  have uA3 : star (d z3) * d z3 = star (c y3) * c y3 := by
    rw [htf.t3]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y3 * star (c y3))) * htf.unit
  have uA4 : star (d z4) * d z4 = star (c y4) * c y4 := by
    rw [htf.t4]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y4 * star (c y4))) * htf.unit
  have uA5 : star (d z5) * d z5 = star (c y5) * c y5 := by
    rw [htf.t5]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y5 * star (c y5))) * htf.unit
  have uA6 : star (d z6) * d z6 = star (c y6) * c y6 := by
    rw [htf.t6]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y6 * star (c y6))) * htf.unit
  have uA7 : star (d z7) * d z7 = star (c y7) * c y7 := by
    rw [htf.t7]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y7 * star (c y7))) * htf.unit
  have uA8 : star (d z8) * d z8 = star (c y8) * c y8 := by
    rw [htf.t8]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y8 * star (c y8))) * htf.unit
  have uA9 : star (d z9) * d z9 = star (c y9) * c y9 := by
    rw [htf.t9]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y9 * star (c y9))) * htf.unit
  have uA10 : star (d z10) * d z10 = star (c y10) * c y10 := by
    rw [htf.t10]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y10 * star (c y10))) * htf.unit
  have uA11 : star (d z11) * d z11 = star (c y11) * c y11 := by
    rw [htf.t11]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y11 * star (c y11))) * htf.unit
  rw [split_mk000000 c d hc hd zz]
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12]
  rw [uA0, uA1, uA2, uA3, uA4, uA5, uA6, uA7, uA8, uA9, uA10, uA11]
  rw [← mul_add]
  refine mul_eq_zero_of_right _ ?_
  simp only [signC_not]
  ring

theorem sgn3_mk110000 : ∀ zz : SS.BitString 6, (SS.PauliString.mk bt110000 zz).wt = 3 →
    SS.bdot zz z2 = !(SS.bdot zz y3)
      ∧ SS.bdot zz z3 = !(SS.bdot zz y2)
      ∧ SS.bdot zz z7 = !(SS.bdot zz y9)
      ∧ SS.bdot zz z9 = !(SS.bdot zz y7)
      ∧ SS.bdot zz z8 = !(SS.bdot zz y10)
      ∧ SS.bdot zz z10 = !(SS.bdot zz y8) := by decide

/-- Weight-two flip mask `110000` carrying a weight-three Pauli: the extra `Z`
outside the mask makes complementation reverse every Walsh sign. -/
theorem a3_mk110000 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (tau : ℂ) (htf : TopForm c d tau) :
    ∀ zz : SS.BitString 6, (SS.PauliString.mk bt110000 zz).wt = 3 →
      projTrace c d ⟨bt110000, zz⟩ = 0 := by
  intro zz hz
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := sgn3_mk110000 zz hz
  have uA2 : star (d z3) * d z2 = star (c y2) * c y3 := by
    rw [htf.t2, htf.t3]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y3 * star (c y2))) * htf.unit
  have uB2 : star (d z2) * d z3 = star (c y3) * c y2 := by
    rw [htf.t2, htf.t3]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y2 * star (c y3))) * htf.unit
  have uA7 : star (d z9) * d z7 = star (c y7) * c y9 := by
    rw [htf.t7, htf.t9]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y9 * star (c y7))) * htf.unit
  have uB7 : star (d z7) * d z9 = star (c y9) * c y7 := by
    rw [htf.t7, htf.t9]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y7 * star (c y9))) * htf.unit
  have uA8 : star (d z10) * d z8 = star (c y8) * c y10 := by
    rw [htf.t8, htf.t10]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y10 * star (c y8))) * htf.unit
  have uB8 : star (d z8) * d z10 = star (c y10) * c y8 := by
    rw [htf.t8, htf.t10]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y8 * star (c y10))) * htf.unit
  rw [split_mk110000 c d hc hd zz]
  rw [e1, e2, e3, e4, e5, e6]
  rw [uA2, uB2, uA7, uB7, uA8, uB8]
  rw [← mul_add]
  refine mul_eq_zero_of_right _ ?_
  simp only [signC_not]
  ring

theorem sgn3_mk101000 : ∀ zz : SS.BitString 6, (SS.PauliString.mk bt101000 zz).wt = 3 →
    SS.bdot zz z2 = !(SS.bdot zz y4)
      ∧ SS.bdot zz z4 = !(SS.bdot zz y2)
      ∧ SS.bdot zz z6 = !(SS.bdot zz y9)
      ∧ SS.bdot zz z9 = !(SS.bdot zz y6)
      ∧ SS.bdot zz z8 = !(SS.bdot zz y11)
      ∧ SS.bdot zz z11 = !(SS.bdot zz y8) := by decide

/-- Weight-two flip mask `101000` carrying a weight-three Pauli: the extra `Z`
outside the mask makes complementation reverse every Walsh sign. -/
theorem a3_mk101000 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (tau : ℂ) (htf : TopForm c d tau) :
    ∀ zz : SS.BitString 6, (SS.PauliString.mk bt101000 zz).wt = 3 →
      projTrace c d ⟨bt101000, zz⟩ = 0 := by
  intro zz hz
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := sgn3_mk101000 zz hz
  have uA2 : star (d z4) * d z2 = star (c y2) * c y4 := by
    rw [htf.t2, htf.t4]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y4 * star (c y2))) * htf.unit
  have uB2 : star (d z2) * d z4 = star (c y4) * c y2 := by
    rw [htf.t2, htf.t4]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y2 * star (c y4))) * htf.unit
  have uA6 : star (d z9) * d z6 = star (c y6) * c y9 := by
    rw [htf.t6, htf.t9]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y9 * star (c y6))) * htf.unit
  have uB6 : star (d z6) * d z9 = star (c y9) * c y6 := by
    rw [htf.t6, htf.t9]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y6 * star (c y9))) * htf.unit
  have uA8 : star (d z11) * d z8 = star (c y8) * c y11 := by
    rw [htf.t8, htf.t11]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y11 * star (c y8))) * htf.unit
  have uB8 : star (d z8) * d z11 = star (c y11) * c y8 := by
    rw [htf.t8, htf.t11]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y8 * star (c y11))) * htf.unit
  rw [split_mk101000 c d hc hd zz]
  rw [e1, e2, e3, e4, e5, e6]
  rw [uA2, uB2, uA6, uB6, uA8, uB8]
  rw [← mul_add]
  refine mul_eq_zero_of_right _ ?_
  simp only [signC_not]
  ring

theorem sgn3_mk100100 : ∀ zz : SS.BitString 6, (SS.PauliString.mk bt100100 zz).wt = 3 →
    SS.bdot zz z2 = !(SS.bdot zz y5)
      ∧ SS.bdot zz z5 = !(SS.bdot zz y2)
      ∧ SS.bdot zz z6 = !(SS.bdot zz y10)
      ∧ SS.bdot zz z10 = !(SS.bdot zz y6)
      ∧ SS.bdot zz z7 = !(SS.bdot zz y11)
      ∧ SS.bdot zz z11 = !(SS.bdot zz y7) := by decide

/-- Weight-two flip mask `100100` carrying a weight-three Pauli: the extra `Z`
outside the mask makes complementation reverse every Walsh sign. -/
theorem a3_mk100100 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (tau : ℂ) (htf : TopForm c d tau) :
    ∀ zz : SS.BitString 6, (SS.PauliString.mk bt100100 zz).wt = 3 →
      projTrace c d ⟨bt100100, zz⟩ = 0 := by
  intro zz hz
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := sgn3_mk100100 zz hz
  have uA2 : star (d z5) * d z2 = star (c y2) * c y5 := by
    rw [htf.t2, htf.t5]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y5 * star (c y2))) * htf.unit
  have uB2 : star (d z2) * d z5 = star (c y5) * c y2 := by
    rw [htf.t2, htf.t5]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y2 * star (c y5))) * htf.unit
  have uA6 : star (d z10) * d z6 = star (c y6) * c y10 := by
    rw [htf.t6, htf.t10]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y10 * star (c y6))) * htf.unit
  have uB6 : star (d z6) * d z10 = star (c y10) * c y6 := by
    rw [htf.t6, htf.t10]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y6 * star (c y10))) * htf.unit
  have uA7 : star (d z11) * d z7 = star (c y7) * c y11 := by
    rw [htf.t7, htf.t11]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y11 * star (c y7))) * htf.unit
  have uB7 : star (d z7) * d z11 = star (c y11) * c y7 := by
    rw [htf.t7, htf.t11]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y7 * star (c y11))) * htf.unit
  rw [split_mk100100 c d hc hd zz]
  rw [e1, e2, e3, e4, e5, e6]
  rw [uA2, uB2, uA6, uB6, uA7, uB7]
  rw [← mul_add]
  refine mul_eq_zero_of_right _ ?_
  simp only [signC_not]
  ring

theorem sgn3_mk011000 : ∀ zz : SS.BitString 6, (SS.PauliString.mk bt011000 zz).wt = 3 →
    SS.bdot zz z3 = !(SS.bdot zz y4)
      ∧ SS.bdot zz z4 = !(SS.bdot zz y3)
      ∧ SS.bdot zz z6 = !(SS.bdot zz y7)
      ∧ SS.bdot zz z7 = !(SS.bdot zz y6)
      ∧ SS.bdot zz z10 = !(SS.bdot zz y11)
      ∧ SS.bdot zz z11 = !(SS.bdot zz y10) := by decide

/-- Weight-two flip mask `011000` carrying a weight-three Pauli: the extra `Z`
outside the mask makes complementation reverse every Walsh sign. -/
theorem a3_mk011000 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (tau : ℂ) (htf : TopForm c d tau) :
    ∀ zz : SS.BitString 6, (SS.PauliString.mk bt011000 zz).wt = 3 →
      projTrace c d ⟨bt011000, zz⟩ = 0 := by
  intro zz hz
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := sgn3_mk011000 zz hz
  have uA3 : star (d z4) * d z3 = star (c y3) * c y4 := by
    rw [htf.t3, htf.t4]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y4 * star (c y3))) * htf.unit
  have uB3 : star (d z3) * d z4 = star (c y4) * c y3 := by
    rw [htf.t3, htf.t4]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y3 * star (c y4))) * htf.unit
  have uA6 : star (d z7) * d z6 = star (c y6) * c y7 := by
    rw [htf.t6, htf.t7]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y7 * star (c y6))) * htf.unit
  have uB6 : star (d z6) * d z7 = star (c y7) * c y6 := by
    rw [htf.t6, htf.t7]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y6 * star (c y7))) * htf.unit
  have uA10 : star (d z11) * d z10 = star (c y10) * c y11 := by
    rw [htf.t10, htf.t11]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y11 * star (c y10))) * htf.unit
  have uB10 : star (d z10) * d z11 = star (c y11) * c y10 := by
    rw [htf.t10, htf.t11]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y10 * star (c y11))) * htf.unit
  rw [split_mk011000 c d hc hd zz]
  rw [e1, e2, e3, e4, e5, e6]
  rw [uA3, uB3, uA6, uB6, uA10, uB10]
  rw [← mul_add]
  refine mul_eq_zero_of_right _ ?_
  simp only [signC_not]
  ring

theorem sgn3_mk010100 : ∀ zz : SS.BitString 6, (SS.PauliString.mk bt010100 zz).wt = 3 →
    SS.bdot zz z3 = !(SS.bdot zz y5)
      ∧ SS.bdot zz z5 = !(SS.bdot zz y3)
      ∧ SS.bdot zz z6 = !(SS.bdot zz y8)
      ∧ SS.bdot zz z8 = !(SS.bdot zz y6)
      ∧ SS.bdot zz z9 = !(SS.bdot zz y11)
      ∧ SS.bdot zz z11 = !(SS.bdot zz y9) := by decide

/-- Weight-two flip mask `010100` carrying a weight-three Pauli: the extra `Z`
outside the mask makes complementation reverse every Walsh sign. -/
theorem a3_mk010100 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (tau : ℂ) (htf : TopForm c d tau) :
    ∀ zz : SS.BitString 6, (SS.PauliString.mk bt010100 zz).wt = 3 →
      projTrace c d ⟨bt010100, zz⟩ = 0 := by
  intro zz hz
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := sgn3_mk010100 zz hz
  have uA3 : star (d z5) * d z3 = star (c y3) * c y5 := by
    rw [htf.t3, htf.t5]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y5 * star (c y3))) * htf.unit
  have uB3 : star (d z3) * d z5 = star (c y5) * c y3 := by
    rw [htf.t3, htf.t5]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y3 * star (c y5))) * htf.unit
  have uA6 : star (d z8) * d z6 = star (c y6) * c y8 := by
    rw [htf.t6, htf.t8]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y8 * star (c y6))) * htf.unit
  have uB6 : star (d z6) * d z8 = star (c y8) * c y6 := by
    rw [htf.t6, htf.t8]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y6 * star (c y8))) * htf.unit
  have uA9 : star (d z11) * d z9 = star (c y9) * c y11 := by
    rw [htf.t9, htf.t11]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y11 * star (c y9))) * htf.unit
  have uB9 : star (d z9) * d z11 = star (c y11) * c y9 := by
    rw [htf.t9, htf.t11]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y9 * star (c y11))) * htf.unit
  rw [split_mk010100 c d hc hd zz]
  rw [e1, e2, e3, e4, e5, e6]
  rw [uA3, uB3, uA6, uB6, uA9, uB9]
  rw [← mul_add]
  refine mul_eq_zero_of_right _ ?_
  simp only [signC_not]
  ring

theorem sgn3_mk001100 : ∀ zz : SS.BitString 6, (SS.PauliString.mk bt001100 zz).wt = 3 →
    SS.bdot zz z4 = !(SS.bdot zz y5)
      ∧ SS.bdot zz z5 = !(SS.bdot zz y4)
      ∧ SS.bdot zz z7 = !(SS.bdot zz y8)
      ∧ SS.bdot zz z8 = !(SS.bdot zz y7)
      ∧ SS.bdot zz z9 = !(SS.bdot zz y10)
      ∧ SS.bdot zz z10 = !(SS.bdot zz y9) := by decide

/-- Weight-two flip mask `001100` carrying a weight-three Pauli: the extra `Z`
outside the mask makes complementation reverse every Walsh sign. -/
theorem a3_mk001100 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (tau : ℂ) (htf : TopForm c d tau) :
    ∀ zz : SS.BitString 6, (SS.PauliString.mk bt001100 zz).wt = 3 →
      projTrace c d ⟨bt001100, zz⟩ = 0 := by
  intro zz hz
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := sgn3_mk001100 zz hz
  have uA4 : star (d z5) * d z4 = star (c y4) * c y5 := by
    rw [htf.t4, htf.t5]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y5 * star (c y4))) * htf.unit
  have uB4 : star (d z4) * d z5 = star (c y5) * c y4 := by
    rw [htf.t4, htf.t5]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y4 * star (c y5))) * htf.unit
  have uA7 : star (d z8) * d z7 = star (c y7) * c y8 := by
    rw [htf.t7, htf.t8]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y8 * star (c y7))) * htf.unit
  have uB7 : star (d z7) * d z8 = star (c y8) * c y7 := by
    rw [htf.t7, htf.t8]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y7 * star (c y8))) * htf.unit
  have uA9 : star (d z10) * d z9 = star (c y9) * c y10 := by
    rw [htf.t9, htf.t10]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y10 * star (c y9))) * htf.unit
  have uB9 : star (d z9) * d z10 = star (c y10) * c y9 := by
    rw [htf.t9, htf.t10]
    simp only [star_neg, star_mul', star_star]
    linear_combination ((c y9 * star (c y10))) * htf.unit
  rw [split_mk001100 c d hc hd zz]
  rw [e1, e2, e3, e4, e5, e6]
  rw [uA4, uB4, uA7, uB7, uA9, uB9]
  rw [← mul_add]
  refine mul_eq_zero_of_right _ ?_
  simp only [signC_not]
  ring

theorem sgn3_mk000011 : ∀ zz : SS.BitString 6, (SS.PauliString.mk bt000011 zz).wt = 3 →
    SS.bdot zz z0 = !(SS.bdot zz y1)
      ∧ SS.bdot zz z1 = !(SS.bdot zz y0) := by decide

/-- Weight-two flip mask `000011` carrying a weight-three Pauli: the extra `Z`
outside the mask makes complementation reverse every Walsh sign. -/
theorem a3_mk000011 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (tau : ℂ) (htf : TopForm c d tau) :
    ∀ zz : SS.BitString 6, (SS.PauliString.mk bt000011 zz).wt = 3 →
      projTrace c d ⟨bt000011, zz⟩ = 0 := by
  intro zz hz
  obtain ⟨e1, e2⟩ := sgn3_mk000011 zz hz
  have uA0 : star (d z1) * d z0 = star (c y0) * c y1 := by
    rw [htf.t0, htf.t1]
    simp only [star_mul', star_star]
    linear_combination ((c y1 * star (c y0))) * htf.unit
  have uB0 : star (d z0) * d z1 = star (c y1) * c y0 := by
    rw [htf.t0, htf.t1]
    simp only [star_mul', star_star]
    linear_combination ((c y0 * star (c y1))) * htf.unit
  rw [split_mk000011 c d hc hd zz]
  rw [e1, e2]
  rw [uA0, uB0]
  rw [← mul_add]
  refine mul_eq_zero_of_right _ ?_
  simp only [signC_not]
  ring

theorem sgn3_mk001101 : ∀ zz : SS.BitString 6, (SS.PauliString.mk bt001101 zz).wt = 3 →
    SS.bdot zz z0 = SS.bdot zz y11
      ∧ SS.bdot zz z11 = SS.bdot zz y0 := by decide

/-- Weight-three mask `001101`: the anchor `u` and the edge `e34` carry opposite
`Theta`-signs, so the top bracket is the negative of the bottom one. -/
theorem a3_mk001101 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (tau : ℂ) (htf : TopForm c d tau) :
    ∀ zz : SS.BitString 6, (SS.PauliString.mk bt001101 zz).wt = 3 →
      projTrace c d ⟨bt001101, zz⟩ = 0 := by
  intro zz hz
  obtain ⟨e1, e2⟩ := sgn3_mk001101 zz hz
  have uA0 : star (d z11) * d z0 = -(star (c y0) * c y11) := by
    rw [htf.t0, htf.t11]
    simp only [star_neg, star_mul', star_star]
    linear_combination (-(c y11 * star (c y0))) * htf.unit
  have uB0 : star (d z0) * d z11 = -(star (c y11) * c y0) := by
    rw [htf.t0, htf.t11]
    simp only [star_mul', star_star]
    linear_combination (-(c y0 * star (c y11))) * htf.unit
  rw [split_mk001101 c d hc hd zz]
  rw [e1, e2]
  rw [uA0, uB0]
  rw [← mul_add]
  refine mul_eq_zero_of_right _ ?_
  simp only [signC_neg]
  ring

theorem sgn3_mk001110 : ∀ zz : SS.BitString 6, (SS.PauliString.mk bt001110 zz).wt = 3 →
    SS.bdot zz z1 = SS.bdot zz y11
      ∧ SS.bdot zz z11 = SS.bdot zz y1 := by decide

/-- Weight-three mask `001110`: the anchor `v` and the edge `e34` carry opposite
`Theta`-signs, so the top bracket is the negative of the bottom one. -/
theorem a3_mk001110 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (tau : ℂ) (htf : TopForm c d tau) :
    ∀ zz : SS.BitString 6, (SS.PauliString.mk bt001110 zz).wt = 3 →
      projTrace c d ⟨bt001110, zz⟩ = 0 := by
  intro zz hz
  obtain ⟨e1, e2⟩ := sgn3_mk001110 zz hz
  have uA1 : star (d z11) * d z1 = -(star (c y1) * c y11) := by
    rw [htf.t1, htf.t11]
    simp only [star_neg, star_mul', star_star]
    linear_combination (-(c y11 * star (c y1))) * htf.unit
  have uB1 : star (d z1) * d z11 = -(star (c y11) * c y1) := by
    rw [htf.t1, htf.t11]
    simp only [star_mul', star_star]
    linear_combination (-(c y1 * star (c y11))) * htf.unit
  rw [split_mk001110 c d hc hd zz]
  rw [e1, e2]
  rw [uA1, uB1]
  rw [← mul_add]
  refine mul_eq_zero_of_right _ ?_
  simp only [signC_neg]
  ring

theorem sgn3_mk010101 : ∀ zz : SS.BitString 6, (SS.PauliString.mk bt010101 zz).wt = 3 →
    SS.bdot zz z0 = SS.bdot zz y10
      ∧ SS.bdot zz z10 = SS.bdot zz y0 := by decide

/-- Weight-three mask `010101`: the anchor `u` and the edge `e24` carry opposite
`Theta`-signs, so the top bracket is the negative of the bottom one. -/
theorem a3_mk010101 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (tau : ℂ) (htf : TopForm c d tau) :
    ∀ zz : SS.BitString 6, (SS.PauliString.mk bt010101 zz).wt = 3 →
      projTrace c d ⟨bt010101, zz⟩ = 0 := by
  intro zz hz
  obtain ⟨e1, e2⟩ := sgn3_mk010101 zz hz
  have uA0 : star (d z10) * d z0 = -(star (c y0) * c y10) := by
    rw [htf.t0, htf.t10]
    simp only [star_neg, star_mul', star_star]
    linear_combination (-(c y10 * star (c y0))) * htf.unit
  have uB0 : star (d z0) * d z10 = -(star (c y10) * c y0) := by
    rw [htf.t0, htf.t10]
    simp only [star_mul', star_star]
    linear_combination (-(c y0 * star (c y10))) * htf.unit
  rw [split_mk010101 c d hc hd zz]
  rw [e1, e2]
  rw [uA0, uB0]
  rw [← mul_add]
  refine mul_eq_zero_of_right _ ?_
  simp only [signC_neg]
  ring

theorem sgn3_mk010110 : ∀ zz : SS.BitString 6, (SS.PauliString.mk bt010110 zz).wt = 3 →
    SS.bdot zz z1 = SS.bdot zz y10
      ∧ SS.bdot zz z10 = SS.bdot zz y1 := by decide

/-- Weight-three mask `010110`: the anchor `v` and the edge `e24` carry opposite
`Theta`-signs, so the top bracket is the negative of the bottom one. -/
theorem a3_mk010110 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (tau : ℂ) (htf : TopForm c d tau) :
    ∀ zz : SS.BitString 6, (SS.PauliString.mk bt010110 zz).wt = 3 →
      projTrace c d ⟨bt010110, zz⟩ = 0 := by
  intro zz hz
  obtain ⟨e1, e2⟩ := sgn3_mk010110 zz hz
  have uA1 : star (d z10) * d z1 = -(star (c y1) * c y10) := by
    rw [htf.t1, htf.t10]
    simp only [star_neg, star_mul', star_star]
    linear_combination (-(c y10 * star (c y1))) * htf.unit
  have uB1 : star (d z1) * d z10 = -(star (c y10) * c y1) := by
    rw [htf.t1, htf.t10]
    simp only [star_mul', star_star]
    linear_combination (-(c y1 * star (c y10))) * htf.unit
  rw [split_mk010110 c d hc hd zz]
  rw [e1, e2]
  rw [uA1, uB1]
  rw [← mul_add]
  refine mul_eq_zero_of_right _ ?_
  simp only [signC_neg]
  ring

theorem sgn3_mk011001 : ∀ zz : SS.BitString 6, (SS.PauliString.mk bt011001 zz).wt = 3 →
    SS.bdot zz z0 = SS.bdot zz y9
      ∧ SS.bdot zz z9 = SS.bdot zz y0 := by decide

/-- Weight-three mask `011001`: the anchor `u` and the edge `e23` carry opposite
`Theta`-signs, so the top bracket is the negative of the bottom one. -/
theorem a3_mk011001 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (tau : ℂ) (htf : TopForm c d tau) :
    ∀ zz : SS.BitString 6, (SS.PauliString.mk bt011001 zz).wt = 3 →
      projTrace c d ⟨bt011001, zz⟩ = 0 := by
  intro zz hz
  obtain ⟨e1, e2⟩ := sgn3_mk011001 zz hz
  have uA0 : star (d z9) * d z0 = -(star (c y0) * c y9) := by
    rw [htf.t0, htf.t9]
    simp only [star_neg, star_mul', star_star]
    linear_combination (-(c y9 * star (c y0))) * htf.unit
  have uB0 : star (d z0) * d z9 = -(star (c y9) * c y0) := by
    rw [htf.t0, htf.t9]
    simp only [star_mul', star_star]
    linear_combination (-(c y0 * star (c y9))) * htf.unit
  rw [split_mk011001 c d hc hd zz]
  rw [e1, e2]
  rw [uA0, uB0]
  rw [← mul_add]
  refine mul_eq_zero_of_right _ ?_
  simp only [signC_neg]
  ring

theorem sgn3_mk011010 : ∀ zz : SS.BitString 6, (SS.PauliString.mk bt011010 zz).wt = 3 →
    SS.bdot zz z1 = SS.bdot zz y9
      ∧ SS.bdot zz z9 = SS.bdot zz y1 := by decide

/-- Weight-three mask `011010`: the anchor `v` and the edge `e23` carry opposite
`Theta`-signs, so the top bracket is the negative of the bottom one. -/
theorem a3_mk011010 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (tau : ℂ) (htf : TopForm c d tau) :
    ∀ zz : SS.BitString 6, (SS.PauliString.mk bt011010 zz).wt = 3 →
      projTrace c d ⟨bt011010, zz⟩ = 0 := by
  intro zz hz
  obtain ⟨e1, e2⟩ := sgn3_mk011010 zz hz
  have uA1 : star (d z9) * d z1 = -(star (c y1) * c y9) := by
    rw [htf.t1, htf.t9]
    simp only [star_neg, star_mul', star_star]
    linear_combination (-(c y9 * star (c y1))) * htf.unit
  have uB1 : star (d z1) * d z9 = -(star (c y9) * c y1) := by
    rw [htf.t1, htf.t9]
    simp only [star_mul', star_star]
    linear_combination (-(c y1 * star (c y9))) * htf.unit
  rw [split_mk011010 c d hc hd zz]
  rw [e1, e2]
  rw [uA1, uB1]
  rw [← mul_add]
  refine mul_eq_zero_of_right _ ?_
  simp only [signC_neg]
  ring

theorem sgn3_mk100101 : ∀ zz : SS.BitString 6, (SS.PauliString.mk bt100101 zz).wt = 3 →
    SS.bdot zz z0 = SS.bdot zz y8
      ∧ SS.bdot zz z8 = SS.bdot zz y0 := by decide

/-- Weight-three mask `100101`: the anchor `u` and the edge `e14` carry opposite
`Theta`-signs, so the top bracket is the negative of the bottom one. -/
theorem a3_mk100101 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (tau : ℂ) (htf : TopForm c d tau) :
    ∀ zz : SS.BitString 6, (SS.PauliString.mk bt100101 zz).wt = 3 →
      projTrace c d ⟨bt100101, zz⟩ = 0 := by
  intro zz hz
  obtain ⟨e1, e2⟩ := sgn3_mk100101 zz hz
  have uA0 : star (d z8) * d z0 = -(star (c y0) * c y8) := by
    rw [htf.t0, htf.t8]
    simp only [star_neg, star_mul', star_star]
    linear_combination (-(c y8 * star (c y0))) * htf.unit
  have uB0 : star (d z0) * d z8 = -(star (c y8) * c y0) := by
    rw [htf.t0, htf.t8]
    simp only [star_mul', star_star]
    linear_combination (-(c y0 * star (c y8))) * htf.unit
  rw [split_mk100101 c d hc hd zz]
  rw [e1, e2]
  rw [uA0, uB0]
  rw [← mul_add]
  refine mul_eq_zero_of_right _ ?_
  simp only [signC_neg]
  ring

theorem sgn3_mk100110 : ∀ zz : SS.BitString 6, (SS.PauliString.mk bt100110 zz).wt = 3 →
    SS.bdot zz z1 = SS.bdot zz y8
      ∧ SS.bdot zz z8 = SS.bdot zz y1 := by decide

/-- Weight-three mask `100110`: the anchor `v` and the edge `e14` carry opposite
`Theta`-signs, so the top bracket is the negative of the bottom one. -/
theorem a3_mk100110 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (tau : ℂ) (htf : TopForm c d tau) :
    ∀ zz : SS.BitString 6, (SS.PauliString.mk bt100110 zz).wt = 3 →
      projTrace c d ⟨bt100110, zz⟩ = 0 := by
  intro zz hz
  obtain ⟨e1, e2⟩ := sgn3_mk100110 zz hz
  have uA1 : star (d z8) * d z1 = -(star (c y1) * c y8) := by
    rw [htf.t1, htf.t8]
    simp only [star_neg, star_mul', star_star]
    linear_combination (-(c y8 * star (c y1))) * htf.unit
  have uB1 : star (d z1) * d z8 = -(star (c y8) * c y1) := by
    rw [htf.t1, htf.t8]
    simp only [star_mul', star_star]
    linear_combination (-(c y1 * star (c y8))) * htf.unit
  rw [split_mk100110 c d hc hd zz]
  rw [e1, e2]
  rw [uA1, uB1]
  rw [← mul_add]
  refine mul_eq_zero_of_right _ ?_
  simp only [signC_neg]
  ring

theorem sgn3_mk101001 : ∀ zz : SS.BitString 6, (SS.PauliString.mk bt101001 zz).wt = 3 →
    SS.bdot zz z0 = SS.bdot zz y7
      ∧ SS.bdot zz z7 = SS.bdot zz y0 := by decide

/-- Weight-three mask `101001`: the anchor `u` and the edge `e13` carry opposite
`Theta`-signs, so the top bracket is the negative of the bottom one. -/
theorem a3_mk101001 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (tau : ℂ) (htf : TopForm c d tau) :
    ∀ zz : SS.BitString 6, (SS.PauliString.mk bt101001 zz).wt = 3 →
      projTrace c d ⟨bt101001, zz⟩ = 0 := by
  intro zz hz
  obtain ⟨e1, e2⟩ := sgn3_mk101001 zz hz
  have uA0 : star (d z7) * d z0 = -(star (c y0) * c y7) := by
    rw [htf.t0, htf.t7]
    simp only [star_neg, star_mul', star_star]
    linear_combination (-(c y7 * star (c y0))) * htf.unit
  have uB0 : star (d z0) * d z7 = -(star (c y7) * c y0) := by
    rw [htf.t0, htf.t7]
    simp only [star_mul', star_star]
    linear_combination (-(c y0 * star (c y7))) * htf.unit
  rw [split_mk101001 c d hc hd zz]
  rw [e1, e2]
  rw [uA0, uB0]
  rw [← mul_add]
  refine mul_eq_zero_of_right _ ?_
  simp only [signC_neg]
  ring

theorem sgn3_mk101010 : ∀ zz : SS.BitString 6, (SS.PauliString.mk bt101010 zz).wt = 3 →
    SS.bdot zz z1 = SS.bdot zz y7
      ∧ SS.bdot zz z7 = SS.bdot zz y1 := by decide

/-- Weight-three mask `101010`: the anchor `v` and the edge `e13` carry opposite
`Theta`-signs, so the top bracket is the negative of the bottom one. -/
theorem a3_mk101010 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (tau : ℂ) (htf : TopForm c d tau) :
    ∀ zz : SS.BitString 6, (SS.PauliString.mk bt101010 zz).wt = 3 →
      projTrace c d ⟨bt101010, zz⟩ = 0 := by
  intro zz hz
  obtain ⟨e1, e2⟩ := sgn3_mk101010 zz hz
  have uA1 : star (d z7) * d z1 = -(star (c y1) * c y7) := by
    rw [htf.t1, htf.t7]
    simp only [star_neg, star_mul', star_star]
    linear_combination (-(c y7 * star (c y1))) * htf.unit
  have uB1 : star (d z1) * d z7 = -(star (c y7) * c y1) := by
    rw [htf.t1, htf.t7]
    simp only [star_mul', star_star]
    linear_combination (-(c y1 * star (c y7))) * htf.unit
  rw [split_mk101010 c d hc hd zz]
  rw [e1, e2]
  rw [uA1, uB1]
  rw [← mul_add]
  refine mul_eq_zero_of_right _ ?_
  simp only [signC_neg]
  ring

theorem sgn3_mk110001 : ∀ zz : SS.BitString 6, (SS.PauliString.mk bt110001 zz).wt = 3 →
    SS.bdot zz z0 = SS.bdot zz y6
      ∧ SS.bdot zz z6 = SS.bdot zz y0 := by decide

/-- Weight-three mask `110001`: the anchor `u` and the edge `e12` carry opposite
`Theta`-signs, so the top bracket is the negative of the bottom one. -/
theorem a3_mk110001 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (tau : ℂ) (htf : TopForm c d tau) :
    ∀ zz : SS.BitString 6, (SS.PauliString.mk bt110001 zz).wt = 3 →
      projTrace c d ⟨bt110001, zz⟩ = 0 := by
  intro zz hz
  obtain ⟨e1, e2⟩ := sgn3_mk110001 zz hz
  have uA0 : star (d z6) * d z0 = -(star (c y0) * c y6) := by
    rw [htf.t0, htf.t6]
    simp only [star_neg, star_mul', star_star]
    linear_combination (-(c y6 * star (c y0))) * htf.unit
  have uB0 : star (d z0) * d z6 = -(star (c y6) * c y0) := by
    rw [htf.t0, htf.t6]
    simp only [star_mul', star_star]
    linear_combination (-(c y0 * star (c y6))) * htf.unit
  rw [split_mk110001 c d hc hd zz]
  rw [e1, e2]
  rw [uA0, uB0]
  rw [← mul_add]
  refine mul_eq_zero_of_right _ ?_
  simp only [signC_neg]
  ring

theorem sgn3_mk110010 : ∀ zz : SS.BitString 6, (SS.PauliString.mk bt110010 zz).wt = 3 →
    SS.bdot zz z1 = SS.bdot zz y6
      ∧ SS.bdot zz z6 = SS.bdot zz y1 := by decide

/-- Weight-three mask `110010`: the anchor `v` and the edge `e12` carry opposite
`Theta`-signs, so the top bracket is the negative of the bottom one. -/
theorem a3_mk110010 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (tau : ℂ) (htf : TopForm c d tau) :
    ∀ zz : SS.BitString 6, (SS.PauliString.mk bt110010 zz).wt = 3 →
      projTrace c d ⟨bt110010, zz⟩ = 0 := by
  intro zz hz
  obtain ⟨e1, e2⟩ := sgn3_mk110010 zz hz
  have uA1 : star (d z6) * d z1 = -(star (c y1) * c y6) := by
    rw [htf.t1, htf.t6]
    simp only [star_neg, star_mul', star_star]
    linear_combination (-(c y6 * star (c y1))) * htf.unit
  have uB1 : star (d z1) * d z6 = -(star (c y6) * c y1) := by
    rw [htf.t1, htf.t6]
    simp only [star_mul', star_star]
    linear_combination (-(c y1 * star (c y6))) * htf.unit
  rw [split_mk110010 c d hc hd zz]
  rw [e1, e2]
  rw [uA1, uB1]
  rw [← mul_add]
  refine mul_eq_zero_of_right _ ?_
  simp only [signC_neg]
  ring

theorem sgn3_mk000111 : ∀ zz : SS.BitString 6, (SS.PauliString.mk bt000111 zz).wt = 3 →
    SS.bdot zz y3 = SS.bdot zz y2
      ∧ SS.bdot zz y7 = SS.bdot zz y9
      ∧ SS.bdot zz y4 = SS.bdot zz y2
      ∧ SS.bdot zz y6 = SS.bdot zz y9
      ∧ SS.bdot zz z3 = SS.bdot zz z2
      ∧ SS.bdot zz z7 = SS.bdot zz z9
      ∧ SS.bdot zz z4 = SS.bdot zz z2
      ∧ SS.bdot zz z6 = SS.bdot zz z9 := by decide

/-- Exceptional weight-three mask `000111` -- the chapter's `f = {i,5,6}`.  Its
three incidences carry a common Walsh sign on each side, so each bracket is a
triangle sum opposite the flipped vertex. -/
theorem a3_mk000111 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (tau : ℂ) (htf : TopForm c d tau)
    (htri : star (c y2) * c y9 + star (c y3) * c y7 + star (c y4) * c y6 = 0) :
    ∀ zz : SS.BitString 6, (SS.PauliString.mk bt000111 zz).wt = 3 →
      projTrace c d ⟨bt000111, zz⟩ = 0 := by
  have hs := congrArg star htri
  simp only [star_add, star_mul', star_star, star_zero] at hs
  have hX : star (c y9) * c y2 + star (c y7) * c y3 + star (c y6) * c y4 = 0 := by linear_combination hs
  intro zz hz
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := sgn3_mk000111 zz hz
  have uA2 : star (d z9) * d z2 = star (c y2) * c y9 := by
    rw [htf.t2, htf.t9]
    simp only [star_neg, star_mul', star_star]
    linear_combination (c y9 * star (c y2)) * htf.unit
  have uB2 : star (d z2) * d z9 = star (c y9) * c y2 := by
    rw [htf.t2, htf.t9]
    simp only [star_neg, star_mul', star_star]
    linear_combination (c y2 * star (c y9)) * htf.unit
  have uA3 : star (d z7) * d z3 = star (c y3) * c y7 := by
    rw [htf.t3, htf.t7]
    simp only [star_neg, star_mul', star_star]
    linear_combination (c y7 * star (c y3)) * htf.unit
  have uB3 : star (d z3) * d z7 = star (c y7) * c y3 := by
    rw [htf.t3, htf.t7]
    simp only [star_neg, star_mul', star_star]
    linear_combination (c y3 * star (c y7)) * htf.unit
  have uA4 : star (d z6) * d z4 = star (c y4) * c y6 := by
    rw [htf.t4, htf.t6]
    simp only [star_neg, star_mul', star_star]
    linear_combination (c y6 * star (c y4)) * htf.unit
  have uB4 : star (d z4) * d z6 = star (c y6) * c y4 := by
    rw [htf.t4, htf.t6]
    simp only [star_neg, star_mul', star_star]
    linear_combination (c y4 * star (c y6)) * htf.unit
  rw [split_mk000111 c d hc hd zz]
  rw [e1, e2, e3, e4, e5, e6, e7, e8]
  rw [uA2, uB2, uA3, uB3, uA4, uB4]
  rw [← mul_add]
  refine mul_eq_zero_of_right _ ?_
  have hb := sixSum (SS.bdot zz y2) (SS.bdot zz y9) hX htri
  have ht := sixSum (SS.bdot zz z2) (SS.bdot zz z9) htri hX
  linear_combination hb + ht

theorem sgn3_mk001011 : ∀ zz : SS.BitString 6, (SS.PauliString.mk bt001011 zz).wt = 3 →
    SS.bdot zz y3 = SS.bdot zz y2
      ∧ SS.bdot zz y8 = SS.bdot zz y10
      ∧ SS.bdot zz y5 = SS.bdot zz y2
      ∧ SS.bdot zz y6 = SS.bdot zz y10
      ∧ SS.bdot zz z3 = SS.bdot zz z2
      ∧ SS.bdot zz z8 = SS.bdot zz z10
      ∧ SS.bdot zz z5 = SS.bdot zz z2
      ∧ SS.bdot zz z6 = SS.bdot zz z10 := by decide

/-- Exceptional weight-three mask `001011` -- the chapter's `f = {i,5,6}`.  Its
three incidences carry a common Walsh sign on each side, so each bracket is a
triangle sum opposite the flipped vertex. -/
theorem a3_mk001011 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (tau : ℂ) (htf : TopForm c d tau)
    (htri : star (c y2) * c y10 + star (c y3) * c y8 + star (c y5) * c y6 = 0) :
    ∀ zz : SS.BitString 6, (SS.PauliString.mk bt001011 zz).wt = 3 →
      projTrace c d ⟨bt001011, zz⟩ = 0 := by
  have hs := congrArg star htri
  simp only [star_add, star_mul', star_star, star_zero] at hs
  have hX : star (c y10) * c y2 + star (c y8) * c y3 + star (c y6) * c y5 = 0 := by linear_combination hs
  intro zz hz
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := sgn3_mk001011 zz hz
  have uA2 : star (d z10) * d z2 = star (c y2) * c y10 := by
    rw [htf.t2, htf.t10]
    simp only [star_neg, star_mul', star_star]
    linear_combination (c y10 * star (c y2)) * htf.unit
  have uB2 : star (d z2) * d z10 = star (c y10) * c y2 := by
    rw [htf.t2, htf.t10]
    simp only [star_neg, star_mul', star_star]
    linear_combination (c y2 * star (c y10)) * htf.unit
  have uA3 : star (d z8) * d z3 = star (c y3) * c y8 := by
    rw [htf.t3, htf.t8]
    simp only [star_neg, star_mul', star_star]
    linear_combination (c y8 * star (c y3)) * htf.unit
  have uB3 : star (d z3) * d z8 = star (c y8) * c y3 := by
    rw [htf.t3, htf.t8]
    simp only [star_neg, star_mul', star_star]
    linear_combination (c y3 * star (c y8)) * htf.unit
  have uA5 : star (d z6) * d z5 = star (c y5) * c y6 := by
    rw [htf.t5, htf.t6]
    simp only [star_neg, star_mul', star_star]
    linear_combination (c y6 * star (c y5)) * htf.unit
  have uB5 : star (d z5) * d z6 = star (c y6) * c y5 := by
    rw [htf.t5, htf.t6]
    simp only [star_neg, star_mul', star_star]
    linear_combination (c y5 * star (c y6)) * htf.unit
  rw [split_mk001011 c d hc hd zz]
  rw [e1, e2, e3, e4, e5, e6, e7, e8]
  rw [uA2, uB2, uA3, uB3, uA5, uB5]
  rw [← mul_add]
  refine mul_eq_zero_of_right _ ?_
  have hb := sixSum (SS.bdot zz y2) (SS.bdot zz y10) hX htri
  have ht := sixSum (SS.bdot zz z2) (SS.bdot zz z10) htri hX
  linear_combination hb + ht

theorem sgn3_mk010011 : ∀ zz : SS.BitString 6, (SS.PauliString.mk bt010011 zz).wt = 3 →
    SS.bdot zz y4 = SS.bdot zz y2
      ∧ SS.bdot zz y8 = SS.bdot zz y11
      ∧ SS.bdot zz y5 = SS.bdot zz y2
      ∧ SS.bdot zz y7 = SS.bdot zz y11
      ∧ SS.bdot zz z4 = SS.bdot zz z2
      ∧ SS.bdot zz z8 = SS.bdot zz z11
      ∧ SS.bdot zz z5 = SS.bdot zz z2
      ∧ SS.bdot zz z7 = SS.bdot zz z11 := by decide

/-- Exceptional weight-three mask `010011` -- the chapter's `f = {i,5,6}`.  Its
three incidences carry a common Walsh sign on each side, so each bracket is a
triangle sum opposite the flipped vertex. -/
theorem a3_mk010011 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (tau : ℂ) (htf : TopForm c d tau)
    (htri : star (c y2) * c y11 + star (c y4) * c y8 + star (c y5) * c y7 = 0) :
    ∀ zz : SS.BitString 6, (SS.PauliString.mk bt010011 zz).wt = 3 →
      projTrace c d ⟨bt010011, zz⟩ = 0 := by
  have hs := congrArg star htri
  simp only [star_add, star_mul', star_star, star_zero] at hs
  have hX : star (c y11) * c y2 + star (c y8) * c y4 + star (c y7) * c y5 = 0 := by linear_combination hs
  intro zz hz
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := sgn3_mk010011 zz hz
  have uA2 : star (d z11) * d z2 = star (c y2) * c y11 := by
    rw [htf.t2, htf.t11]
    simp only [star_neg, star_mul', star_star]
    linear_combination (c y11 * star (c y2)) * htf.unit
  have uB2 : star (d z2) * d z11 = star (c y11) * c y2 := by
    rw [htf.t2, htf.t11]
    simp only [star_neg, star_mul', star_star]
    linear_combination (c y2 * star (c y11)) * htf.unit
  have uA4 : star (d z8) * d z4 = star (c y4) * c y8 := by
    rw [htf.t4, htf.t8]
    simp only [star_neg, star_mul', star_star]
    linear_combination (c y8 * star (c y4)) * htf.unit
  have uB4 : star (d z4) * d z8 = star (c y8) * c y4 := by
    rw [htf.t4, htf.t8]
    simp only [star_neg, star_mul', star_star]
    linear_combination (c y4 * star (c y8)) * htf.unit
  have uA5 : star (d z7) * d z5 = star (c y5) * c y7 := by
    rw [htf.t5, htf.t7]
    simp only [star_neg, star_mul', star_star]
    linear_combination (c y7 * star (c y5)) * htf.unit
  have uB5 : star (d z5) * d z7 = star (c y7) * c y5 := by
    rw [htf.t5, htf.t7]
    simp only [star_neg, star_mul', star_star]
    linear_combination (c y5 * star (c y7)) * htf.unit
  rw [split_mk010011 c d hc hd zz]
  rw [e1, e2, e3, e4, e5, e6, e7, e8]
  rw [uA2, uB2, uA4, uB4, uA5, uB5]
  rw [← mul_add]
  refine mul_eq_zero_of_right _ ?_
  have hb := sixSum (SS.bdot zz y2) (SS.bdot zz y11) hX htri
  have ht := sixSum (SS.bdot zz z2) (SS.bdot zz z11) htri hX
  linear_combination hb + ht

theorem sgn3_mk100011 : ∀ zz : SS.BitString 6, (SS.PauliString.mk bt100011 zz).wt = 3 →
    SS.bdot zz y4 = SS.bdot zz y3
      ∧ SS.bdot zz y10 = SS.bdot zz y11
      ∧ SS.bdot zz y5 = SS.bdot zz y3
      ∧ SS.bdot zz y9 = SS.bdot zz y11
      ∧ SS.bdot zz z4 = SS.bdot zz z3
      ∧ SS.bdot zz z10 = SS.bdot zz z11
      ∧ SS.bdot zz z5 = SS.bdot zz z3
      ∧ SS.bdot zz z9 = SS.bdot zz z11 := by decide

/-- Exceptional weight-three mask `100011` -- the chapter's `f = {i,5,6}`.  Its
three incidences carry a common Walsh sign on each side, so each bracket is a
triangle sum opposite the flipped vertex. -/
theorem a3_mk100011 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (tau : ℂ) (htf : TopForm c d tau)
    (htri : star (c y3) * c y11 + star (c y4) * c y10 + star (c y5) * c y9 = 0) :
    ∀ zz : SS.BitString 6, (SS.PauliString.mk bt100011 zz).wt = 3 →
      projTrace c d ⟨bt100011, zz⟩ = 0 := by
  have hs := congrArg star htri
  simp only [star_add, star_mul', star_star, star_zero] at hs
  have hX : star (c y11) * c y3 + star (c y10) * c y4 + star (c y9) * c y5 = 0 := by linear_combination hs
  intro zz hz
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := sgn3_mk100011 zz hz
  have uA3 : star (d z11) * d z3 = star (c y3) * c y11 := by
    rw [htf.t3, htf.t11]
    simp only [star_neg, star_mul', star_star]
    linear_combination (c y11 * star (c y3)) * htf.unit
  have uB3 : star (d z3) * d z11 = star (c y11) * c y3 := by
    rw [htf.t3, htf.t11]
    simp only [star_neg, star_mul', star_star]
    linear_combination (c y3 * star (c y11)) * htf.unit
  have uA4 : star (d z10) * d z4 = star (c y4) * c y10 := by
    rw [htf.t4, htf.t10]
    simp only [star_neg, star_mul', star_star]
    linear_combination (c y10 * star (c y4)) * htf.unit
  have uB4 : star (d z4) * d z10 = star (c y10) * c y4 := by
    rw [htf.t4, htf.t10]
    simp only [star_neg, star_mul', star_star]
    linear_combination (c y4 * star (c y10)) * htf.unit
  have uA5 : star (d z9) * d z5 = star (c y5) * c y9 := by
    rw [htf.t5, htf.t9]
    simp only [star_neg, star_mul', star_star]
    linear_combination (c y9 * star (c y5)) * htf.unit
  have uB5 : star (d z5) * d z9 = star (c y9) * c y5 := by
    rw [htf.t5, htf.t9]
    simp only [star_neg, star_mul', star_star]
    linear_combination (c y5 * star (c y9)) * htf.unit
  rw [split_mk100011 c d hc hd zz]
  rw [e1, e2, e3, e4, e5, e6, e7, e8]
  rw [uA3, uB3, uA4, uB4, uA5, uB5]
  rw [← mul_add]
  refine mul_eq_zero_of_right _ ?_
  have hb := sixSum (SS.bdot zz y3) (SS.bdot zz y11) hX htri
  have ht := sixSum (SS.bdot zz z3) (SS.bdot zz z11) htri hX
  linear_combination hb + ht

/-! ## 9.  The diagonal masks: the identity and the fifteen `Z_i Z_j` rows -/

theorem sgB_000000_0 : SS.bdot bt000000 y0 = false := by decide
theorem sgT_000000_0 : SS.bdot bt000000 z0 = false := by decide
theorem sgB_000000_1 : SS.bdot bt000000 y1 = false := by decide
theorem sgT_000000_1 : SS.bdot bt000000 z1 = false := by decide
theorem sgB_000000_2 : SS.bdot bt000000 y2 = false := by decide
theorem sgT_000000_2 : SS.bdot bt000000 z2 = false := by decide
theorem sgB_000000_3 : SS.bdot bt000000 y3 = false := by decide
theorem sgT_000000_3 : SS.bdot bt000000 z3 = false := by decide
theorem sgB_000000_4 : SS.bdot bt000000 y4 = false := by decide
theorem sgT_000000_4 : SS.bdot bt000000 z4 = false := by decide
theorem sgB_000000_5 : SS.bdot bt000000 y5 = false := by decide
theorem sgT_000000_5 : SS.bdot bt000000 z5 = false := by decide
theorem sgB_000000_6 : SS.bdot bt000000 y6 = false := by decide
theorem sgT_000000_6 : SS.bdot bt000000 z6 = false := by decide
theorem sgB_000000_7 : SS.bdot bt000000 y7 = false := by decide
theorem sgT_000000_7 : SS.bdot bt000000 z7 = false := by decide
theorem sgB_000000_8 : SS.bdot bt000000 y8 = false := by decide
theorem sgT_000000_8 : SS.bdot bt000000 z8 = false := by decide
theorem sgB_000000_9 : SS.bdot bt000000 y9 = false := by decide
theorem sgT_000000_9 : SS.bdot bt000000 z9 = false := by decide
theorem sgB_000000_10 : SS.bdot bt000000 y10 = false := by decide
theorem sgT_000000_10 : SS.bdot bt000000 z10 = false := by decide
theorem sgB_000000_11 : SS.bdot bt000000 y11 = false := by decide
theorem sgT_000000_11 : SS.bdot bt000000 z11 = false := by decide
theorem sgB_000011_0 : SS.bdot bt000011 y0 = false := by decide
theorem sgT_000011_0 : SS.bdot bt000011 z0 = false := by decide
theorem sgB_000011_1 : SS.bdot bt000011 y1 = false := by decide
theorem sgT_000011_1 : SS.bdot bt000011 z1 = false := by decide
theorem sgB_000011_2 : SS.bdot bt000011 y2 = true := by decide
theorem sgT_000011_2 : SS.bdot bt000011 z2 = true := by decide
theorem sgB_000011_3 : SS.bdot bt000011 y3 = true := by decide
theorem sgT_000011_3 : SS.bdot bt000011 z3 = true := by decide
theorem sgB_000011_4 : SS.bdot bt000011 y4 = true := by decide
theorem sgT_000011_4 : SS.bdot bt000011 z4 = true := by decide
theorem sgB_000011_5 : SS.bdot bt000011 y5 = true := by decide
theorem sgT_000011_5 : SS.bdot bt000011 z5 = true := by decide
theorem sgB_000011_6 : SS.bdot bt000011 y6 = true := by decide
theorem sgT_000011_6 : SS.bdot bt000011 z6 = true := by decide
theorem sgB_000011_7 : SS.bdot bt000011 y7 = true := by decide
theorem sgT_000011_7 : SS.bdot bt000011 z7 = true := by decide
theorem sgB_000011_8 : SS.bdot bt000011 y8 = true := by decide
theorem sgT_000011_8 : SS.bdot bt000011 z8 = true := by decide
theorem sgB_000011_9 : SS.bdot bt000011 y9 = true := by decide
theorem sgT_000011_9 : SS.bdot bt000011 z9 = true := by decide
theorem sgB_000011_10 : SS.bdot bt000011 y10 = true := by decide
theorem sgT_000011_10 : SS.bdot bt000011 z10 = true := by decide
theorem sgB_000011_11 : SS.bdot bt000011 y11 = true := by decide
theorem sgT_000011_11 : SS.bdot bt000011 z11 = true := by decide
theorem sgB_000101_0 : SS.bdot bt000101 y0 = false := by decide
theorem sgT_000101_0 : SS.bdot bt000101 z0 = false := by decide
theorem sgB_000101_1 : SS.bdot bt000101 y1 = true := by decide
theorem sgT_000101_1 : SS.bdot bt000101 z1 = true := by decide
theorem sgB_000101_2 : SS.bdot bt000101 y2 = true := by decide
theorem sgT_000101_2 : SS.bdot bt000101 z2 = true := by decide
theorem sgB_000101_3 : SS.bdot bt000101 y3 = true := by decide
theorem sgT_000101_3 : SS.bdot bt000101 z3 = true := by decide
theorem sgB_000101_4 : SS.bdot bt000101 y4 = true := by decide
theorem sgT_000101_4 : SS.bdot bt000101 z4 = true := by decide
theorem sgB_000101_5 : SS.bdot bt000101 y5 = false := by decide
theorem sgT_000101_5 : SS.bdot bt000101 z5 = false := by decide
theorem sgB_000101_6 : SS.bdot bt000101 y6 = true := by decide
theorem sgT_000101_6 : SS.bdot bt000101 z6 = true := by decide
theorem sgB_000101_7 : SS.bdot bt000101 y7 = true := by decide
theorem sgT_000101_7 : SS.bdot bt000101 z7 = true := by decide
theorem sgB_000101_8 : SS.bdot bt000101 y8 = false := by decide
theorem sgT_000101_8 : SS.bdot bt000101 z8 = false := by decide
theorem sgB_000101_9 : SS.bdot bt000101 y9 = true := by decide
theorem sgT_000101_9 : SS.bdot bt000101 z9 = true := by decide
theorem sgB_000101_10 : SS.bdot bt000101 y10 = false := by decide
theorem sgT_000101_10 : SS.bdot bt000101 z10 = false := by decide
theorem sgB_000101_11 : SS.bdot bt000101 y11 = false := by decide
theorem sgT_000101_11 : SS.bdot bt000101 z11 = false := by decide
theorem sgB_000110_0 : SS.bdot bt000110 y0 = false := by decide
theorem sgT_000110_0 : SS.bdot bt000110 z0 = false := by decide
theorem sgB_000110_1 : SS.bdot bt000110 y1 = true := by decide
theorem sgT_000110_1 : SS.bdot bt000110 z1 = true := by decide
theorem sgB_000110_2 : SS.bdot bt000110 y2 = false := by decide
theorem sgT_000110_2 : SS.bdot bt000110 z2 = false := by decide
theorem sgB_000110_3 : SS.bdot bt000110 y3 = false := by decide
theorem sgT_000110_3 : SS.bdot bt000110 z3 = false := by decide
theorem sgB_000110_4 : SS.bdot bt000110 y4 = false := by decide
theorem sgT_000110_4 : SS.bdot bt000110 z4 = false := by decide
theorem sgB_000110_5 : SS.bdot bt000110 y5 = true := by decide
theorem sgT_000110_5 : SS.bdot bt000110 z5 = true := by decide
theorem sgB_000110_6 : SS.bdot bt000110 y6 = false := by decide
theorem sgT_000110_6 : SS.bdot bt000110 z6 = false := by decide
theorem sgB_000110_7 : SS.bdot bt000110 y7 = false := by decide
theorem sgT_000110_7 : SS.bdot bt000110 z7 = false := by decide
theorem sgB_000110_8 : SS.bdot bt000110 y8 = true := by decide
theorem sgT_000110_8 : SS.bdot bt000110 z8 = true := by decide
theorem sgB_000110_9 : SS.bdot bt000110 y9 = false := by decide
theorem sgT_000110_9 : SS.bdot bt000110 z9 = false := by decide
theorem sgB_000110_10 : SS.bdot bt000110 y10 = true := by decide
theorem sgT_000110_10 : SS.bdot bt000110 z10 = true := by decide
theorem sgB_000110_11 : SS.bdot bt000110 y11 = true := by decide
theorem sgT_000110_11 : SS.bdot bt000110 z11 = true := by decide
theorem sgB_001001_0 : SS.bdot bt001001 y0 = false := by decide
theorem sgT_001001_0 : SS.bdot bt001001 z0 = false := by decide
theorem sgB_001001_1 : SS.bdot bt001001 y1 = true := by decide
theorem sgT_001001_1 : SS.bdot bt001001 z1 = true := by decide
theorem sgB_001001_2 : SS.bdot bt001001 y2 = true := by decide
theorem sgT_001001_2 : SS.bdot bt001001 z2 = true := by decide
theorem sgB_001001_3 : SS.bdot bt001001 y3 = true := by decide
theorem sgT_001001_3 : SS.bdot bt001001 z3 = true := by decide
theorem sgB_001001_4 : SS.bdot bt001001 y4 = false := by decide
theorem sgT_001001_4 : SS.bdot bt001001 z4 = false := by decide
theorem sgB_001001_5 : SS.bdot bt001001 y5 = true := by decide
theorem sgT_001001_5 : SS.bdot bt001001 z5 = true := by decide
theorem sgB_001001_6 : SS.bdot bt001001 y6 = true := by decide
theorem sgT_001001_6 : SS.bdot bt001001 z6 = true := by decide
theorem sgB_001001_7 : SS.bdot bt001001 y7 = false := by decide
theorem sgT_001001_7 : SS.bdot bt001001 z7 = false := by decide
theorem sgB_001001_8 : SS.bdot bt001001 y8 = true := by decide
theorem sgT_001001_8 : SS.bdot bt001001 z8 = true := by decide
theorem sgB_001001_9 : SS.bdot bt001001 y9 = false := by decide
theorem sgT_001001_9 : SS.bdot bt001001 z9 = false := by decide
theorem sgB_001001_10 : SS.bdot bt001001 y10 = true := by decide
theorem sgT_001001_10 : SS.bdot bt001001 z10 = true := by decide
theorem sgB_001001_11 : SS.bdot bt001001 y11 = false := by decide
theorem sgT_001001_11 : SS.bdot bt001001 z11 = false := by decide
theorem sgB_001010_0 : SS.bdot bt001010 y0 = false := by decide
theorem sgT_001010_0 : SS.bdot bt001010 z0 = false := by decide
theorem sgB_001010_1 : SS.bdot bt001010 y1 = true := by decide
theorem sgT_001010_1 : SS.bdot bt001010 z1 = true := by decide
theorem sgB_001010_2 : SS.bdot bt001010 y2 = false := by decide
theorem sgT_001010_2 : SS.bdot bt001010 z2 = false := by decide
theorem sgB_001010_3 : SS.bdot bt001010 y3 = false := by decide
theorem sgT_001010_3 : SS.bdot bt001010 z3 = false := by decide
theorem sgB_001010_4 : SS.bdot bt001010 y4 = true := by decide
theorem sgT_001010_4 : SS.bdot bt001010 z4 = true := by decide
theorem sgB_001010_5 : SS.bdot bt001010 y5 = false := by decide
theorem sgT_001010_5 : SS.bdot bt001010 z5 = false := by decide
theorem sgB_001010_6 : SS.bdot bt001010 y6 = false := by decide
theorem sgT_001010_6 : SS.bdot bt001010 z6 = false := by decide
theorem sgB_001010_7 : SS.bdot bt001010 y7 = true := by decide
theorem sgT_001010_7 : SS.bdot bt001010 z7 = true := by decide
theorem sgB_001010_8 : SS.bdot bt001010 y8 = false := by decide
theorem sgT_001010_8 : SS.bdot bt001010 z8 = false := by decide
theorem sgB_001010_9 : SS.bdot bt001010 y9 = true := by decide
theorem sgT_001010_9 : SS.bdot bt001010 z9 = true := by decide
theorem sgB_001010_10 : SS.bdot bt001010 y10 = false := by decide
theorem sgT_001010_10 : SS.bdot bt001010 z10 = false := by decide
theorem sgB_001010_11 : SS.bdot bt001010 y11 = true := by decide
theorem sgT_001010_11 : SS.bdot bt001010 z11 = true := by decide
theorem sgB_001100_0 : SS.bdot bt001100 y0 = false := by decide
theorem sgT_001100_0 : SS.bdot bt001100 z0 = false := by decide
theorem sgB_001100_1 : SS.bdot bt001100 y1 = false := by decide
theorem sgT_001100_1 : SS.bdot bt001100 z1 = false := by decide
theorem sgB_001100_2 : SS.bdot bt001100 y2 = false := by decide
theorem sgT_001100_2 : SS.bdot bt001100 z2 = false := by decide
theorem sgB_001100_3 : SS.bdot bt001100 y3 = false := by decide
theorem sgT_001100_3 : SS.bdot bt001100 z3 = false := by decide
theorem sgB_001100_4 : SS.bdot bt001100 y4 = true := by decide
theorem sgT_001100_4 : SS.bdot bt001100 z4 = true := by decide
theorem sgB_001100_5 : SS.bdot bt001100 y5 = true := by decide
theorem sgT_001100_5 : SS.bdot bt001100 z5 = true := by decide
theorem sgB_001100_6 : SS.bdot bt001100 y6 = false := by decide
theorem sgT_001100_6 : SS.bdot bt001100 z6 = false := by decide
theorem sgB_001100_7 : SS.bdot bt001100 y7 = true := by decide
theorem sgT_001100_7 : SS.bdot bt001100 z7 = true := by decide
theorem sgB_001100_8 : SS.bdot bt001100 y8 = true := by decide
theorem sgT_001100_8 : SS.bdot bt001100 z8 = true := by decide
theorem sgB_001100_9 : SS.bdot bt001100 y9 = true := by decide
theorem sgT_001100_9 : SS.bdot bt001100 z9 = true := by decide
theorem sgB_001100_10 : SS.bdot bt001100 y10 = true := by decide
theorem sgT_001100_10 : SS.bdot bt001100 z10 = true := by decide
theorem sgB_001100_11 : SS.bdot bt001100 y11 = false := by decide
theorem sgT_001100_11 : SS.bdot bt001100 z11 = false := by decide
theorem sgB_010001_0 : SS.bdot bt010001 y0 = false := by decide
theorem sgT_010001_0 : SS.bdot bt010001 z0 = false := by decide
theorem sgB_010001_1 : SS.bdot bt010001 y1 = true := by decide
theorem sgT_010001_1 : SS.bdot bt010001 z1 = true := by decide
theorem sgB_010001_2 : SS.bdot bt010001 y2 = true := by decide
theorem sgT_010001_2 : SS.bdot bt010001 z2 = true := by decide
theorem sgB_010001_3 : SS.bdot bt010001 y3 = false := by decide
theorem sgT_010001_3 : SS.bdot bt010001 z3 = false := by decide
theorem sgB_010001_4 : SS.bdot bt010001 y4 = true := by decide
theorem sgT_010001_4 : SS.bdot bt010001 z4 = true := by decide
theorem sgB_010001_5 : SS.bdot bt010001 y5 = true := by decide
theorem sgT_010001_5 : SS.bdot bt010001 z5 = true := by decide
theorem sgB_010001_6 : SS.bdot bt010001 y6 = false := by decide
theorem sgT_010001_6 : SS.bdot bt010001 z6 = false := by decide
theorem sgB_010001_7 : SS.bdot bt010001 y7 = true := by decide
theorem sgT_010001_7 : SS.bdot bt010001 z7 = true := by decide
theorem sgB_010001_8 : SS.bdot bt010001 y8 = true := by decide
theorem sgT_010001_8 : SS.bdot bt010001 z8 = true := by decide
theorem sgB_010001_9 : SS.bdot bt010001 y9 = false := by decide
theorem sgT_010001_9 : SS.bdot bt010001 z9 = false := by decide
theorem sgB_010001_10 : SS.bdot bt010001 y10 = false := by decide
theorem sgT_010001_10 : SS.bdot bt010001 z10 = false := by decide
theorem sgB_010001_11 : SS.bdot bt010001 y11 = true := by decide
theorem sgT_010001_11 : SS.bdot bt010001 z11 = true := by decide
theorem sgB_010010_0 : SS.bdot bt010010 y0 = false := by decide
theorem sgT_010010_0 : SS.bdot bt010010 z0 = false := by decide
theorem sgB_010010_1 : SS.bdot bt010010 y1 = true := by decide
theorem sgT_010010_1 : SS.bdot bt010010 z1 = true := by decide
theorem sgB_010010_2 : SS.bdot bt010010 y2 = false := by decide
theorem sgT_010010_2 : SS.bdot bt010010 z2 = false := by decide
theorem sgB_010010_3 : SS.bdot bt010010 y3 = true := by decide
theorem sgT_010010_3 : SS.bdot bt010010 z3 = true := by decide
theorem sgB_010010_4 : SS.bdot bt010010 y4 = false := by decide
theorem sgT_010010_4 : SS.bdot bt010010 z4 = false := by decide
theorem sgB_010010_5 : SS.bdot bt010010 y5 = false := by decide
theorem sgT_010010_5 : SS.bdot bt010010 z5 = false := by decide
theorem sgB_010010_6 : SS.bdot bt010010 y6 = true := by decide
theorem sgT_010010_6 : SS.bdot bt010010 z6 = true := by decide
theorem sgB_010010_7 : SS.bdot bt010010 y7 = false := by decide
theorem sgT_010010_7 : SS.bdot bt010010 z7 = false := by decide
theorem sgB_010010_8 : SS.bdot bt010010 y8 = false := by decide
theorem sgT_010010_8 : SS.bdot bt010010 z8 = false := by decide
theorem sgB_010010_9 : SS.bdot bt010010 y9 = true := by decide
theorem sgT_010010_9 : SS.bdot bt010010 z9 = true := by decide
theorem sgB_010010_10 : SS.bdot bt010010 y10 = true := by decide
theorem sgT_010010_10 : SS.bdot bt010010 z10 = true := by decide
theorem sgB_010010_11 : SS.bdot bt010010 y11 = false := by decide
theorem sgT_010010_11 : SS.bdot bt010010 z11 = false := by decide
theorem sgB_010100_0 : SS.bdot bt010100 y0 = false := by decide
theorem sgT_010100_0 : SS.bdot bt010100 z0 = false := by decide
theorem sgB_010100_1 : SS.bdot bt010100 y1 = false := by decide
theorem sgT_010100_1 : SS.bdot bt010100 z1 = false := by decide
theorem sgB_010100_2 : SS.bdot bt010100 y2 = false := by decide
theorem sgT_010100_2 : SS.bdot bt010100 z2 = false := by decide
theorem sgB_010100_3 : SS.bdot bt010100 y3 = true := by decide
theorem sgT_010100_3 : SS.bdot bt010100 z3 = true := by decide
theorem sgB_010100_4 : SS.bdot bt010100 y4 = false := by decide
theorem sgT_010100_4 : SS.bdot bt010100 z4 = false := by decide
theorem sgB_010100_5 : SS.bdot bt010100 y5 = true := by decide
theorem sgT_010100_5 : SS.bdot bt010100 z5 = true := by decide
theorem sgB_010100_6 : SS.bdot bt010100 y6 = true := by decide
theorem sgT_010100_6 : SS.bdot bt010100 z6 = true := by decide
theorem sgB_010100_7 : SS.bdot bt010100 y7 = false := by decide
theorem sgT_010100_7 : SS.bdot bt010100 z7 = false := by decide
theorem sgB_010100_8 : SS.bdot bt010100 y8 = true := by decide
theorem sgT_010100_8 : SS.bdot bt010100 z8 = true := by decide
theorem sgB_010100_9 : SS.bdot bt010100 y9 = true := by decide
theorem sgT_010100_9 : SS.bdot bt010100 z9 = true := by decide
theorem sgB_010100_10 : SS.bdot bt010100 y10 = false := by decide
theorem sgT_010100_10 : SS.bdot bt010100 z10 = false := by decide
theorem sgB_010100_11 : SS.bdot bt010100 y11 = true := by decide
theorem sgT_010100_11 : SS.bdot bt010100 z11 = true := by decide
theorem sgB_011000_0 : SS.bdot bt011000 y0 = false := by decide
theorem sgT_011000_0 : SS.bdot bt011000 z0 = false := by decide
theorem sgB_011000_1 : SS.bdot bt011000 y1 = false := by decide
theorem sgT_011000_1 : SS.bdot bt011000 z1 = false := by decide
theorem sgB_011000_2 : SS.bdot bt011000 y2 = false := by decide
theorem sgT_011000_2 : SS.bdot bt011000 z2 = false := by decide
theorem sgB_011000_3 : SS.bdot bt011000 y3 = true := by decide
theorem sgT_011000_3 : SS.bdot bt011000 z3 = true := by decide
theorem sgB_011000_4 : SS.bdot bt011000 y4 = true := by decide
theorem sgT_011000_4 : SS.bdot bt011000 z4 = true := by decide
theorem sgB_011000_5 : SS.bdot bt011000 y5 = false := by decide
theorem sgT_011000_5 : SS.bdot bt011000 z5 = false := by decide
theorem sgB_011000_6 : SS.bdot bt011000 y6 = true := by decide
theorem sgT_011000_6 : SS.bdot bt011000 z6 = true := by decide
theorem sgB_011000_7 : SS.bdot bt011000 y7 = true := by decide
theorem sgT_011000_7 : SS.bdot bt011000 z7 = true := by decide
theorem sgB_011000_8 : SS.bdot bt011000 y8 = false := by decide
theorem sgT_011000_8 : SS.bdot bt011000 z8 = false := by decide
theorem sgB_011000_9 : SS.bdot bt011000 y9 = false := by decide
theorem sgT_011000_9 : SS.bdot bt011000 z9 = false := by decide
theorem sgB_011000_10 : SS.bdot bt011000 y10 = true := by decide
theorem sgT_011000_10 : SS.bdot bt011000 z10 = true := by decide
theorem sgB_011000_11 : SS.bdot bt011000 y11 = true := by decide
theorem sgT_011000_11 : SS.bdot bt011000 z11 = true := by decide
theorem sgB_100001_0 : SS.bdot bt100001 y0 = false := by decide
theorem sgT_100001_0 : SS.bdot bt100001 z0 = false := by decide
theorem sgB_100001_1 : SS.bdot bt100001 y1 = true := by decide
theorem sgT_100001_1 : SS.bdot bt100001 z1 = true := by decide
theorem sgB_100001_2 : SS.bdot bt100001 y2 = false := by decide
theorem sgT_100001_2 : SS.bdot bt100001 z2 = false := by decide
theorem sgB_100001_3 : SS.bdot bt100001 y3 = true := by decide
theorem sgT_100001_3 : SS.bdot bt100001 z3 = true := by decide
theorem sgB_100001_4 : SS.bdot bt100001 y4 = true := by decide
theorem sgT_100001_4 : SS.bdot bt100001 z4 = true := by decide
theorem sgB_100001_5 : SS.bdot bt100001 y5 = true := by decide
theorem sgT_100001_5 : SS.bdot bt100001 z5 = true := by decide
theorem sgB_100001_6 : SS.bdot bt100001 y6 = false := by decide
theorem sgT_100001_6 : SS.bdot bt100001 z6 = false := by decide
theorem sgB_100001_7 : SS.bdot bt100001 y7 = false := by decide
theorem sgT_100001_7 : SS.bdot bt100001 z7 = false := by decide
theorem sgB_100001_8 : SS.bdot bt100001 y8 = false := by decide
theorem sgT_100001_8 : SS.bdot bt100001 z8 = false := by decide
theorem sgB_100001_9 : SS.bdot bt100001 y9 = true := by decide
theorem sgT_100001_9 : SS.bdot bt100001 z9 = true := by decide
theorem sgB_100001_10 : SS.bdot bt100001 y10 = true := by decide
theorem sgT_100001_10 : SS.bdot bt100001 z10 = true := by decide
theorem sgB_100001_11 : SS.bdot bt100001 y11 = true := by decide
theorem sgT_100001_11 : SS.bdot bt100001 z11 = true := by decide
theorem sgB_100010_0 : SS.bdot bt100010 y0 = false := by decide
theorem sgT_100010_0 : SS.bdot bt100010 z0 = false := by decide
theorem sgB_100010_1 : SS.bdot bt100010 y1 = true := by decide
theorem sgT_100010_1 : SS.bdot bt100010 z1 = true := by decide
theorem sgB_100010_2 : SS.bdot bt100010 y2 = true := by decide
theorem sgT_100010_2 : SS.bdot bt100010 z2 = true := by decide
theorem sgB_100010_3 : SS.bdot bt100010 y3 = false := by decide
theorem sgT_100010_3 : SS.bdot bt100010 z3 = false := by decide
theorem sgB_100010_4 : SS.bdot bt100010 y4 = false := by decide
theorem sgT_100010_4 : SS.bdot bt100010 z4 = false := by decide
theorem sgB_100010_5 : SS.bdot bt100010 y5 = false := by decide
theorem sgT_100010_5 : SS.bdot bt100010 z5 = false := by decide
theorem sgB_100010_6 : SS.bdot bt100010 y6 = true := by decide
theorem sgT_100010_6 : SS.bdot bt100010 z6 = true := by decide
theorem sgB_100010_7 : SS.bdot bt100010 y7 = true := by decide
theorem sgT_100010_7 : SS.bdot bt100010 z7 = true := by decide
theorem sgB_100010_8 : SS.bdot bt100010 y8 = true := by decide
theorem sgT_100010_8 : SS.bdot bt100010 z8 = true := by decide
theorem sgB_100010_9 : SS.bdot bt100010 y9 = false := by decide
theorem sgT_100010_9 : SS.bdot bt100010 z9 = false := by decide
theorem sgB_100010_10 : SS.bdot bt100010 y10 = false := by decide
theorem sgT_100010_10 : SS.bdot bt100010 z10 = false := by decide
theorem sgB_100010_11 : SS.bdot bt100010 y11 = false := by decide
theorem sgT_100010_11 : SS.bdot bt100010 z11 = false := by decide
theorem sgB_100100_0 : SS.bdot bt100100 y0 = false := by decide
theorem sgT_100100_0 : SS.bdot bt100100 z0 = false := by decide
theorem sgB_100100_1 : SS.bdot bt100100 y1 = false := by decide
theorem sgT_100100_1 : SS.bdot bt100100 z1 = false := by decide
theorem sgB_100100_2 : SS.bdot bt100100 y2 = true := by decide
theorem sgT_100100_2 : SS.bdot bt100100 z2 = true := by decide
theorem sgB_100100_3 : SS.bdot bt100100 y3 = false := by decide
theorem sgT_100100_3 : SS.bdot bt100100 z3 = false := by decide
theorem sgB_100100_4 : SS.bdot bt100100 y4 = false := by decide
theorem sgT_100100_4 : SS.bdot bt100100 z4 = false := by decide
theorem sgB_100100_5 : SS.bdot bt100100 y5 = true := by decide
theorem sgT_100100_5 : SS.bdot bt100100 z5 = true := by decide
theorem sgB_100100_6 : SS.bdot bt100100 y6 = true := by decide
theorem sgT_100100_6 : SS.bdot bt100100 z6 = true := by decide
theorem sgB_100100_7 : SS.bdot bt100100 y7 = true := by decide
theorem sgT_100100_7 : SS.bdot bt100100 z7 = true := by decide
theorem sgB_100100_8 : SS.bdot bt100100 y8 = false := by decide
theorem sgT_100100_8 : SS.bdot bt100100 z8 = false := by decide
theorem sgB_100100_9 : SS.bdot bt100100 y9 = false := by decide
theorem sgT_100100_9 : SS.bdot bt100100 z9 = false := by decide
theorem sgB_100100_10 : SS.bdot bt100100 y10 = true := by decide
theorem sgT_100100_10 : SS.bdot bt100100 z10 = true := by decide
theorem sgB_100100_11 : SS.bdot bt100100 y11 = true := by decide
theorem sgT_100100_11 : SS.bdot bt100100 z11 = true := by decide
theorem sgB_101000_0 : SS.bdot bt101000 y0 = false := by decide
theorem sgT_101000_0 : SS.bdot bt101000 z0 = false := by decide
theorem sgB_101000_1 : SS.bdot bt101000 y1 = false := by decide
theorem sgT_101000_1 : SS.bdot bt101000 z1 = false := by decide
theorem sgB_101000_2 : SS.bdot bt101000 y2 = true := by decide
theorem sgT_101000_2 : SS.bdot bt101000 z2 = true := by decide
theorem sgB_101000_3 : SS.bdot bt101000 y3 = false := by decide
theorem sgT_101000_3 : SS.bdot bt101000 z3 = false := by decide
theorem sgB_101000_4 : SS.bdot bt101000 y4 = true := by decide
theorem sgT_101000_4 : SS.bdot bt101000 z4 = true := by decide
theorem sgB_101000_5 : SS.bdot bt101000 y5 = false := by decide
theorem sgT_101000_5 : SS.bdot bt101000 z5 = false := by decide
theorem sgB_101000_6 : SS.bdot bt101000 y6 = true := by decide
theorem sgT_101000_6 : SS.bdot bt101000 z6 = true := by decide
theorem sgB_101000_7 : SS.bdot bt101000 y7 = false := by decide
theorem sgT_101000_7 : SS.bdot bt101000 z7 = false := by decide
theorem sgB_101000_8 : SS.bdot bt101000 y8 = true := by decide
theorem sgT_101000_8 : SS.bdot bt101000 z8 = true := by decide
theorem sgB_101000_9 : SS.bdot bt101000 y9 = true := by decide
theorem sgT_101000_9 : SS.bdot bt101000 z9 = true := by decide
theorem sgB_101000_10 : SS.bdot bt101000 y10 = false := by decide
theorem sgT_101000_10 : SS.bdot bt101000 z10 = false := by decide
theorem sgB_101000_11 : SS.bdot bt101000 y11 = true := by decide
theorem sgT_101000_11 : SS.bdot bt101000 z11 = true := by decide
theorem sgB_110000_0 : SS.bdot bt110000 y0 = false := by decide
theorem sgT_110000_0 : SS.bdot bt110000 z0 = false := by decide
theorem sgB_110000_1 : SS.bdot bt110000 y1 = false := by decide
theorem sgT_110000_1 : SS.bdot bt110000 z1 = false := by decide
theorem sgB_110000_2 : SS.bdot bt110000 y2 = true := by decide
theorem sgT_110000_2 : SS.bdot bt110000 z2 = true := by decide
theorem sgB_110000_3 : SS.bdot bt110000 y3 = true := by decide
theorem sgT_110000_3 : SS.bdot bt110000 z3 = true := by decide
theorem sgB_110000_4 : SS.bdot bt110000 y4 = false := by decide
theorem sgT_110000_4 : SS.bdot bt110000 z4 = false := by decide
theorem sgB_110000_5 : SS.bdot bt110000 y5 = false := by decide
theorem sgT_110000_5 : SS.bdot bt110000 z5 = false := by decide
theorem sgB_110000_6 : SS.bdot bt110000 y6 = false := by decide
theorem sgT_110000_6 : SS.bdot bt110000 z6 = false := by decide
theorem sgB_110000_7 : SS.bdot bt110000 y7 = true := by decide
theorem sgT_110000_7 : SS.bdot bt110000 z7 = true := by decide
theorem sgB_110000_8 : SS.bdot bt110000 y8 = true := by decide
theorem sgT_110000_8 : SS.bdot bt110000 z8 = true := by decide
theorem sgB_110000_9 : SS.bdot bt110000 y9 = true := by decide
theorem sgT_110000_9 : SS.bdot bt110000 z9 = true := by decide
theorem sgB_110000_10 : SS.bdot bt110000 y10 = true := by decide
theorem sgT_110000_10 : SS.bdot bt110000 z10 = true := by decide
theorem sgB_110000_11 : SS.bdot bt110000 y11 = false := by decide
theorem sgT_110000_11 : SS.bdot bt110000 z11 = false := by decide

set_option maxHeartbeats 3200000 in
/-- **The diagonal projector traces.**  A trivial flip mask makes both fibers
fully incident, and complementation matches the two probability vectors, so the
trace is twice the bottom Walsh sum.  The forced magnitudes evaluate all sixteen:
`1` for the identity, `1/15` on the six `K_4` edges, `+-1/5` on the eight rows
joining a vertex to a last coordinate, and `-3/5` on `Z_5 Z_6` -- exactly the
chapter's weight-two table. -/
theorem diag_values (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (k0 : Complex.normSq (c y0) = 1/10)
    (k1 : Complex.normSq (c y1) = 1/10)
    (k2 : Complex.normSq (c y2) = 1/10)
    (k3 : Complex.normSq (c y3) = 1/10)
    (k4 : Complex.normSq (c y4) = 1/10)
    (k5 : Complex.normSq (c y5) = 1/10)
    (k6 : Complex.normSq (c y6) = 1/15)
    (k7 : Complex.normSq (c y7) = 1/15)
    (k8 : Complex.normSq (c y8) = 1/15)
    (k9 : Complex.normSq (c y9) = 1/15)
    (k10 : Complex.normSq (c y10) = 1/15)
    (k11 : Complex.normSq (c y11) = 1/15)
    (l0 : Complex.normSq (d z0) = 1/10)
    (l1 : Complex.normSq (d z1) = 1/10)
    (l2 : Complex.normSq (d z2) = 1/10)
    (l3 : Complex.normSq (d z3) = 1/10)
    (l4 : Complex.normSq (d z4) = 1/10)
    (l5 : Complex.normSq (d z5) = 1/10)
    (l6 : Complex.normSq (d z6) = 1/15)
    (l7 : Complex.normSq (d z7) = 1/15)
    (l8 : Complex.normSq (d z8) = 1/15)
    (l9 : Complex.normSq (d z9) = 1/15)
    (l10 : Complex.normSq (d z10) = 1/15)
    (l11 : Complex.normSq (d z11) = 1/15)
    : Complex.normSq (projTrace c d ⟨bt000000, bt000000⟩) = 4
      ∧ Complex.normSq (projTrace c d ⟨bt000000, bt000011⟩) = 36/25
      ∧ Complex.normSq (projTrace c d ⟨bt000000, bt000101⟩) = 4/25
      ∧ Complex.normSq (projTrace c d ⟨bt000000, bt000110⟩) = 4/25
      ∧ Complex.normSq (projTrace c d ⟨bt000000, bt001001⟩) = 4/25
      ∧ Complex.normSq (projTrace c d ⟨bt000000, bt001010⟩) = 4/25
      ∧ Complex.normSq (projTrace c d ⟨bt000000, bt001100⟩) = 4/225
      ∧ Complex.normSq (projTrace c d ⟨bt000000, bt010001⟩) = 4/25
      ∧ Complex.normSq (projTrace c d ⟨bt000000, bt010010⟩) = 4/25
      ∧ Complex.normSq (projTrace c d ⟨bt000000, bt010100⟩) = 4/225
      ∧ Complex.normSq (projTrace c d ⟨bt000000, bt011000⟩) = 4/225
      ∧ Complex.normSq (projTrace c d ⟨bt000000, bt100001⟩) = 4/25
      ∧ Complex.normSq (projTrace c d ⟨bt000000, bt100010⟩) = 4/25
      ∧ Complex.normSq (projTrace c d ⟨bt000000, bt100100⟩) = 4/225
      ∧ Complex.normSq (projTrace c d ⟨bt000000, bt101000⟩) = 4/225
      ∧ Complex.normSq (projTrace c d ⟨bt000000, bt110000⟩) = 4/225 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h : projTrace c d ⟨bt000000, bt000000⟩
        = Complex.I ^ (SS.PauliString.mk bt000000 bt000000).numY * (2 * ((1 : ℝ) : ℂ)) := by
      rw [split_mk000000 c d hc hd bt000000]
      simp only [sgB_000000_0, sgB_000000_1, sgB_000000_2, sgB_000000_3, sgB_000000_4, sgB_000000_5, sgB_000000_6, sgB_000000_7, sgB_000000_8, sgB_000000_9, sgB_000000_10, sgB_000000_11, sgT_000000_0, sgT_000000_1, sgT_000000_2, sgT_000000_3, sgT_000000_4, sgT_000000_5, sgT_000000_6, sgT_000000_7, sgT_000000_8, sgT_000000_9, sgT_000000_10, sgT_000000_11,
        SS.signC_false, SixQubit.star_mul_self]
      rw [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11,
        l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11]
      push_cast
      ring
    rw [h, normSq_I_pow_mul, normSq_two_mul, Complex.normSq_ofReal]
    norm_num
  · have h : projTrace c d ⟨bt000000, bt000011⟩
        = Complex.I ^ (SS.PauliString.mk bt000000 bt000011).numY * (2 * ((-(3/5) : ℝ) : ℂ)) := by
      rw [split_mk000000 c d hc hd bt000011]
      simp only [sgB_000011_0, sgB_000011_1, sgB_000011_2, sgB_000011_3, sgB_000011_4, sgB_000011_5, sgB_000011_6, sgB_000011_7, sgB_000011_8, sgB_000011_9, sgB_000011_10, sgB_000011_11, sgT_000011_0, sgT_000011_1, sgT_000011_2, sgT_000011_3, sgT_000011_4, sgT_000011_5, sgT_000011_6, sgT_000011_7, sgT_000011_8, sgT_000011_9, sgT_000011_10, sgT_000011_11,
        SS.signC_false, SS.signC_true, SixQubit.star_mul_self]
      rw [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11,
        l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11]
      push_cast
      ring
    rw [h, normSq_I_pow_mul, normSq_two_mul, Complex.normSq_ofReal]
    norm_num
  · have h : projTrace c d ⟨bt000000, bt000101⟩
        = Complex.I ^ (SS.PauliString.mk bt000000 bt000101).numY * (2 * ((-(1/5) : ℝ) : ℂ)) := by
      rw [split_mk000000 c d hc hd bt000101]
      simp only [sgB_000101_0, sgB_000101_1, sgB_000101_2, sgB_000101_3, sgB_000101_4, sgB_000101_5, sgB_000101_6, sgB_000101_7, sgB_000101_8, sgB_000101_9, sgB_000101_10, sgB_000101_11, sgT_000101_0, sgT_000101_1, sgT_000101_2, sgT_000101_3, sgT_000101_4, sgT_000101_5, sgT_000101_6, sgT_000101_7, sgT_000101_8, sgT_000101_9, sgT_000101_10, sgT_000101_11,
        SS.signC_false, SS.signC_true, SixQubit.star_mul_self]
      rw [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11,
        l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11]
      push_cast
      ring
    rw [h, normSq_I_pow_mul, normSq_two_mul, Complex.normSq_ofReal]
    norm_num
  · have h : projTrace c d ⟨bt000000, bt000110⟩
        = Complex.I ^ (SS.PauliString.mk bt000000 bt000110).numY * (2 * ((1/5 : ℝ) : ℂ)) := by
      rw [split_mk000000 c d hc hd bt000110]
      simp only [sgB_000110_0, sgB_000110_1, sgB_000110_2, sgB_000110_3, sgB_000110_4, sgB_000110_5, sgB_000110_6, sgB_000110_7, sgB_000110_8, sgB_000110_9, sgB_000110_10, sgB_000110_11, sgT_000110_0, sgT_000110_1, sgT_000110_2, sgT_000110_3, sgT_000110_4, sgT_000110_5, sgT_000110_6, sgT_000110_7, sgT_000110_8, sgT_000110_9, sgT_000110_10, sgT_000110_11,
        SS.signC_false, SS.signC_true, SixQubit.star_mul_self]
      rw [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11,
        l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11]
      push_cast
      ring
    rw [h, normSq_I_pow_mul, normSq_two_mul, Complex.normSq_ofReal]
    norm_num
  · have h : projTrace c d ⟨bt000000, bt001001⟩
        = Complex.I ^ (SS.PauliString.mk bt000000 bt001001).numY * (2 * ((-(1/5) : ℝ) : ℂ)) := by
      rw [split_mk000000 c d hc hd bt001001]
      simp only [sgB_001001_0, sgB_001001_1, sgB_001001_2, sgB_001001_3, sgB_001001_4, sgB_001001_5, sgB_001001_6, sgB_001001_7, sgB_001001_8, sgB_001001_9, sgB_001001_10, sgB_001001_11, sgT_001001_0, sgT_001001_1, sgT_001001_2, sgT_001001_3, sgT_001001_4, sgT_001001_5, sgT_001001_6, sgT_001001_7, sgT_001001_8, sgT_001001_9, sgT_001001_10, sgT_001001_11,
        SS.signC_false, SS.signC_true, SixQubit.star_mul_self]
      rw [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11,
        l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11]
      push_cast
      ring
    rw [h, normSq_I_pow_mul, normSq_two_mul, Complex.normSq_ofReal]
    norm_num
  · have h : projTrace c d ⟨bt000000, bt001010⟩
        = Complex.I ^ (SS.PauliString.mk bt000000 bt001010).numY * (2 * ((1/5 : ℝ) : ℂ)) := by
      rw [split_mk000000 c d hc hd bt001010]
      simp only [sgB_001010_0, sgB_001010_1, sgB_001010_2, sgB_001010_3, sgB_001010_4, sgB_001010_5, sgB_001010_6, sgB_001010_7, sgB_001010_8, sgB_001010_9, sgB_001010_10, sgB_001010_11, sgT_001010_0, sgT_001010_1, sgT_001010_2, sgT_001010_3, sgT_001010_4, sgT_001010_5, sgT_001010_6, sgT_001010_7, sgT_001010_8, sgT_001010_9, sgT_001010_10, sgT_001010_11,
        SS.signC_false, SS.signC_true, SixQubit.star_mul_self]
      rw [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11,
        l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11]
      push_cast
      ring
    rw [h, normSq_I_pow_mul, normSq_two_mul, Complex.normSq_ofReal]
    norm_num
  · have h : projTrace c d ⟨bt000000, bt001100⟩
        = Complex.I ^ (SS.PauliString.mk bt000000 bt001100).numY * (2 * ((1/15 : ℝ) : ℂ)) := by
      rw [split_mk000000 c d hc hd bt001100]
      simp only [sgB_001100_0, sgB_001100_1, sgB_001100_2, sgB_001100_3, sgB_001100_4, sgB_001100_5, sgB_001100_6, sgB_001100_7, sgB_001100_8, sgB_001100_9, sgB_001100_10, sgB_001100_11, sgT_001100_0, sgT_001100_1, sgT_001100_2, sgT_001100_3, sgT_001100_4, sgT_001100_5, sgT_001100_6, sgT_001100_7, sgT_001100_8, sgT_001100_9, sgT_001100_10, sgT_001100_11,
        SS.signC_false, SS.signC_true, SixQubit.star_mul_self]
      rw [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11,
        l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11]
      push_cast
      ring
    rw [h, normSq_I_pow_mul, normSq_two_mul, Complex.normSq_ofReal]
    norm_num
  · have h : projTrace c d ⟨bt000000, bt010001⟩
        = Complex.I ^ (SS.PauliString.mk bt000000 bt010001).numY * (2 * ((-(1/5) : ℝ) : ℂ)) := by
      rw [split_mk000000 c d hc hd bt010001]
      simp only [sgB_010001_0, sgB_010001_1, sgB_010001_2, sgB_010001_3, sgB_010001_4, sgB_010001_5, sgB_010001_6, sgB_010001_7, sgB_010001_8, sgB_010001_9, sgB_010001_10, sgB_010001_11, sgT_010001_0, sgT_010001_1, sgT_010001_2, sgT_010001_3, sgT_010001_4, sgT_010001_5, sgT_010001_6, sgT_010001_7, sgT_010001_8, sgT_010001_9, sgT_010001_10, sgT_010001_11,
        SS.signC_false, SS.signC_true, SixQubit.star_mul_self]
      rw [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11,
        l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11]
      push_cast
      ring
    rw [h, normSq_I_pow_mul, normSq_two_mul, Complex.normSq_ofReal]
    norm_num
  · have h : projTrace c d ⟨bt000000, bt010010⟩
        = Complex.I ^ (SS.PauliString.mk bt000000 bt010010).numY * (2 * ((1/5 : ℝ) : ℂ)) := by
      rw [split_mk000000 c d hc hd bt010010]
      simp only [sgB_010010_0, sgB_010010_1, sgB_010010_2, sgB_010010_3, sgB_010010_4, sgB_010010_5, sgB_010010_6, sgB_010010_7, sgB_010010_8, sgB_010010_9, sgB_010010_10, sgB_010010_11, sgT_010010_0, sgT_010010_1, sgT_010010_2, sgT_010010_3, sgT_010010_4, sgT_010010_5, sgT_010010_6, sgT_010010_7, sgT_010010_8, sgT_010010_9, sgT_010010_10, sgT_010010_11,
        SS.signC_false, SS.signC_true, SixQubit.star_mul_self]
      rw [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11,
        l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11]
      push_cast
      ring
    rw [h, normSq_I_pow_mul, normSq_two_mul, Complex.normSq_ofReal]
    norm_num
  · have h : projTrace c d ⟨bt000000, bt010100⟩
        = Complex.I ^ (SS.PauliString.mk bt000000 bt010100).numY * (2 * ((1/15 : ℝ) : ℂ)) := by
      rw [split_mk000000 c d hc hd bt010100]
      simp only [sgB_010100_0, sgB_010100_1, sgB_010100_2, sgB_010100_3, sgB_010100_4, sgB_010100_5, sgB_010100_6, sgB_010100_7, sgB_010100_8, sgB_010100_9, sgB_010100_10, sgB_010100_11, sgT_010100_0, sgT_010100_1, sgT_010100_2, sgT_010100_3, sgT_010100_4, sgT_010100_5, sgT_010100_6, sgT_010100_7, sgT_010100_8, sgT_010100_9, sgT_010100_10, sgT_010100_11,
        SS.signC_false, SS.signC_true, SixQubit.star_mul_self]
      rw [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11,
        l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11]
      push_cast
      ring
    rw [h, normSq_I_pow_mul, normSq_two_mul, Complex.normSq_ofReal]
    norm_num
  · have h : projTrace c d ⟨bt000000, bt011000⟩
        = Complex.I ^ (SS.PauliString.mk bt000000 bt011000).numY * (2 * ((1/15 : ℝ) : ℂ)) := by
      rw [split_mk000000 c d hc hd bt011000]
      simp only [sgB_011000_0, sgB_011000_1, sgB_011000_2, sgB_011000_3, sgB_011000_4, sgB_011000_5, sgB_011000_6, sgB_011000_7, sgB_011000_8, sgB_011000_9, sgB_011000_10, sgB_011000_11, sgT_011000_0, sgT_011000_1, sgT_011000_2, sgT_011000_3, sgT_011000_4, sgT_011000_5, sgT_011000_6, sgT_011000_7, sgT_011000_8, sgT_011000_9, sgT_011000_10, sgT_011000_11,
        SS.signC_false, SS.signC_true, SixQubit.star_mul_self]
      rw [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11,
        l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11]
      push_cast
      ring
    rw [h, normSq_I_pow_mul, normSq_two_mul, Complex.normSq_ofReal]
    norm_num
  · have h : projTrace c d ⟨bt000000, bt100001⟩
        = Complex.I ^ (SS.PauliString.mk bt000000 bt100001).numY * (2 * ((-(1/5) : ℝ) : ℂ)) := by
      rw [split_mk000000 c d hc hd bt100001]
      simp only [sgB_100001_0, sgB_100001_1, sgB_100001_2, sgB_100001_3, sgB_100001_4, sgB_100001_5, sgB_100001_6, sgB_100001_7, sgB_100001_8, sgB_100001_9, sgB_100001_10, sgB_100001_11, sgT_100001_0, sgT_100001_1, sgT_100001_2, sgT_100001_3, sgT_100001_4, sgT_100001_5, sgT_100001_6, sgT_100001_7, sgT_100001_8, sgT_100001_9, sgT_100001_10, sgT_100001_11,
        SS.signC_false, SS.signC_true, SixQubit.star_mul_self]
      rw [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11,
        l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11]
      push_cast
      ring
    rw [h, normSq_I_pow_mul, normSq_two_mul, Complex.normSq_ofReal]
    norm_num
  · have h : projTrace c d ⟨bt000000, bt100010⟩
        = Complex.I ^ (SS.PauliString.mk bt000000 bt100010).numY * (2 * ((1/5 : ℝ) : ℂ)) := by
      rw [split_mk000000 c d hc hd bt100010]
      simp only [sgB_100010_0, sgB_100010_1, sgB_100010_2, sgB_100010_3, sgB_100010_4, sgB_100010_5, sgB_100010_6, sgB_100010_7, sgB_100010_8, sgB_100010_9, sgB_100010_10, sgB_100010_11, sgT_100010_0, sgT_100010_1, sgT_100010_2, sgT_100010_3, sgT_100010_4, sgT_100010_5, sgT_100010_6, sgT_100010_7, sgT_100010_8, sgT_100010_9, sgT_100010_10, sgT_100010_11,
        SS.signC_false, SS.signC_true, SixQubit.star_mul_self]
      rw [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11,
        l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11]
      push_cast
      ring
    rw [h, normSq_I_pow_mul, normSq_two_mul, Complex.normSq_ofReal]
    norm_num
  · have h : projTrace c d ⟨bt000000, bt100100⟩
        = Complex.I ^ (SS.PauliString.mk bt000000 bt100100).numY * (2 * ((1/15 : ℝ) : ℂ)) := by
      rw [split_mk000000 c d hc hd bt100100]
      simp only [sgB_100100_0, sgB_100100_1, sgB_100100_2, sgB_100100_3, sgB_100100_4, sgB_100100_5, sgB_100100_6, sgB_100100_7, sgB_100100_8, sgB_100100_9, sgB_100100_10, sgB_100100_11, sgT_100100_0, sgT_100100_1, sgT_100100_2, sgT_100100_3, sgT_100100_4, sgT_100100_5, sgT_100100_6, sgT_100100_7, sgT_100100_8, sgT_100100_9, sgT_100100_10, sgT_100100_11,
        SS.signC_false, SS.signC_true, SixQubit.star_mul_self]
      rw [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11,
        l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11]
      push_cast
      ring
    rw [h, normSq_I_pow_mul, normSq_two_mul, Complex.normSq_ofReal]
    norm_num
  · have h : projTrace c d ⟨bt000000, bt101000⟩
        = Complex.I ^ (SS.PauliString.mk bt000000 bt101000).numY * (2 * ((1/15 : ℝ) : ℂ)) := by
      rw [split_mk000000 c d hc hd bt101000]
      simp only [sgB_101000_0, sgB_101000_1, sgB_101000_2, sgB_101000_3, sgB_101000_4, sgB_101000_5, sgB_101000_6, sgB_101000_7, sgB_101000_8, sgB_101000_9, sgB_101000_10, sgB_101000_11, sgT_101000_0, sgT_101000_1, sgT_101000_2, sgT_101000_3, sgT_101000_4, sgT_101000_5, sgT_101000_6, sgT_101000_7, sgT_101000_8, sgT_101000_9, sgT_101000_10, sgT_101000_11,
        SS.signC_false, SS.signC_true, SixQubit.star_mul_self]
      rw [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11,
        l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11]
      push_cast
      ring
    rw [h, normSq_I_pow_mul, normSq_two_mul, Complex.normSq_ofReal]
    norm_num
  · have h : projTrace c d ⟨bt000000, bt110000⟩
        = Complex.I ^ (SS.PauliString.mk bt000000 bt110000).numY * (2 * ((1/15 : ℝ) : ℂ)) := by
      rw [split_mk000000 c d hc hd bt110000]
      simp only [sgB_110000_0, sgB_110000_1, sgB_110000_2, sgB_110000_3, sgB_110000_4, sgB_110000_5, sgB_110000_6, sgB_110000_7, sgB_110000_8, sgB_110000_9, sgB_110000_10, sgB_110000_11, sgT_110000_0, sgT_110000_1, sgT_110000_2, sgT_110000_3, sgT_110000_4, sgT_110000_5, sgT_110000_6, sgT_110000_7, sgT_110000_8, sgT_110000_9, sgT_110000_10, sgT_110000_11,
        SS.signC_false, SS.signC_true, SixQubit.star_mul_self]
      rw [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11,
        l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11]
      push_cast
      ring
    rw [h, normSq_I_pow_mul, normSq_two_mul, Complex.normSq_ofReal]
    norm_num

/-! ## 10.  The seven non-diagonal weight-two masks -/

theorem sgB_010000_2 : SS.bdot bt010000 y2 = true := by decide
theorem sgB_010000_3 : SS.bdot bt010000 y3 = false := by decide
theorem sgT_010000_2 : SS.bdot bt010000 z2 = false := by decide
theorem sgT_010000_3 : SS.bdot bt010000 z3 = true := by decide
theorem sgB_010000_7 : SS.bdot bt010000 y7 = false := by decide
theorem sgB_010000_9 : SS.bdot bt010000 y9 = true := by decide
theorem sgT_010000_7 : SS.bdot bt010000 z7 = true := by decide
theorem sgT_010000_9 : SS.bdot bt010000 z9 = false := by decide
theorem sgB_010000_8 : SS.bdot bt010000 y8 = false := by decide
theorem sgB_010000_10 : SS.bdot bt010000 y10 = true := by decide
theorem sgT_010000_8 : SS.bdot bt010000 z8 = true := by decide
theorem sgT_010000_10 : SS.bdot bt010000 z10 = false := by decide
theorem sgB_100000_2 : SS.bdot bt100000 y2 = false := by decide
theorem sgB_100000_3 : SS.bdot bt100000 y3 = true := by decide
theorem sgT_100000_2 : SS.bdot bt100000 z2 = true := by decide
theorem sgT_100000_3 : SS.bdot bt100000 z3 = false := by decide
theorem sgB_100000_7 : SS.bdot bt100000 y7 = true := by decide
theorem sgB_100000_9 : SS.bdot bt100000 y9 = false := by decide
theorem sgT_100000_7 : SS.bdot bt100000 z7 = false := by decide
theorem sgT_100000_9 : SS.bdot bt100000 z9 = true := by decide
theorem sgB_100000_8 : SS.bdot bt100000 y8 = true := by decide
theorem sgB_100000_10 : SS.bdot bt100000 y10 = false := by decide
theorem sgT_100000_8 : SS.bdot bt100000 z8 = false := by decide
theorem sgT_100000_10 : SS.bdot bt100000 z10 = true := by decide
theorem sgB_001000_2 : SS.bdot bt001000 y2 = true := by decide
theorem sgB_001000_4 : SS.bdot bt001000 y4 = false := by decide
theorem sgT_001000_2 : SS.bdot bt001000 z2 = false := by decide
theorem sgT_001000_4 : SS.bdot bt001000 z4 = true := by decide
theorem sgB_001000_6 : SS.bdot bt001000 y6 = false := by decide
theorem sgB_001000_9 : SS.bdot bt001000 y9 = true := by decide
theorem sgT_001000_6 : SS.bdot bt001000 z6 = true := by decide
theorem sgT_001000_9 : SS.bdot bt001000 z9 = false := by decide
theorem sgB_001000_8 : SS.bdot bt001000 y8 = false := by decide
theorem sgB_001000_11 : SS.bdot bt001000 y11 = true := by decide
theorem sgT_001000_8 : SS.bdot bt001000 z8 = true := by decide
theorem sgT_001000_11 : SS.bdot bt001000 z11 = false := by decide
theorem sgB_100000_4 : SS.bdot bt100000 y4 = true := by decide
theorem sgT_100000_4 : SS.bdot bt100000 z4 = false := by decide
theorem sgB_100000_6 : SS.bdot bt100000 y6 = true := by decide
theorem sgT_100000_6 : SS.bdot bt100000 z6 = false := by decide
theorem sgB_100000_11 : SS.bdot bt100000 y11 = false := by decide
theorem sgT_100000_11 : SS.bdot bt100000 z11 = true := by decide
theorem sgB_000100_2 : SS.bdot bt000100 y2 = true := by decide
theorem sgB_000100_5 : SS.bdot bt000100 y5 = false := by decide
theorem sgT_000100_2 : SS.bdot bt000100 z2 = false := by decide
theorem sgT_000100_5 : SS.bdot bt000100 z5 = true := by decide
theorem sgB_000100_6 : SS.bdot bt000100 y6 = false := by decide
theorem sgB_000100_10 : SS.bdot bt000100 y10 = true := by decide
theorem sgT_000100_6 : SS.bdot bt000100 z6 = true := by decide
theorem sgT_000100_10 : SS.bdot bt000100 z10 = false := by decide
theorem sgB_000100_7 : SS.bdot bt000100 y7 = false := by decide
theorem sgB_000100_11 : SS.bdot bt000100 y11 = true := by decide
theorem sgT_000100_7 : SS.bdot bt000100 z7 = true := by decide
theorem sgT_000100_11 : SS.bdot bt000100 z11 = false := by decide
theorem sgB_100000_5 : SS.bdot bt100000 y5 = true := by decide
theorem sgT_100000_5 : SS.bdot bt100000 z5 = false := by decide
theorem sgB_001000_3 : SS.bdot bt001000 y3 = true := by decide
theorem sgT_001000_3 : SS.bdot bt001000 z3 = false := by decide
theorem sgB_001000_7 : SS.bdot bt001000 y7 = true := by decide
theorem sgT_001000_7 : SS.bdot bt001000 z7 = false := by decide
theorem sgB_001000_10 : SS.bdot bt001000 y10 = false := by decide
theorem sgT_001000_10 : SS.bdot bt001000 z10 = true := by decide
theorem sgB_010000_4 : SS.bdot bt010000 y4 = true := by decide
theorem sgT_010000_4 : SS.bdot bt010000 z4 = false := by decide
theorem sgB_010000_6 : SS.bdot bt010000 y6 = true := by decide
theorem sgT_010000_6 : SS.bdot bt010000 z6 = false := by decide
theorem sgB_010000_11 : SS.bdot bt010000 y11 = false := by decide
theorem sgT_010000_11 : SS.bdot bt010000 z11 = true := by decide
theorem sgB_000100_3 : SS.bdot bt000100 y3 = true := by decide
theorem sgT_000100_3 : SS.bdot bt000100 z3 = false := by decide
theorem sgB_000100_8 : SS.bdot bt000100 y8 = true := by decide
theorem sgT_000100_8 : SS.bdot bt000100 z8 = false := by decide
theorem sgB_000100_9 : SS.bdot bt000100 y9 = false := by decide
theorem sgT_000100_9 : SS.bdot bt000100 z9 = true := by decide
theorem sgB_010000_5 : SS.bdot bt010000 y5 = true := by decide
theorem sgT_010000_5 : SS.bdot bt010000 z5 = false := by decide
theorem sgB_000100_4 : SS.bdot bt000100 y4 = true := by decide
theorem sgT_000100_4 : SS.bdot bt000100 z4 = false := by decide
theorem sgB_001000_5 : SS.bdot bt001000 y5 = true := by decide
theorem sgT_001000_5 : SS.bdot bt001000 z5 = false := by decide
theorem sgB_000001_0 : SS.bdot bt000001 y0 = false := by decide
theorem sgB_000001_1 : SS.bdot bt000001 y1 = true := by decide
theorem sgT_000001_0 : SS.bdot bt000001 z0 = true := by decide
theorem sgT_000001_1 : SS.bdot bt000001 z1 = false := by decide
theorem sgB_000010_0 : SS.bdot bt000010 y0 = false := by decide
theorem sgB_000010_1 : SS.bdot bt000010 y1 = true := by decide
theorem sgT_000010_0 : SS.bdot bt000010 z0 = true := by decide
theorem sgT_000010_1 : SS.bdot bt000010 z1 = false := by decide

set_option maxHeartbeats 1600000 in
/-- The four dressings of the flip mask `110000`.  Their projector traces are
`+-2 (G + conj G)` and `+-2 (G - conj G)`, so this mask contributes
`32 * normSq G` to the weight-two sum. -/
theorem vals_mk110000 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (tau : ℂ) (htf : TopForm c d tau) :
    Complex.normSq (projTrace c d ⟨bt110000, bt000000⟩)
        = 4 * Complex.normSq ((star (c y3) * c y2 + star (c y7) * c y9 + star (c y8) * c y10) + star (star (c y3) * c y2 + star (c y7) * c y9 + star (c y8) * c y10))
      ∧ Complex.normSq (projTrace c d ⟨bt110000, bt010000⟩)
        = 4 * Complex.normSq ((star (c y3) * c y2 + star (c y7) * c y9 + star (c y8) * c y10) - star (star (c y3) * c y2 + star (c y7) * c y9 + star (c y8) * c y10))
      ∧ Complex.normSq (projTrace c d ⟨bt110000, bt100000⟩)
        = 4 * Complex.normSq ((star (c y3) * c y2 + star (c y7) * c y9 + star (c y8) * c y10) - star (star (c y3) * c y2 + star (c y7) * c y9 + star (c y8) * c y10))
      ∧ Complex.normSq (projTrace c d ⟨bt110000, bt110000⟩)
        = 4 * Complex.normSq ((star (c y3) * c y2 + star (c y7) * c y9 + star (c y8) * c y10) + star (star (c y3) * c y2 + star (c y7) * c y9 + star (c y8) * c y10)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h : projTrace c d ⟨bt110000, bt000000⟩
        = Complex.I ^ (SS.PauliString.mk bt110000 bt000000).numY * (2 * ((star (c y3) * c y2 + star (c y7) * c y9 + star (c y8) * c y10) + star (star (c y3) * c y2 + star (c y7) * c y9 + star (c y8) * c y10))) := by
      rw [split_mk110000 c d hc hd bt000000]
      simp only [sgB_000000_2, sgB_000000_3, sgB_000000_7, sgB_000000_9, sgB_000000_8, sgB_000000_10, sgT_000000_2, sgT_000000_3, sgT_000000_7, sgT_000000_9, sgT_000000_8, sgT_000000_10,
        SS.signC_false]
      rw [htf.t2, htf.t3, htf.t7, htf.t9, htf.t8, htf.t10]
      simp only [star_neg, star_mul', star_star, star_add]
      linear_combination (Complex.I ^ (SS.PauliString.mk bt110000 bt000000).numY * ((star (c y3) * c y2 + star (c y7) * c y9 + star (c y8) * c y10) + (star (c y2) * c y3 + star (c y9) * c y7 + star (c y10) * c y8))) * htf.unit
    rw [h, normSq_I_pow_mul, normSq_two_mul]
  · have h : projTrace c d ⟨bt110000, bt010000⟩
        = Complex.I ^ (SS.PauliString.mk bt110000 bt010000).numY * (2 * (-((star (c y3) * c y2 + star (c y7) * c y9 + star (c y8) * c y10) - star (star (c y3) * c y2 + star (c y7) * c y9 + star (c y8) * c y10)))) := by
      rw [split_mk110000 c d hc hd bt010000]
      simp only [sgB_010000_2, sgB_010000_3, sgB_010000_7, sgB_010000_9, sgB_010000_8, sgB_010000_10, sgT_010000_2, sgT_010000_3, sgT_010000_7, sgT_010000_9, sgT_010000_8, sgT_010000_10,
        SS.signC_false, SS.signC_true]
      rw [htf.t2, htf.t3, htf.t7, htf.t9, htf.t8, htf.t10]
      simp only [star_neg, star_mul', star_star, star_add]
      linear_combination (Complex.I ^ (SS.PauliString.mk bt110000 bt010000).numY * (-((star (c y3) * c y2 + star (c y7) * c y9 + star (c y8) * c y10) - (star (c y2) * c y3 + star (c y9) * c y7 + star (c y10) * c y8)))) * htf.unit
    rw [h, normSq_I_pow_mul, normSq_two_mul, Complex.normSq_neg]
  · have h : projTrace c d ⟨bt110000, bt100000⟩
        = Complex.I ^ (SS.PauliString.mk bt110000 bt100000).numY * (2 * ((star (c y3) * c y2 + star (c y7) * c y9 + star (c y8) * c y10) - star (star (c y3) * c y2 + star (c y7) * c y9 + star (c y8) * c y10))) := by
      rw [split_mk110000 c d hc hd bt100000]
      simp only [sgB_100000_2, sgB_100000_3, sgB_100000_7, sgB_100000_9, sgB_100000_8, sgB_100000_10, sgT_100000_2, sgT_100000_3, sgT_100000_7, sgT_100000_9, sgT_100000_8, sgT_100000_10,
        SS.signC_false, SS.signC_true]
      rw [htf.t2, htf.t3, htf.t7, htf.t9, htf.t8, htf.t10]
      simp only [star_neg, star_mul', star_star, star_add]
      linear_combination (Complex.I ^ (SS.PauliString.mk bt110000 bt100000).numY * ((star (c y3) * c y2 + star (c y7) * c y9 + star (c y8) * c y10) - (star (c y2) * c y3 + star (c y9) * c y7 + star (c y10) * c y8))) * htf.unit
    rw [h, normSq_I_pow_mul, normSq_two_mul]
  · have h : projTrace c d ⟨bt110000, bt110000⟩
        = Complex.I ^ (SS.PauliString.mk bt110000 bt110000).numY * (2 * (-((star (c y3) * c y2 + star (c y7) * c y9 + star (c y8) * c y10) + star (star (c y3) * c y2 + star (c y7) * c y9 + star (c y8) * c y10)))) := by
      rw [split_mk110000 c d hc hd bt110000]
      simp only [sgB_110000_2, sgB_110000_3, sgB_110000_7, sgB_110000_9, sgB_110000_8, sgB_110000_10, sgT_110000_2, sgT_110000_3, sgT_110000_7, sgT_110000_9, sgT_110000_8, sgT_110000_10,
        SS.signC_true]
      rw [htf.t2, htf.t3, htf.t7, htf.t9, htf.t8, htf.t10]
      simp only [star_neg, star_mul', star_star, star_add]
      linear_combination (Complex.I ^ (SS.PauliString.mk bt110000 bt110000).numY * (-((star (c y3) * c y2 + star (c y7) * c y9 + star (c y8) * c y10) + (star (c y2) * c y3 + star (c y9) * c y7 + star (c y10) * c y8)))) * htf.unit
    rw [h, normSq_I_pow_mul, normSq_two_mul, Complex.normSq_neg]

set_option maxHeartbeats 1600000 in
/-- The four dressings of the flip mask `101000`.  Their projector traces are
`+-2 (G + conj G)` and `+-2 (G - conj G)`, so this mask contributes
`32 * normSq G` to the weight-two sum. -/
theorem vals_mk101000 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (tau : ℂ) (htf : TopForm c d tau) :
    Complex.normSq (projTrace c d ⟨bt101000, bt000000⟩)
        = 4 * Complex.normSq ((star (c y4) * c y2 + star (c y6) * c y9 + star (c y8) * c y11) + star (star (c y4) * c y2 + star (c y6) * c y9 + star (c y8) * c y11))
      ∧ Complex.normSq (projTrace c d ⟨bt101000, bt001000⟩)
        = 4 * Complex.normSq ((star (c y4) * c y2 + star (c y6) * c y9 + star (c y8) * c y11) - star (star (c y4) * c y2 + star (c y6) * c y9 + star (c y8) * c y11))
      ∧ Complex.normSq (projTrace c d ⟨bt101000, bt100000⟩)
        = 4 * Complex.normSq ((star (c y4) * c y2 + star (c y6) * c y9 + star (c y8) * c y11) - star (star (c y4) * c y2 + star (c y6) * c y9 + star (c y8) * c y11))
      ∧ Complex.normSq (projTrace c d ⟨bt101000, bt101000⟩)
        = 4 * Complex.normSq ((star (c y4) * c y2 + star (c y6) * c y9 + star (c y8) * c y11) + star (star (c y4) * c y2 + star (c y6) * c y9 + star (c y8) * c y11)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h : projTrace c d ⟨bt101000, bt000000⟩
        = Complex.I ^ (SS.PauliString.mk bt101000 bt000000).numY * (2 * ((star (c y4) * c y2 + star (c y6) * c y9 + star (c y8) * c y11) + star (star (c y4) * c y2 + star (c y6) * c y9 + star (c y8) * c y11))) := by
      rw [split_mk101000 c d hc hd bt000000]
      simp only [sgB_000000_2, sgB_000000_4, sgB_000000_6, sgB_000000_9, sgB_000000_8, sgB_000000_11, sgT_000000_2, sgT_000000_4, sgT_000000_6, sgT_000000_9, sgT_000000_8, sgT_000000_11,
        SS.signC_false]
      rw [htf.t2, htf.t4, htf.t6, htf.t9, htf.t8, htf.t11]
      simp only [star_neg, star_mul', star_star, star_add]
      linear_combination (Complex.I ^ (SS.PauliString.mk bt101000 bt000000).numY * ((star (c y4) * c y2 + star (c y6) * c y9 + star (c y8) * c y11) + (star (c y2) * c y4 + star (c y9) * c y6 + star (c y11) * c y8))) * htf.unit
    rw [h, normSq_I_pow_mul, normSq_two_mul]
  · have h : projTrace c d ⟨bt101000, bt001000⟩
        = Complex.I ^ (SS.PauliString.mk bt101000 bt001000).numY * (2 * (-((star (c y4) * c y2 + star (c y6) * c y9 + star (c y8) * c y11) - star (star (c y4) * c y2 + star (c y6) * c y9 + star (c y8) * c y11)))) := by
      rw [split_mk101000 c d hc hd bt001000]
      simp only [sgB_001000_2, sgB_001000_4, sgB_001000_6, sgB_001000_9, sgB_001000_8, sgB_001000_11, sgT_001000_2, sgT_001000_4, sgT_001000_6, sgT_001000_9, sgT_001000_8, sgT_001000_11,
        SS.signC_false, SS.signC_true]
      rw [htf.t2, htf.t4, htf.t6, htf.t9, htf.t8, htf.t11]
      simp only [star_neg, star_mul', star_star, star_add]
      linear_combination (Complex.I ^ (SS.PauliString.mk bt101000 bt001000).numY * (-((star (c y4) * c y2 + star (c y6) * c y9 + star (c y8) * c y11) - (star (c y2) * c y4 + star (c y9) * c y6 + star (c y11) * c y8)))) * htf.unit
    rw [h, normSq_I_pow_mul, normSq_two_mul, Complex.normSq_neg]
  · have h : projTrace c d ⟨bt101000, bt100000⟩
        = Complex.I ^ (SS.PauliString.mk bt101000 bt100000).numY * (2 * ((star (c y4) * c y2 + star (c y6) * c y9 + star (c y8) * c y11) - star (star (c y4) * c y2 + star (c y6) * c y9 + star (c y8) * c y11))) := by
      rw [split_mk101000 c d hc hd bt100000]
      simp only [sgB_100000_2, sgB_100000_4, sgB_100000_6, sgB_100000_9, sgB_100000_8, sgB_100000_11, sgT_100000_2, sgT_100000_4, sgT_100000_6, sgT_100000_9, sgT_100000_8, sgT_100000_11,
        SS.signC_false, SS.signC_true]
      rw [htf.t2, htf.t4, htf.t6, htf.t9, htf.t8, htf.t11]
      simp only [star_neg, star_mul', star_star, star_add]
      linear_combination (Complex.I ^ (SS.PauliString.mk bt101000 bt100000).numY * ((star (c y4) * c y2 + star (c y6) * c y9 + star (c y8) * c y11) - (star (c y2) * c y4 + star (c y9) * c y6 + star (c y11) * c y8))) * htf.unit
    rw [h, normSq_I_pow_mul, normSq_two_mul]
  · have h : projTrace c d ⟨bt101000, bt101000⟩
        = Complex.I ^ (SS.PauliString.mk bt101000 bt101000).numY * (2 * (-((star (c y4) * c y2 + star (c y6) * c y9 + star (c y8) * c y11) + star (star (c y4) * c y2 + star (c y6) * c y9 + star (c y8) * c y11)))) := by
      rw [split_mk101000 c d hc hd bt101000]
      simp only [sgB_101000_2, sgB_101000_4, sgB_101000_6, sgB_101000_9, sgB_101000_8, sgB_101000_11, sgT_101000_2, sgT_101000_4, sgT_101000_6, sgT_101000_9, sgT_101000_8, sgT_101000_11,
        SS.signC_true]
      rw [htf.t2, htf.t4, htf.t6, htf.t9, htf.t8, htf.t11]
      simp only [star_neg, star_mul', star_star, star_add]
      linear_combination (Complex.I ^ (SS.PauliString.mk bt101000 bt101000).numY * (-((star (c y4) * c y2 + star (c y6) * c y9 + star (c y8) * c y11) + (star (c y2) * c y4 + star (c y9) * c y6 + star (c y11) * c y8)))) * htf.unit
    rw [h, normSq_I_pow_mul, normSq_two_mul, Complex.normSq_neg]

set_option maxHeartbeats 1600000 in
/-- The four dressings of the flip mask `100100`.  Their projector traces are
`+-2 (G + conj G)` and `+-2 (G - conj G)`, so this mask contributes
`32 * normSq G` to the weight-two sum. -/
theorem vals_mk100100 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (tau : ℂ) (htf : TopForm c d tau) :
    Complex.normSq (projTrace c d ⟨bt100100, bt000000⟩)
        = 4 * Complex.normSq ((star (c y5) * c y2 + star (c y6) * c y10 + star (c y7) * c y11) + star (star (c y5) * c y2 + star (c y6) * c y10 + star (c y7) * c y11))
      ∧ Complex.normSq (projTrace c d ⟨bt100100, bt000100⟩)
        = 4 * Complex.normSq ((star (c y5) * c y2 + star (c y6) * c y10 + star (c y7) * c y11) - star (star (c y5) * c y2 + star (c y6) * c y10 + star (c y7) * c y11))
      ∧ Complex.normSq (projTrace c d ⟨bt100100, bt100000⟩)
        = 4 * Complex.normSq ((star (c y5) * c y2 + star (c y6) * c y10 + star (c y7) * c y11) - star (star (c y5) * c y2 + star (c y6) * c y10 + star (c y7) * c y11))
      ∧ Complex.normSq (projTrace c d ⟨bt100100, bt100100⟩)
        = 4 * Complex.normSq ((star (c y5) * c y2 + star (c y6) * c y10 + star (c y7) * c y11) + star (star (c y5) * c y2 + star (c y6) * c y10 + star (c y7) * c y11)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h : projTrace c d ⟨bt100100, bt000000⟩
        = Complex.I ^ (SS.PauliString.mk bt100100 bt000000).numY * (2 * ((star (c y5) * c y2 + star (c y6) * c y10 + star (c y7) * c y11) + star (star (c y5) * c y2 + star (c y6) * c y10 + star (c y7) * c y11))) := by
      rw [split_mk100100 c d hc hd bt000000]
      simp only [sgB_000000_2, sgB_000000_5, sgB_000000_6, sgB_000000_10, sgB_000000_7, sgB_000000_11, sgT_000000_2, sgT_000000_5, sgT_000000_6, sgT_000000_10, sgT_000000_7, sgT_000000_11,
        SS.signC_false]
      rw [htf.t2, htf.t5, htf.t6, htf.t10, htf.t7, htf.t11]
      simp only [star_neg, star_mul', star_star, star_add]
      linear_combination (Complex.I ^ (SS.PauliString.mk bt100100 bt000000).numY * ((star (c y5) * c y2 + star (c y6) * c y10 + star (c y7) * c y11) + (star (c y2) * c y5 + star (c y10) * c y6 + star (c y11) * c y7))) * htf.unit
    rw [h, normSq_I_pow_mul, normSq_two_mul]
  · have h : projTrace c d ⟨bt100100, bt000100⟩
        = Complex.I ^ (SS.PauliString.mk bt100100 bt000100).numY * (2 * (-((star (c y5) * c y2 + star (c y6) * c y10 + star (c y7) * c y11) - star (star (c y5) * c y2 + star (c y6) * c y10 + star (c y7) * c y11)))) := by
      rw [split_mk100100 c d hc hd bt000100]
      simp only [sgB_000100_2, sgB_000100_5, sgB_000100_6, sgB_000100_10, sgB_000100_7, sgB_000100_11, sgT_000100_2, sgT_000100_5, sgT_000100_6, sgT_000100_10, sgT_000100_7, sgT_000100_11,
        SS.signC_false, SS.signC_true]
      rw [htf.t2, htf.t5, htf.t6, htf.t10, htf.t7, htf.t11]
      simp only [star_neg, star_mul', star_star, star_add]
      linear_combination (Complex.I ^ (SS.PauliString.mk bt100100 bt000100).numY * (-((star (c y5) * c y2 + star (c y6) * c y10 + star (c y7) * c y11) - (star (c y2) * c y5 + star (c y10) * c y6 + star (c y11) * c y7)))) * htf.unit
    rw [h, normSq_I_pow_mul, normSq_two_mul, Complex.normSq_neg]
  · have h : projTrace c d ⟨bt100100, bt100000⟩
        = Complex.I ^ (SS.PauliString.mk bt100100 bt100000).numY * (2 * ((star (c y5) * c y2 + star (c y6) * c y10 + star (c y7) * c y11) - star (star (c y5) * c y2 + star (c y6) * c y10 + star (c y7) * c y11))) := by
      rw [split_mk100100 c d hc hd bt100000]
      simp only [sgB_100000_2, sgB_100000_5, sgB_100000_6, sgB_100000_10, sgB_100000_7, sgB_100000_11, sgT_100000_2, sgT_100000_5, sgT_100000_6, sgT_100000_10, sgT_100000_7, sgT_100000_11,
        SS.signC_false, SS.signC_true]
      rw [htf.t2, htf.t5, htf.t6, htf.t10, htf.t7, htf.t11]
      simp only [star_neg, star_mul', star_star, star_add]
      linear_combination (Complex.I ^ (SS.PauliString.mk bt100100 bt100000).numY * ((star (c y5) * c y2 + star (c y6) * c y10 + star (c y7) * c y11) - (star (c y2) * c y5 + star (c y10) * c y6 + star (c y11) * c y7))) * htf.unit
    rw [h, normSq_I_pow_mul, normSq_two_mul]
  · have h : projTrace c d ⟨bt100100, bt100100⟩
        = Complex.I ^ (SS.PauliString.mk bt100100 bt100100).numY * (2 * (-((star (c y5) * c y2 + star (c y6) * c y10 + star (c y7) * c y11) + star (star (c y5) * c y2 + star (c y6) * c y10 + star (c y7) * c y11)))) := by
      rw [split_mk100100 c d hc hd bt100100]
      simp only [sgB_100100_2, sgB_100100_5, sgB_100100_6, sgB_100100_10, sgB_100100_7, sgB_100100_11, sgT_100100_2, sgT_100100_5, sgT_100100_6, sgT_100100_10, sgT_100100_7, sgT_100100_11,
        SS.signC_true]
      rw [htf.t2, htf.t5, htf.t6, htf.t10, htf.t7, htf.t11]
      simp only [star_neg, star_mul', star_star, star_add]
      linear_combination (Complex.I ^ (SS.PauliString.mk bt100100 bt100100).numY * (-((star (c y5) * c y2 + star (c y6) * c y10 + star (c y7) * c y11) + (star (c y2) * c y5 + star (c y10) * c y6 + star (c y11) * c y7)))) * htf.unit
    rw [h, normSq_I_pow_mul, normSq_two_mul, Complex.normSq_neg]

set_option maxHeartbeats 1600000 in
/-- The four dressings of the flip mask `011000`.  Their projector traces are
`+-2 (G + conj G)` and `+-2 (G - conj G)`, so this mask contributes
`32 * normSq G` to the weight-two sum. -/
theorem vals_mk011000 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (tau : ℂ) (htf : TopForm c d tau) :
    Complex.normSq (projTrace c d ⟨bt011000, bt000000⟩)
        = 4 * Complex.normSq ((star (c y4) * c y3 + star (c y6) * c y7 + star (c y10) * c y11) + star (star (c y4) * c y3 + star (c y6) * c y7 + star (c y10) * c y11))
      ∧ Complex.normSq (projTrace c d ⟨bt011000, bt001000⟩)
        = 4 * Complex.normSq ((star (c y4) * c y3 + star (c y6) * c y7 + star (c y10) * c y11) - star (star (c y4) * c y3 + star (c y6) * c y7 + star (c y10) * c y11))
      ∧ Complex.normSq (projTrace c d ⟨bt011000, bt010000⟩)
        = 4 * Complex.normSq ((star (c y4) * c y3 + star (c y6) * c y7 + star (c y10) * c y11) - star (star (c y4) * c y3 + star (c y6) * c y7 + star (c y10) * c y11))
      ∧ Complex.normSq (projTrace c d ⟨bt011000, bt011000⟩)
        = 4 * Complex.normSq ((star (c y4) * c y3 + star (c y6) * c y7 + star (c y10) * c y11) + star (star (c y4) * c y3 + star (c y6) * c y7 + star (c y10) * c y11)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h : projTrace c d ⟨bt011000, bt000000⟩
        = Complex.I ^ (SS.PauliString.mk bt011000 bt000000).numY * (2 * ((star (c y4) * c y3 + star (c y6) * c y7 + star (c y10) * c y11) + star (star (c y4) * c y3 + star (c y6) * c y7 + star (c y10) * c y11))) := by
      rw [split_mk011000 c d hc hd bt000000]
      simp only [sgB_000000_3, sgB_000000_4, sgB_000000_6, sgB_000000_7, sgB_000000_10, sgB_000000_11, sgT_000000_3, sgT_000000_4, sgT_000000_6, sgT_000000_7, sgT_000000_10, sgT_000000_11,
        SS.signC_false]
      rw [htf.t3, htf.t4, htf.t6, htf.t7, htf.t10, htf.t11]
      simp only [star_neg, star_mul', star_star, star_add]
      linear_combination (Complex.I ^ (SS.PauliString.mk bt011000 bt000000).numY * ((star (c y4) * c y3 + star (c y6) * c y7 + star (c y10) * c y11) + (star (c y3) * c y4 + star (c y7) * c y6 + star (c y11) * c y10))) * htf.unit
    rw [h, normSq_I_pow_mul, normSq_two_mul]
  · have h : projTrace c d ⟨bt011000, bt001000⟩
        = Complex.I ^ (SS.PauliString.mk bt011000 bt001000).numY * (2 * (-((star (c y4) * c y3 + star (c y6) * c y7 + star (c y10) * c y11) - star (star (c y4) * c y3 + star (c y6) * c y7 + star (c y10) * c y11)))) := by
      rw [split_mk011000 c d hc hd bt001000]
      simp only [sgB_001000_3, sgB_001000_4, sgB_001000_6, sgB_001000_7, sgB_001000_10, sgB_001000_11, sgT_001000_3, sgT_001000_4, sgT_001000_6, sgT_001000_7, sgT_001000_10, sgT_001000_11,
        SS.signC_false, SS.signC_true]
      rw [htf.t3, htf.t4, htf.t6, htf.t7, htf.t10, htf.t11]
      simp only [star_neg, star_mul', star_star, star_add]
      linear_combination (Complex.I ^ (SS.PauliString.mk bt011000 bt001000).numY * (-((star (c y4) * c y3 + star (c y6) * c y7 + star (c y10) * c y11) - (star (c y3) * c y4 + star (c y7) * c y6 + star (c y11) * c y10)))) * htf.unit
    rw [h, normSq_I_pow_mul, normSq_two_mul, Complex.normSq_neg]
  · have h : projTrace c d ⟨bt011000, bt010000⟩
        = Complex.I ^ (SS.PauliString.mk bt011000 bt010000).numY * (2 * ((star (c y4) * c y3 + star (c y6) * c y7 + star (c y10) * c y11) - star (star (c y4) * c y3 + star (c y6) * c y7 + star (c y10) * c y11))) := by
      rw [split_mk011000 c d hc hd bt010000]
      simp only [sgB_010000_3, sgB_010000_4, sgB_010000_6, sgB_010000_7, sgB_010000_10, sgB_010000_11, sgT_010000_3, sgT_010000_4, sgT_010000_6, sgT_010000_7, sgT_010000_10, sgT_010000_11,
        SS.signC_false, SS.signC_true]
      rw [htf.t3, htf.t4, htf.t6, htf.t7, htf.t10, htf.t11]
      simp only [star_neg, star_mul', star_star, star_add]
      linear_combination (Complex.I ^ (SS.PauliString.mk bt011000 bt010000).numY * ((star (c y4) * c y3 + star (c y6) * c y7 + star (c y10) * c y11) - (star (c y3) * c y4 + star (c y7) * c y6 + star (c y11) * c y10))) * htf.unit
    rw [h, normSq_I_pow_mul, normSq_two_mul]
  · have h : projTrace c d ⟨bt011000, bt011000⟩
        = Complex.I ^ (SS.PauliString.mk bt011000 bt011000).numY * (2 * (-((star (c y4) * c y3 + star (c y6) * c y7 + star (c y10) * c y11) + star (star (c y4) * c y3 + star (c y6) * c y7 + star (c y10) * c y11)))) := by
      rw [split_mk011000 c d hc hd bt011000]
      simp only [sgB_011000_3, sgB_011000_4, sgB_011000_6, sgB_011000_7, sgB_011000_10, sgB_011000_11, sgT_011000_3, sgT_011000_4, sgT_011000_6, sgT_011000_7, sgT_011000_10, sgT_011000_11,
        SS.signC_true]
      rw [htf.t3, htf.t4, htf.t6, htf.t7, htf.t10, htf.t11]
      simp only [star_neg, star_mul', star_star, star_add]
      linear_combination (Complex.I ^ (SS.PauliString.mk bt011000 bt011000).numY * (-((star (c y4) * c y3 + star (c y6) * c y7 + star (c y10) * c y11) + (star (c y3) * c y4 + star (c y7) * c y6 + star (c y11) * c y10)))) * htf.unit
    rw [h, normSq_I_pow_mul, normSq_two_mul, Complex.normSq_neg]

set_option maxHeartbeats 1600000 in
/-- The four dressings of the flip mask `010100`.  Their projector traces are
`+-2 (G + conj G)` and `+-2 (G - conj G)`, so this mask contributes
`32 * normSq G` to the weight-two sum. -/
theorem vals_mk010100 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (tau : ℂ) (htf : TopForm c d tau) :
    Complex.normSq (projTrace c d ⟨bt010100, bt000000⟩)
        = 4 * Complex.normSq ((star (c y5) * c y3 + star (c y6) * c y8 + star (c y9) * c y11) + star (star (c y5) * c y3 + star (c y6) * c y8 + star (c y9) * c y11))
      ∧ Complex.normSq (projTrace c d ⟨bt010100, bt000100⟩)
        = 4 * Complex.normSq ((star (c y5) * c y3 + star (c y6) * c y8 + star (c y9) * c y11) - star (star (c y5) * c y3 + star (c y6) * c y8 + star (c y9) * c y11))
      ∧ Complex.normSq (projTrace c d ⟨bt010100, bt010000⟩)
        = 4 * Complex.normSq ((star (c y5) * c y3 + star (c y6) * c y8 + star (c y9) * c y11) - star (star (c y5) * c y3 + star (c y6) * c y8 + star (c y9) * c y11))
      ∧ Complex.normSq (projTrace c d ⟨bt010100, bt010100⟩)
        = 4 * Complex.normSq ((star (c y5) * c y3 + star (c y6) * c y8 + star (c y9) * c y11) + star (star (c y5) * c y3 + star (c y6) * c y8 + star (c y9) * c y11)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h : projTrace c d ⟨bt010100, bt000000⟩
        = Complex.I ^ (SS.PauliString.mk bt010100 bt000000).numY * (2 * ((star (c y5) * c y3 + star (c y6) * c y8 + star (c y9) * c y11) + star (star (c y5) * c y3 + star (c y6) * c y8 + star (c y9) * c y11))) := by
      rw [split_mk010100 c d hc hd bt000000]
      simp only [sgB_000000_3, sgB_000000_5, sgB_000000_6, sgB_000000_8, sgB_000000_9, sgB_000000_11, sgT_000000_3, sgT_000000_5, sgT_000000_6, sgT_000000_8, sgT_000000_9, sgT_000000_11,
        SS.signC_false]
      rw [htf.t3, htf.t5, htf.t6, htf.t8, htf.t9, htf.t11]
      simp only [star_neg, star_mul', star_star, star_add]
      linear_combination (Complex.I ^ (SS.PauliString.mk bt010100 bt000000).numY * ((star (c y5) * c y3 + star (c y6) * c y8 + star (c y9) * c y11) + (star (c y3) * c y5 + star (c y8) * c y6 + star (c y11) * c y9))) * htf.unit
    rw [h, normSq_I_pow_mul, normSq_two_mul]
  · have h : projTrace c d ⟨bt010100, bt000100⟩
        = Complex.I ^ (SS.PauliString.mk bt010100 bt000100).numY * (2 * (-((star (c y5) * c y3 + star (c y6) * c y8 + star (c y9) * c y11) - star (star (c y5) * c y3 + star (c y6) * c y8 + star (c y9) * c y11)))) := by
      rw [split_mk010100 c d hc hd bt000100]
      simp only [sgB_000100_3, sgB_000100_5, sgB_000100_6, sgB_000100_8, sgB_000100_9, sgB_000100_11, sgT_000100_3, sgT_000100_5, sgT_000100_6, sgT_000100_8, sgT_000100_9, sgT_000100_11,
        SS.signC_false, SS.signC_true]
      rw [htf.t3, htf.t5, htf.t6, htf.t8, htf.t9, htf.t11]
      simp only [star_neg, star_mul', star_star, star_add]
      linear_combination (Complex.I ^ (SS.PauliString.mk bt010100 bt000100).numY * (-((star (c y5) * c y3 + star (c y6) * c y8 + star (c y9) * c y11) - (star (c y3) * c y5 + star (c y8) * c y6 + star (c y11) * c y9)))) * htf.unit
    rw [h, normSq_I_pow_mul, normSq_two_mul, Complex.normSq_neg]
  · have h : projTrace c d ⟨bt010100, bt010000⟩
        = Complex.I ^ (SS.PauliString.mk bt010100 bt010000).numY * (2 * ((star (c y5) * c y3 + star (c y6) * c y8 + star (c y9) * c y11) - star (star (c y5) * c y3 + star (c y6) * c y8 + star (c y9) * c y11))) := by
      rw [split_mk010100 c d hc hd bt010000]
      simp only [sgB_010000_3, sgB_010000_5, sgB_010000_6, sgB_010000_8, sgB_010000_9, sgB_010000_11, sgT_010000_3, sgT_010000_5, sgT_010000_6, sgT_010000_8, sgT_010000_9, sgT_010000_11,
        SS.signC_false, SS.signC_true]
      rw [htf.t3, htf.t5, htf.t6, htf.t8, htf.t9, htf.t11]
      simp only [star_neg, star_mul', star_star, star_add]
      linear_combination (Complex.I ^ (SS.PauliString.mk bt010100 bt010000).numY * ((star (c y5) * c y3 + star (c y6) * c y8 + star (c y9) * c y11) - (star (c y3) * c y5 + star (c y8) * c y6 + star (c y11) * c y9))) * htf.unit
    rw [h, normSq_I_pow_mul, normSq_two_mul]
  · have h : projTrace c d ⟨bt010100, bt010100⟩
        = Complex.I ^ (SS.PauliString.mk bt010100 bt010100).numY * (2 * (-((star (c y5) * c y3 + star (c y6) * c y8 + star (c y9) * c y11) + star (star (c y5) * c y3 + star (c y6) * c y8 + star (c y9) * c y11)))) := by
      rw [split_mk010100 c d hc hd bt010100]
      simp only [sgB_010100_3, sgB_010100_5, sgB_010100_6, sgB_010100_8, sgB_010100_9, sgB_010100_11, sgT_010100_3, sgT_010100_5, sgT_010100_6, sgT_010100_8, sgT_010100_9, sgT_010100_11,
        SS.signC_true]
      rw [htf.t3, htf.t5, htf.t6, htf.t8, htf.t9, htf.t11]
      simp only [star_neg, star_mul', star_star, star_add]
      linear_combination (Complex.I ^ (SS.PauliString.mk bt010100 bt010100).numY * (-((star (c y5) * c y3 + star (c y6) * c y8 + star (c y9) * c y11) + (star (c y3) * c y5 + star (c y8) * c y6 + star (c y11) * c y9)))) * htf.unit
    rw [h, normSq_I_pow_mul, normSq_two_mul, Complex.normSq_neg]

set_option maxHeartbeats 1600000 in
/-- The four dressings of the flip mask `001100`.  Their projector traces are
`+-2 (G + conj G)` and `+-2 (G - conj G)`, so this mask contributes
`32 * normSq G` to the weight-two sum. -/
theorem vals_mk001100 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (tau : ℂ) (htf : TopForm c d tau) :
    Complex.normSq (projTrace c d ⟨bt001100, bt000000⟩)
        = 4 * Complex.normSq ((star (c y5) * c y4 + star (c y7) * c y8 + star (c y9) * c y10) + star (star (c y5) * c y4 + star (c y7) * c y8 + star (c y9) * c y10))
      ∧ Complex.normSq (projTrace c d ⟨bt001100, bt000100⟩)
        = 4 * Complex.normSq ((star (c y5) * c y4 + star (c y7) * c y8 + star (c y9) * c y10) - star (star (c y5) * c y4 + star (c y7) * c y8 + star (c y9) * c y10))
      ∧ Complex.normSq (projTrace c d ⟨bt001100, bt001000⟩)
        = 4 * Complex.normSq ((star (c y5) * c y4 + star (c y7) * c y8 + star (c y9) * c y10) - star (star (c y5) * c y4 + star (c y7) * c y8 + star (c y9) * c y10))
      ∧ Complex.normSq (projTrace c d ⟨bt001100, bt001100⟩)
        = 4 * Complex.normSq ((star (c y5) * c y4 + star (c y7) * c y8 + star (c y9) * c y10) + star (star (c y5) * c y4 + star (c y7) * c y8 + star (c y9) * c y10)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h : projTrace c d ⟨bt001100, bt000000⟩
        = Complex.I ^ (SS.PauliString.mk bt001100 bt000000).numY * (2 * ((star (c y5) * c y4 + star (c y7) * c y8 + star (c y9) * c y10) + star (star (c y5) * c y4 + star (c y7) * c y8 + star (c y9) * c y10))) := by
      rw [split_mk001100 c d hc hd bt000000]
      simp only [sgB_000000_4, sgB_000000_5, sgB_000000_7, sgB_000000_8, sgB_000000_9, sgB_000000_10, sgT_000000_4, sgT_000000_5, sgT_000000_7, sgT_000000_8, sgT_000000_9, sgT_000000_10,
        SS.signC_false]
      rw [htf.t4, htf.t5, htf.t7, htf.t8, htf.t9, htf.t10]
      simp only [star_neg, star_mul', star_star, star_add]
      linear_combination (Complex.I ^ (SS.PauliString.mk bt001100 bt000000).numY * ((star (c y5) * c y4 + star (c y7) * c y8 + star (c y9) * c y10) + (star (c y4) * c y5 + star (c y8) * c y7 + star (c y10) * c y9))) * htf.unit
    rw [h, normSq_I_pow_mul, normSq_two_mul]
  · have h : projTrace c d ⟨bt001100, bt000100⟩
        = Complex.I ^ (SS.PauliString.mk bt001100 bt000100).numY * (2 * (-((star (c y5) * c y4 + star (c y7) * c y8 + star (c y9) * c y10) - star (star (c y5) * c y4 + star (c y7) * c y8 + star (c y9) * c y10)))) := by
      rw [split_mk001100 c d hc hd bt000100]
      simp only [sgB_000100_4, sgB_000100_5, sgB_000100_7, sgB_000100_8, sgB_000100_9, sgB_000100_10, sgT_000100_4, sgT_000100_5, sgT_000100_7, sgT_000100_8, sgT_000100_9, sgT_000100_10,
        SS.signC_false, SS.signC_true]
      rw [htf.t4, htf.t5, htf.t7, htf.t8, htf.t9, htf.t10]
      simp only [star_neg, star_mul', star_star, star_add]
      linear_combination (Complex.I ^ (SS.PauliString.mk bt001100 bt000100).numY * (-((star (c y5) * c y4 + star (c y7) * c y8 + star (c y9) * c y10) - (star (c y4) * c y5 + star (c y8) * c y7 + star (c y10) * c y9)))) * htf.unit
    rw [h, normSq_I_pow_mul, normSq_two_mul, Complex.normSq_neg]
  · have h : projTrace c d ⟨bt001100, bt001000⟩
        = Complex.I ^ (SS.PauliString.mk bt001100 bt001000).numY * (2 * ((star (c y5) * c y4 + star (c y7) * c y8 + star (c y9) * c y10) - star (star (c y5) * c y4 + star (c y7) * c y8 + star (c y9) * c y10))) := by
      rw [split_mk001100 c d hc hd bt001000]
      simp only [sgB_001000_4, sgB_001000_5, sgB_001000_7, sgB_001000_8, sgB_001000_9, sgB_001000_10, sgT_001000_4, sgT_001000_5, sgT_001000_7, sgT_001000_8, sgT_001000_9, sgT_001000_10,
        SS.signC_false, SS.signC_true]
      rw [htf.t4, htf.t5, htf.t7, htf.t8, htf.t9, htf.t10]
      simp only [star_neg, star_mul', star_star, star_add]
      linear_combination (Complex.I ^ (SS.PauliString.mk bt001100 bt001000).numY * ((star (c y5) * c y4 + star (c y7) * c y8 + star (c y9) * c y10) - (star (c y4) * c y5 + star (c y8) * c y7 + star (c y10) * c y9))) * htf.unit
    rw [h, normSq_I_pow_mul, normSq_two_mul]
  · have h : projTrace c d ⟨bt001100, bt001100⟩
        = Complex.I ^ (SS.PauliString.mk bt001100 bt001100).numY * (2 * (-((star (c y5) * c y4 + star (c y7) * c y8 + star (c y9) * c y10) + star (star (c y5) * c y4 + star (c y7) * c y8 + star (c y9) * c y10)))) := by
      rw [split_mk001100 c d hc hd bt001100]
      simp only [sgB_001100_4, sgB_001100_5, sgB_001100_7, sgB_001100_8, sgB_001100_9, sgB_001100_10, sgT_001100_4, sgT_001100_5, sgT_001100_7, sgT_001100_8, sgT_001100_9, sgT_001100_10,
        SS.signC_true]
      rw [htf.t4, htf.t5, htf.t7, htf.t8, htf.t9, htf.t10]
      simp only [star_neg, star_mul', star_star, star_add]
      linear_combination (Complex.I ^ (SS.PauliString.mk bt001100 bt001100).numY * (-((star (c y5) * c y4 + star (c y7) * c y8 + star (c y9) * c y10) + (star (c y4) * c y5 + star (c y8) * c y7 + star (c y10) * c y9)))) * htf.unit
    rw [h, normSq_I_pow_mul, normSq_two_mul, Complex.normSq_neg]

set_option maxHeartbeats 1600000 in
/-- The four dressings of the flip mask `000011`.  Their projector traces are
`+-2 (G + conj G)` and `+-2 (G - conj G)`, so this mask contributes
`32 * normSq G` to the weight-two sum. -/
theorem vals_mk000011 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (tau : ℂ) (htf : TopForm c d tau) :
    Complex.normSq (projTrace c d ⟨bt000011, bt000000⟩)
        = 4 * Complex.normSq ((star (c y1) * c y0) + star (star (c y1) * c y0))
      ∧ Complex.normSq (projTrace c d ⟨bt000011, bt000001⟩)
        = 4 * Complex.normSq ((star (c y1) * c y0) - star (star (c y1) * c y0))
      ∧ Complex.normSq (projTrace c d ⟨bt000011, bt000010⟩)
        = 4 * Complex.normSq ((star (c y1) * c y0) - star (star (c y1) * c y0))
      ∧ Complex.normSq (projTrace c d ⟨bt000011, bt000011⟩)
        = 4 * Complex.normSq ((star (c y1) * c y0) + star (star (c y1) * c y0)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h : projTrace c d ⟨bt000011, bt000000⟩
        = Complex.I ^ (SS.PauliString.mk bt000011 bt000000).numY * (2 * ((star (c y1) * c y0) + star (star (c y1) * c y0))) := by
      rw [split_mk000011 c d hc hd bt000000]
      simp only [sgB_000000_0, sgB_000000_1, sgT_000000_0, sgT_000000_1,
        SS.signC_false]
      rw [htf.t0, htf.t1]
      simp only [star_mul', star_star]
      linear_combination (Complex.I ^ (SS.PauliString.mk bt000011 bt000000).numY * ((star (c y1) * c y0) + (star (c y0) * c y1))) * htf.unit
    rw [h, normSq_I_pow_mul, normSq_two_mul]
  · have h : projTrace c d ⟨bt000011, bt000001⟩
        = Complex.I ^ (SS.PauliString.mk bt000011 bt000001).numY * (2 * ((star (c y1) * c y0) - star (star (c y1) * c y0))) := by
      rw [split_mk000011 c d hc hd bt000001]
      simp only [sgB_000001_0, sgB_000001_1, sgT_000001_0, sgT_000001_1,
        SS.signC_false, SS.signC_true]
      rw [htf.t0, htf.t1]
      simp only [star_mul', star_star]
      linear_combination (Complex.I ^ (SS.PauliString.mk bt000011 bt000001).numY * ((star (c y1) * c y0) - (star (c y0) * c y1))) * htf.unit
    rw [h, normSq_I_pow_mul, normSq_two_mul]
  · have h : projTrace c d ⟨bt000011, bt000010⟩
        = Complex.I ^ (SS.PauliString.mk bt000011 bt000010).numY * (2 * ((star (c y1) * c y0) - star (star (c y1) * c y0))) := by
      rw [split_mk000011 c d hc hd bt000010]
      simp only [sgB_000010_0, sgB_000010_1, sgT_000010_0, sgT_000010_1,
        SS.signC_false, SS.signC_true]
      rw [htf.t0, htf.t1]
      simp only [star_mul', star_star]
      linear_combination (Complex.I ^ (SS.PauliString.mk bt000011 bt000010).numY * ((star (c y1) * c y0) - (star (c y0) * c y1))) * htf.unit
    rw [h, normSq_I_pow_mul, normSq_two_mul]
  · have h : projTrace c d ⟨bt000011, bt000011⟩
        = Complex.I ^ (SS.PauliString.mk bt000011 bt000011).numY * (2 * ((star (c y1) * c y0) + star (star (c y1) * c y0))) := by
      rw [split_mk000011 c d hc hd bt000011]
      simp only [sgB_000011_0, sgB_000011_1, sgT_000011_0, sgT_000011_1,
        SS.signC_false]
      rw [htf.t0, htf.t1]
      simp only [star_mul', star_star]
      linear_combination (Complex.I ^ (SS.PauliString.mk bt000011 bt000011).numY * ((star (c y1) * c y0) + (star (c y0) * c y1))) * htf.unit
    rw [h, normSq_I_pow_mul, normSq_two_mul]

/-! ## 11.  The enumerator coefficients -/

/-- The eight flip masks of Hamming weight at most two that join two points of a
fiber. -/
def gm2 : Finset (SS.BitString 6) :=
  {bt000000, bt110000, bt101000, bt100100, bt011000, bt010100, bt001100, bt000011}

theorem masks2 : ∀ f : SS.BitString 6, SS.hammingWt f ≤ 2 →
    f ∈ gm2 ∨ (S0.filter (fun s => SS.bxor s f ∈ S0) = ∅
        ∧ S1.filter (fun s => SS.bxor s f ∈ S1) = ∅) := by decide

theorem masks0 : ∀ f : SS.BitString 6, SS.hammingWt f ≤ 0 → f = bt000000 := by decide

def Zsmk000000 : Finset (SS.BitString 6) :=
  {bt000011, bt000101, bt000110, bt001001, bt001010, bt001100, bt010001, bt010010, bt010100, bt011000, bt100001, bt100010, bt100100, bt101000, bt110000}

theorem zset_mk000000 : ∀ zz : SS.BitString 6, zz ∉ Zsmk000000 →
    (SS.PauliString.mk bt000000 zz).wt ≠ 2 := by decide

def Zsmk110000 : Finset (SS.BitString 6) :=
  {bt000000, bt010000, bt100000, bt110000}

theorem zset_mk110000 : ∀ zz : SS.BitString 6, zz ∉ Zsmk110000 →
    (SS.PauliString.mk bt110000 zz).wt ≠ 2 := by decide

def Zsmk101000 : Finset (SS.BitString 6) :=
  {bt000000, bt001000, bt100000, bt101000}

theorem zset_mk101000 : ∀ zz : SS.BitString 6, zz ∉ Zsmk101000 →
    (SS.PauliString.mk bt101000 zz).wt ≠ 2 := by decide

def Zsmk100100 : Finset (SS.BitString 6) :=
  {bt000000, bt000100, bt100000, bt100100}

theorem zset_mk100100 : ∀ zz : SS.BitString 6, zz ∉ Zsmk100100 →
    (SS.PauliString.mk bt100100 zz).wt ≠ 2 := by decide

def Zsmk011000 : Finset (SS.BitString 6) :=
  {bt000000, bt001000, bt010000, bt011000}

theorem zset_mk011000 : ∀ zz : SS.BitString 6, zz ∉ Zsmk011000 →
    (SS.PauliString.mk bt011000 zz).wt ≠ 2 := by decide

def Zsmk010100 : Finset (SS.BitString 6) :=
  {bt000000, bt000100, bt010000, bt010100}

theorem zset_mk010100 : ∀ zz : SS.BitString 6, zz ∉ Zsmk010100 →
    (SS.PauliString.mk bt010100 zz).wt ≠ 2 := by decide

def Zsmk001100 : Finset (SS.BitString 6) :=
  {bt000000, bt000100, bt001000, bt001100}

theorem zset_mk001100 : ∀ zz : SS.BitString 6, zz ∉ Zsmk001100 →
    (SS.PauliString.mk bt001100 zz).wt ≠ 2 := by decide

def Zsmk000011 : Finset (SS.BitString 6) :=
  {bt000000, bt000001, bt000010, bt000011}

theorem zset_mk000011 : ∀ zz : SS.BitString 6, zz ∉ Zsmk000011 →
    (SS.PauliString.mk bt000011 zz).wt ≠ 2 := by decide

def Zs0 : Finset (SS.BitString 6) := {bt000000}

theorem zset_0 : ∀ zz : SS.BitString 6, zz ∉ Zs0 →
    (SS.PauliString.mk bt000000 zz).wt ≠ 0 := by decide

/-- The enumerator sum, split into an outer sum over flip masks and an inner sum
over dressings. -/
theorem AEnum_split (c d : SS.BitString 6 -> ℂ) (j : ℕ) :
    AEnum c d j = (∑ f : SS.BitString 6, ∑ zz : SS.BitString 6,
        if (SS.PauliString.mk f zz).wt = j
          then Complex.normSq (projTrace c d ⟨f, zz⟩) else 0) / 4 := by
  rw [AEnum, paulisOfWeight, Finset.sum_filter, Fintype.sum_prod_type]

set_option maxHeartbeats 1600000 in
/-- **`A_0 = 1`.**  The identity is the only weight-zero Pauli, and its projector
trace is the sum of the two normalizations. -/
theorem A0_value (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
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
    AEnum c d 0 = 1 := by
  obtain ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11⟩ :=
    magnitudes_forced c d hm ho0 ho1 ho2 ho3 ho4 ho5 ho6 ho7 ho8 ho9 ho10 ho11 ho12 ho13 ho14 ho15 ho16 ho17 ho18 ho19 ho20
  obtain ⟨v0, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    diag_values c d hc hd k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11
  have hin : (∑ zz : SS.BitString 6,
      if (SS.PauliString.mk bt000000 zz).wt = 0
        then Complex.normSq (projTrace c d ⟨bt000000, zz⟩) else 0) = 4 := by
    rw [← Finset.sum_subset (Finset.subset_univ Zs0)
        (fun zz _ hzz => by rw [if_neg (zset_0 zz hzz)])]
    simp only [Zs0, Finset.sum_singleton]
    rw [if_pos (by decide : (SS.PauliString.mk bt000000 bt000000).wt = 0), v0]
  rw [AEnum_split]
  have hout : (∑ f : SS.BitString 6, ∑ zz : SS.BitString 6,
      if (SS.PauliString.mk f zz).wt = 0
        then Complex.normSq (projTrace c d ⟨f, zz⟩) else 0)
      = ∑ f ∈ Zs0, ∑ zz : SS.BitString 6,
      if (SS.PauliString.mk f zz).wt = 0
        then Complex.normSq (projTrace c d ⟨f, zz⟩) else 0 := by
    refine (Finset.sum_subset (Finset.subset_univ Zs0) ?_).symm
    intro f _ hf
    refine Finset.sum_eq_zero (fun zz _ => ?_)
    by_cases hw : (SS.PauliString.mk f zz).wt = 0
    · refine absurd (Finset.mem_singleton.mpr (masks0 f ?_)) hf
      have h1 := hammingWt_x_le_wt (SS.PauliString.mk f zz)
      rw [hw] at h1
      exact h1
    · rw [if_neg hw]
  rw [hout]
  simp only [Zs0, Finset.sum_singleton]
  rw [hin]
  norm_num

set_option maxHeartbeats 3200000 in
/-- **`A_2 = 21/25` for every exact orbit-36 solution.** -/
theorem A2_value (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
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
    (ho20 : offSum c d ex56 w0 = 0)
    (ho21 : offSum c d ex16 w0 = 0) :
    AEnum c d 2 = 21/25 := by
  obtain ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11⟩ :=
    magnitudes_forced c d hm ho0 ho1 ho2 ho3 ho4 ho5 ho6 ho7 ho8 ho9 ho10 ho11 ho12 ho13 ho14 ho15 ho16 ho17 ho18 ho19 ho20
  obtain ⟨-, -, n2, n3, n4, n5, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    full_support c d hm ho0 ho1 ho2 ho3 ho4 ho5 ho6 ho7 ho8 ho9 ho10 ho11 ho12 ho13 ho14 ho15 ho16 ho17 ho18 ho19 ho20
  obtain ⟨tau, htf⟩ := top_form c d hm ho0 ho1 ho2 ho3 ho4 ho5 ho6 ho7 ho8 ho9 ho10 ho11 ho12 ho13 ho14 ho15 ho16 ho17 ho18 ho19 ho20 ho21
  obtain ⟨mu, hmu, hp12, hp34, hcol⟩ := phase_rigidity c d hm ho0 ho1 ho2 ho3 ho4 ho5 ho6 ho7 ho8 ho9 ho10 ho11 ho12 ho13 ho14 ho15 ho16 ho17 ho18 ho19 ho20
  have hG : Complex.normSq (star (c y3) * c y2 + star (c y7) * c y9 + star (c y8) * c y10) = 1/900
      ∧ Complex.normSq (star (c y4) * c y2 + star (c y6) * c y9 + star (c y8) * c y11) = 1/900
      ∧ Complex.normSq (star (c y5) * c y2 + star (c y6) * c y10 + star (c y7) * c y11) = 1/900
      ∧ Complex.normSq (star (c y4) * c y3 + star (c y6) * c y7 + star (c y10) * c y11) = 1/900
      ∧ Complex.normSq (star (c y5) * c y3 + star (c y6) * c y8 + star (c y9) * c y11) = 1/900
      ∧ Complex.normSq (star (c y5) * c y4 + star (c y7) * c y8 + star (c y9) * c y10) = 1/900 := by
    rcases hcol with ⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3, b4⟩
    · exact edges_of_colouring rho_quadratic star_rho k2 k3 k4 k5 hmu n2 n3 n4 n5
        hp12 hp34 b1 b2 b3 b4
    · exact edges_of_colouring rho_sq_quadratic star_rho_sq k2 k3 k4 k5 hmu
        n2 n3 n4 n5 hp12 hp34 b1 b2
        (by linear_combination b3 - (rho * mu) * rho_pow_three)
        (by linear_combination b4 - (rho * mu) * rho_pow_three)
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hG
  have g7 : Complex.normSq (star (c y1) * c y0) = 1/100 := by
    rw [map_mul, normSq_star, k1, k0]; norm_num
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15⟩ :=
    diag_values c d hc hd k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11
  obtain ⟨a00, a01, a02, a03⟩ := vals_mk110000 c d hc hd tau htf
  obtain ⟨a10, a11, a12, a13⟩ := vals_mk101000 c d hc hd tau htf
  obtain ⟨a20, a21, a22, a23⟩ := vals_mk100100 c d hc hd tau htf
  obtain ⟨a30, a31, a32, a33⟩ := vals_mk011000 c d hc hd tau htf
  obtain ⟨a40, a41, a42, a43⟩ := vals_mk010100 c d hc hd tau htf
  obtain ⟨a50, a51, a52, a53⟩ := vals_mk001100 c d hc hd tau htf
  obtain ⟨a60, a61, a62, a63⟩ := vals_mk000011 c d hc hd tau htf
  have hin0 : (∑ zz : SS.BitString 6,
      if (SS.PauliString.mk bt000000 zz).wt = 2
        then Complex.normSq (projTrace c d ⟨bt000000, zz⟩) else 0)
      = (36/25) + (4/25) + (4/25) + (4/25) + (4/25) + (4/225) + (4/25) + (4/25) + (4/225) + (4/225) + (4/25) + (4/25) + (4/225) + (4/225) + (4/225) := by
    rw [← Finset.sum_subset (Finset.subset_univ Zsmk000000)
        (fun zz _ hzz => by rw [if_neg (zset_mk000000 zz hzz)])]
    simp only [Zsmk000000]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    rw [if_pos (by decide : (SS.PauliString.mk bt000000 bt000011).wt = 2)]
    rw [if_pos (by decide : (SS.PauliString.mk bt000000 bt000101).wt = 2)]
    rw [if_pos (by decide : (SS.PauliString.mk bt000000 bt000110).wt = 2)]
    rw [if_pos (by decide : (SS.PauliString.mk bt000000 bt001001).wt = 2)]
    rw [if_pos (by decide : (SS.PauliString.mk bt000000 bt001010).wt = 2)]
    rw [if_pos (by decide : (SS.PauliString.mk bt000000 bt001100).wt = 2)]
    rw [if_pos (by decide : (SS.PauliString.mk bt000000 bt010001).wt = 2)]
    rw [if_pos (by decide : (SS.PauliString.mk bt000000 bt010010).wt = 2)]
    rw [if_pos (by decide : (SS.PauliString.mk bt000000 bt010100).wt = 2)]
    rw [if_pos (by decide : (SS.PauliString.mk bt000000 bt011000).wt = 2)]
    rw [if_pos (by decide : (SS.PauliString.mk bt000000 bt100001).wt = 2)]
    rw [if_pos (by decide : (SS.PauliString.mk bt000000 bt100010).wt = 2)]
    rw [if_pos (by decide : (SS.PauliString.mk bt000000 bt100100).wt = 2)]
    rw [if_pos (by decide : (SS.PauliString.mk bt000000 bt101000).wt = 2)]
    rw [if_pos (by decide : (SS.PauliString.mk bt000000 bt110000).wt = 2)]
    rw [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15]
    norm_num
  have hin1 : (∑ zz : SS.BitString 6,
      if (SS.PauliString.mk bt110000 zz).wt = 2
        then Complex.normSq (projTrace c d ⟨bt110000, zz⟩) else 0)
      = 4 * Complex.normSq ((star (c y3) * c y2 + star (c y7) * c y9 + star (c y8) * c y10) + star (star (c y3) * c y2 + star (c y7) * c y9 + star (c y8) * c y10))
        + 4 * Complex.normSq ((star (c y3) * c y2 + star (c y7) * c y9 + star (c y8) * c y10) - star (star (c y3) * c y2 + star (c y7) * c y9 + star (c y8) * c y10))
        + 4 * Complex.normSq ((star (c y3) * c y2 + star (c y7) * c y9 + star (c y8) * c y10) - star (star (c y3) * c y2 + star (c y7) * c y9 + star (c y8) * c y10))
        + 4 * Complex.normSq ((star (c y3) * c y2 + star (c y7) * c y9 + star (c y8) * c y10) + star (star (c y3) * c y2 + star (c y7) * c y9 + star (c y8) * c y10)) := by
    rw [← Finset.sum_subset (Finset.subset_univ Zsmk110000)
        (fun zz _ hzz => by rw [if_neg (zset_mk110000 zz hzz)])]
    simp only [Zsmk110000]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    rw [if_pos (by decide : (SS.PauliString.mk bt110000 bt000000).wt = 2)]
    rw [if_pos (by decide : (SS.PauliString.mk bt110000 bt010000).wt = 2)]
    rw [if_pos (by decide : (SS.PauliString.mk bt110000 bt100000).wt = 2)]
    rw [if_pos (by decide : (SS.PauliString.mk bt110000 bt110000).wt = 2)]
    rw [a00, a01, a02, a03]
    ring
  have hin2 : (∑ zz : SS.BitString 6,
      if (SS.PauliString.mk bt101000 zz).wt = 2
        then Complex.normSq (projTrace c d ⟨bt101000, zz⟩) else 0)
      = 4 * Complex.normSq ((star (c y4) * c y2 + star (c y6) * c y9 + star (c y8) * c y11) + star (star (c y4) * c y2 + star (c y6) * c y9 + star (c y8) * c y11))
        + 4 * Complex.normSq ((star (c y4) * c y2 + star (c y6) * c y9 + star (c y8) * c y11) - star (star (c y4) * c y2 + star (c y6) * c y9 + star (c y8) * c y11))
        + 4 * Complex.normSq ((star (c y4) * c y2 + star (c y6) * c y9 + star (c y8) * c y11) - star (star (c y4) * c y2 + star (c y6) * c y9 + star (c y8) * c y11))
        + 4 * Complex.normSq ((star (c y4) * c y2 + star (c y6) * c y9 + star (c y8) * c y11) + star (star (c y4) * c y2 + star (c y6) * c y9 + star (c y8) * c y11)) := by
    rw [← Finset.sum_subset (Finset.subset_univ Zsmk101000)
        (fun zz _ hzz => by rw [if_neg (zset_mk101000 zz hzz)])]
    simp only [Zsmk101000]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    rw [if_pos (by decide : (SS.PauliString.mk bt101000 bt000000).wt = 2)]
    rw [if_pos (by decide : (SS.PauliString.mk bt101000 bt001000).wt = 2)]
    rw [if_pos (by decide : (SS.PauliString.mk bt101000 bt100000).wt = 2)]
    rw [if_pos (by decide : (SS.PauliString.mk bt101000 bt101000).wt = 2)]
    rw [a10, a11, a12, a13]
    ring
  have hin3 : (∑ zz : SS.BitString 6,
      if (SS.PauliString.mk bt100100 zz).wt = 2
        then Complex.normSq (projTrace c d ⟨bt100100, zz⟩) else 0)
      = 4 * Complex.normSq ((star (c y5) * c y2 + star (c y6) * c y10 + star (c y7) * c y11) + star (star (c y5) * c y2 + star (c y6) * c y10 + star (c y7) * c y11))
        + 4 * Complex.normSq ((star (c y5) * c y2 + star (c y6) * c y10 + star (c y7) * c y11) - star (star (c y5) * c y2 + star (c y6) * c y10 + star (c y7) * c y11))
        + 4 * Complex.normSq ((star (c y5) * c y2 + star (c y6) * c y10 + star (c y7) * c y11) - star (star (c y5) * c y2 + star (c y6) * c y10 + star (c y7) * c y11))
        + 4 * Complex.normSq ((star (c y5) * c y2 + star (c y6) * c y10 + star (c y7) * c y11) + star (star (c y5) * c y2 + star (c y6) * c y10 + star (c y7) * c y11)) := by
    rw [← Finset.sum_subset (Finset.subset_univ Zsmk100100)
        (fun zz _ hzz => by rw [if_neg (zset_mk100100 zz hzz)])]
    simp only [Zsmk100100]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    rw [if_pos (by decide : (SS.PauliString.mk bt100100 bt000000).wt = 2)]
    rw [if_pos (by decide : (SS.PauliString.mk bt100100 bt000100).wt = 2)]
    rw [if_pos (by decide : (SS.PauliString.mk bt100100 bt100000).wt = 2)]
    rw [if_pos (by decide : (SS.PauliString.mk bt100100 bt100100).wt = 2)]
    rw [a20, a21, a22, a23]
    ring
  have hin4 : (∑ zz : SS.BitString 6,
      if (SS.PauliString.mk bt011000 zz).wt = 2
        then Complex.normSq (projTrace c d ⟨bt011000, zz⟩) else 0)
      = 4 * Complex.normSq ((star (c y4) * c y3 + star (c y6) * c y7 + star (c y10) * c y11) + star (star (c y4) * c y3 + star (c y6) * c y7 + star (c y10) * c y11))
        + 4 * Complex.normSq ((star (c y4) * c y3 + star (c y6) * c y7 + star (c y10) * c y11) - star (star (c y4) * c y3 + star (c y6) * c y7 + star (c y10) * c y11))
        + 4 * Complex.normSq ((star (c y4) * c y3 + star (c y6) * c y7 + star (c y10) * c y11) - star (star (c y4) * c y3 + star (c y6) * c y7 + star (c y10) * c y11))
        + 4 * Complex.normSq ((star (c y4) * c y3 + star (c y6) * c y7 + star (c y10) * c y11) + star (star (c y4) * c y3 + star (c y6) * c y7 + star (c y10) * c y11)) := by
    rw [← Finset.sum_subset (Finset.subset_univ Zsmk011000)
        (fun zz _ hzz => by rw [if_neg (zset_mk011000 zz hzz)])]
    simp only [Zsmk011000]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    rw [if_pos (by decide : (SS.PauliString.mk bt011000 bt000000).wt = 2)]
    rw [if_pos (by decide : (SS.PauliString.mk bt011000 bt001000).wt = 2)]
    rw [if_pos (by decide : (SS.PauliString.mk bt011000 bt010000).wt = 2)]
    rw [if_pos (by decide : (SS.PauliString.mk bt011000 bt011000).wt = 2)]
    rw [a30, a31, a32, a33]
    ring
  have hin5 : (∑ zz : SS.BitString 6,
      if (SS.PauliString.mk bt010100 zz).wt = 2
        then Complex.normSq (projTrace c d ⟨bt010100, zz⟩) else 0)
      = 4 * Complex.normSq ((star (c y5) * c y3 + star (c y6) * c y8 + star (c y9) * c y11) + star (star (c y5) * c y3 + star (c y6) * c y8 + star (c y9) * c y11))
        + 4 * Complex.normSq ((star (c y5) * c y3 + star (c y6) * c y8 + star (c y9) * c y11) - star (star (c y5) * c y3 + star (c y6) * c y8 + star (c y9) * c y11))
        + 4 * Complex.normSq ((star (c y5) * c y3 + star (c y6) * c y8 + star (c y9) * c y11) - star (star (c y5) * c y3 + star (c y6) * c y8 + star (c y9) * c y11))
        + 4 * Complex.normSq ((star (c y5) * c y3 + star (c y6) * c y8 + star (c y9) * c y11) + star (star (c y5) * c y3 + star (c y6) * c y8 + star (c y9) * c y11)) := by
    rw [← Finset.sum_subset (Finset.subset_univ Zsmk010100)
        (fun zz _ hzz => by rw [if_neg (zset_mk010100 zz hzz)])]
    simp only [Zsmk010100]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    rw [if_pos (by decide : (SS.PauliString.mk bt010100 bt000000).wt = 2)]
    rw [if_pos (by decide : (SS.PauliString.mk bt010100 bt000100).wt = 2)]
    rw [if_pos (by decide : (SS.PauliString.mk bt010100 bt010000).wt = 2)]
    rw [if_pos (by decide : (SS.PauliString.mk bt010100 bt010100).wt = 2)]
    rw [a40, a41, a42, a43]
    ring
  have hin6 : (∑ zz : SS.BitString 6,
      if (SS.PauliString.mk bt001100 zz).wt = 2
        then Complex.normSq (projTrace c d ⟨bt001100, zz⟩) else 0)
      = 4 * Complex.normSq ((star (c y5) * c y4 + star (c y7) * c y8 + star (c y9) * c y10) + star (star (c y5) * c y4 + star (c y7) * c y8 + star (c y9) * c y10))
        + 4 * Complex.normSq ((star (c y5) * c y4 + star (c y7) * c y8 + star (c y9) * c y10) - star (star (c y5) * c y4 + star (c y7) * c y8 + star (c y9) * c y10))
        + 4 * Complex.normSq ((star (c y5) * c y4 + star (c y7) * c y8 + star (c y9) * c y10) - star (star (c y5) * c y4 + star (c y7) * c y8 + star (c y9) * c y10))
        + 4 * Complex.normSq ((star (c y5) * c y4 + star (c y7) * c y8 + star (c y9) * c y10) + star (star (c y5) * c y4 + star (c y7) * c y8 + star (c y9) * c y10)) := by
    rw [← Finset.sum_subset (Finset.subset_univ Zsmk001100)
        (fun zz _ hzz => by rw [if_neg (zset_mk001100 zz hzz)])]
    simp only [Zsmk001100]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    rw [if_pos (by decide : (SS.PauliString.mk bt001100 bt000000).wt = 2)]
    rw [if_pos (by decide : (SS.PauliString.mk bt001100 bt000100).wt = 2)]
    rw [if_pos (by decide : (SS.PauliString.mk bt001100 bt001000).wt = 2)]
    rw [if_pos (by decide : (SS.PauliString.mk bt001100 bt001100).wt = 2)]
    rw [a50, a51, a52, a53]
    ring
  have hin7 : (∑ zz : SS.BitString 6,
      if (SS.PauliString.mk bt000011 zz).wt = 2
        then Complex.normSq (projTrace c d ⟨bt000011, zz⟩) else 0)
      = 4 * Complex.normSq ((star (c y1) * c y0) + star (star (c y1) * c y0))
        + 4 * Complex.normSq ((star (c y1) * c y0) - star (star (c y1) * c y0))
        + 4 * Complex.normSq ((star (c y1) * c y0) - star (star (c y1) * c y0))
        + 4 * Complex.normSq ((star (c y1) * c y0) + star (star (c y1) * c y0)) := by
    rw [← Finset.sum_subset (Finset.subset_univ Zsmk000011)
        (fun zz _ hzz => by rw [if_neg (zset_mk000011 zz hzz)])]
    simp only [Zsmk000011]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    rw [if_pos (by decide : (SS.PauliString.mk bt000011 bt000000).wt = 2)]
    rw [if_pos (by decide : (SS.PauliString.mk bt000011 bt000001).wt = 2)]
    rw [if_pos (by decide : (SS.PauliString.mk bt000011 bt000010).wt = 2)]
    rw [if_pos (by decide : (SS.PauliString.mk bt000011 bt000011).wt = 2)]
    rw [a60, a61, a62, a63]
    ring
  rw [AEnum_split]
  have hout : (∑ f : SS.BitString 6, ∑ zz : SS.BitString 6,
      if (SS.PauliString.mk f zz).wt = 2
        then Complex.normSq (projTrace c d ⟨f, zz⟩) else 0)
      = ∑ f ∈ gm2, ∑ zz : SS.BitString 6,
      if (SS.PauliString.mk f zz).wt = 2
        then Complex.normSq (projTrace c d ⟨f, zz⟩) else 0 := by
    refine (Finset.sum_subset (Finset.subset_univ gm2) ?_).symm
    intro f _ hf
    refine Finset.sum_eq_zero (fun zz _ => ?_)
    by_cases hw : (SS.PauliString.mk f zz).wt = 2
    · rw [if_pos hw]
      obtain ⟨e0, e1⟩ := (masks2 f (by
        have h1 := hammingWt_x_le_wt (SS.PauliString.mk f zz)
        rw [hw] at h1
        exact h1)).resolve_left hf
      rw [projTrace_no_incidence hc hd e0 e1, Complex.normSq_zero]
    · rw [if_neg hw]
  rw [hout]
  simp only [gm2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [hin0, hin1, hin2, hin3, hin4, hin5, hin6, hin7]
  have s0 := normSq_split (star (c y3) * c y2 + star (c y7) * c y9 + star (c y8) * c y10)
  have s1 := normSq_split (star (c y4) * c y2 + star (c y6) * c y9 + star (c y8) * c y11)
  have s2 := normSq_split (star (c y5) * c y2 + star (c y6) * c y10 + star (c y7) * c y11)
  have s3 := normSq_split (star (c y4) * c y3 + star (c y6) * c y7 + star (c y10) * c y11)
  have s4 := normSq_split (star (c y5) * c y3 + star (c y6) * c y8 + star (c y9) * c y11)
  have s5 := normSq_split (star (c y5) * c y4 + star (c y7) * c y8 + star (c y9) * c y10)
  have s6 := normSq_split (star (c y1) * c y0)
  linarith [s0, s1, s2, s3, s4, s5, s6, g1, g2, g3, g4, g5, g6, g7]

set_option maxHeartbeats 3200000 in
/-- **`A_3 = 0` for every exact orbit-36 solution.** -/
theorem A3_value (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
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
    (ho20 : offSum c d ex56 w0 = 0)
    (ho21 : offSum c d ex16 w0 = 0) :
    AEnum c d 3 = 0 := by
  obtain ⟨-, -, k2, k3, k4, k5, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    magnitudes_forced c d hm ho0 ho1 ho2 ho3 ho4 ho5 ho6 ho7 ho8 ho9 ho10 ho11 ho12 ho13 ho14 ho15 ho16 ho17 ho18 ho19 ho20
  obtain ⟨-, -, n2, n3, n4, n5, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    full_support c d hm ho0 ho1 ho2 ho3 ho4 ho5 ho6 ho7 ho8 ho9 ho10 ho11 ho12 ho13 ho14 ho15 ho16 ho17 ho18 ho19 ho20
  obtain ⟨tau, htf⟩ := top_form c d hm ho0 ho1 ho2 ho3 ho4 ho5 ho6 ho7 ho8 ho9 ho10 ho11 ho12 ho13 ho14 ho15 ho16 ho17 ho18 ho19 ho20 ho21
  obtain ⟨mu, -, hp12, hp34, hcol⟩ := phase_rigidity c d hm ho0 ho1 ho2 ho3 ho4 ho5 ho6 ho7 ho8 ho9 ho10 ho11 ho12 ho13 ho14 ho15 ho16 ho17 ho18 ho19 ho20
  have htri : star (c y2) * c y9 + star (c y3) * c y7 + star (c y4) * c y6 = 0
      ∧ star (c y2) * c y10 + star (c y3) * c y8 + star (c y5) * c y6 = 0
      ∧ star (c y2) * c y11 + star (c y4) * c y8 + star (c y5) * c y7 = 0
      ∧ star (c y3) * c y11 + star (c y4) * c y10 + star (c y5) * c y9 = 0 := by
    rcases hcol with ⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3, b4⟩
    · refine ⟨?_, ?_, ?_, ?_⟩
      · linear_combination triangle_sum (r2 := c y4) (r3 := c y3)
          (r4 := c y2) (c34 := c y6) (c24 := c y7) (c23 := c y9)
          (mu := mu) k4 k3 k2
          (by linear_combination hp12) (by linear_combination b1)
          (by linear_combination b4) n4 n3 n2
      · linear_combination triangle_sum (r2 := c y5) (r3 := c y2)
          (r4 := c y3) (c34 := c y6) (c24 := c y10) (c23 := c y8)
          (mu := mu) k5 k2 k3
          (by linear_combination hp12) (by linear_combination b2)
          (by linear_combination b3) n5 n2 n3
      · linear_combination triangle_sum (r2 := c y2) (r3 := c y5)
          (r4 := c y4) (c34 := c y11) (c24 := c y7) (c23 := c y8)
          (mu := mu) k2 k5 k4
          (by linear_combination hp34) (by linear_combination b1)
          (by linear_combination b3) n2 n5 n4
      · linear_combination triangle_sum (r2 := c y3) (r3 := c y4)
          (r4 := c y5) (c34 := c y11) (c24 := c y10) (c23 := c y9)
          (mu := mu) k3 k4 k5
          (by linear_combination hp34) (by linear_combination b2)
          (by linear_combination b4) n3 n4 n5
    · refine ⟨?_, ?_, ?_, ?_⟩
      · linear_combination triangle_sum (r2 := c y4) (r3 := c y2)
          (r4 := c y3) (c34 := c y6) (c24 := c y9) (c23 := c y7)
          (mu := mu) k4 k2 k3
          (by linear_combination hp12) (by linear_combination b4)
          (by linear_combination b1) n4 n2 n3
      · linear_combination triangle_sum (r2 := c y5) (r3 := c y3)
          (r4 := c y2) (c34 := c y6) (c24 := c y8) (c23 := c y10)
          (mu := mu) k5 k3 k2
          (by linear_combination hp12) (by linear_combination b3)
          (by linear_combination b2) n5 n3 n2
      · linear_combination triangle_sum (r2 := c y2) (r3 := c y4)
          (r4 := c y5) (c34 := c y11) (c24 := c y8) (c23 := c y7)
          (mu := mu) k2 k4 k5
          (by linear_combination hp34) (by linear_combination b3)
          (by linear_combination b1) n2 n4 n5
      · linear_combination triangle_sum (r2 := c y3) (r3 := c y5)
          (r4 := c y4) (c34 := c y11) (c24 := c y9) (c23 := c y10)
          (mu := mu) k3 k5 k4
          (by linear_combination hp34) (by linear_combination b4)
          (by linear_combination b2) n3 n5 n4
  obtain ⟨tr0, tr1, tr2, tr3⟩ := htri
  refine AEnum_eq_zero ?_
  rintro ⟨xx, zz⟩ hP
  have hle : SS.hammingWt xx ≤ 3 := by
    have h1 := hammingWt_x_le_wt (SS.PauliString.mk xx zz)
    rw [hP] at h1
    exact h1
  rcases masks3 xx hle with hin | ⟨e0, e1⟩
  · simp only [gm3, Finset.mem_insert, Finset.mem_singleton] at hin
    rcases hin with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst h
      exact a3_mk000000 c d hc hd tau htf zz hP
    · subst h
      exact a3_mk110000 c d hc hd tau htf zz hP
    · subst h
      exact a3_mk101000 c d hc hd tau htf zz hP
    · subst h
      exact a3_mk100100 c d hc hd tau htf zz hP
    · subst h
      exact a3_mk011000 c d hc hd tau htf zz hP
    · subst h
      exact a3_mk010100 c d hc hd tau htf zz hP
    · subst h
      exact a3_mk001100 c d hc hd tau htf zz hP
    · subst h
      exact a3_mk000011 c d hc hd tau htf zz hP
    · subst h
      exact a3_mk001101 c d hc hd tau htf zz hP
    · subst h
      exact a3_mk001110 c d hc hd tau htf zz hP
    · subst h
      exact a3_mk010101 c d hc hd tau htf zz hP
    · subst h
      exact a3_mk010110 c d hc hd tau htf zz hP
    · subst h
      exact a3_mk011001 c d hc hd tau htf zz hP
    · subst h
      exact a3_mk011010 c d hc hd tau htf zz hP
    · subst h
      exact a3_mk100101 c d hc hd tau htf zz hP
    · subst h
      exact a3_mk100110 c d hc hd tau htf zz hP
    · subst h
      exact a3_mk101001 c d hc hd tau htf zz hP
    · subst h
      exact a3_mk101010 c d hc hd tau htf zz hP
    · subst h
      exact a3_mk110001 c d hc hd tau htf zz hP
    · subst h
      exact a3_mk110010 c d hc hd tau htf zz hP
    · subst h
      exact a3_mk000111 c d hc hd tau htf tr0 zz hP
    · subst h
      exact a3_mk001011 c d hc hd tau htf tr1 zz hP
    · subst h
      exact a3_mk010011 c d hc hd tau htf tr2 zz hP
    · subst h
      exact a3_mk100011 c d hc hd tau htf tr3 zz hP
  · exact projTrace_no_incidence hc hd e0 e1

/-! ## 12.  The unique enumerator -/

set_option maxHeartbeats 3200000 in
/-- **The unique Shor--Laflamme weight enumerator on orbit 36.**

The first four coefficients are *derived*: the only inputs are the two support
conditions, one `MomentSystem`, and twenty-two vanishing Knill--Laflamme rows.
The remaining three are read off from the quantum MacWilliams normal form of a
`((6,2,3))` code, which enters as the three displayed hypotheses `hmw4, hmw5,
`hmw6` -- exactly Eq. (o36MacWilliamsnormalform) of the chapter.  That relation
holds for every `((6,2,3))` code and is *not* proved here. -/
theorem unique_enumerator (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
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
    (ho20 : offSum c d ex56 w0 = 0)
    (ho21 : offSum c d ex16 w0 = 0)
    (A4 A5 A6 : ℝ)
    (hmw4 : A4 = 15 - 4 * AEnum c d 2 - 3 * AEnum c d 3)
    (hmw5 : A5 = 12 + 3 * AEnum c d 1 + 4 * AEnum c d 2 + 3 * AEnum c d 3)
    (hmw6 : A6 = 4 - 4 * AEnum c d 1 - AEnum c d 2 - AEnum c d 3) :
    AEnum c d 0 = 1 ∧ AEnum c d 1 = 0 ∧ AEnum c d 2 = 21/25 ∧ AEnum c d 3 = 0
      ∧ A4 = 291/25 ∧ A5 = 384/25 ∧ A6 = 79/25 := by
  have h0 : AEnum c d 0 = 1 := A0_value c d hc hd hm ho0 ho1 ho2 ho3 ho4 ho5 ho6 ho7 ho8 ho9 ho10 ho11 ho12 ho13 ho14 ho15 ho16 ho17 ho18 ho19 ho20
  have h1 : AEnum c d 1 = 0 := A1_eq_zero c d hc hd hm
  have h2 : AEnum c d 2 = 21/25 := A2_value c d hc hd hm ho0 ho1 ho2 ho3 ho4 ho5 ho6 ho7 ho8 ho9 ho10 ho11 ho12 ho13 ho14 ho15 ho16 ho17 ho18 ho19 ho20 ho21
  have h3 : AEnum c d 3 = 0 := A3_value c d hc hd hm ho0 ho1 ho2 ho3 ho4 ho5 ho6 ho7 ho8 ho9 ho10 ho11 ho12 ho13 ho14 ho15 ho16 ho17 ho18 ho19 ho20 ho21
  refine ⟨h0, h1, h2, h3, ?_, ?_, ?_⟩
  · rw [hmw4, h2, h3]; norm_num
  · rw [hmw5, h1, h2, h3]; norm_num
  · rw [hmw6, h1, h2, h3]; norm_num

/-- The same closure performed over `ℚ` by
`Orbit36Phase.macwilliams_normal_form`, which is the shape the chapter states. -/
theorem unique_enumerator_rat :
    (1 : ℚ) = 1 ∧ (0 : ℚ) = 0 ∧ (21/25 : ℚ) = 21/25 ∧ (0 : ℚ) = 0
      ∧ (15 - 4 * (21/25 : ℚ) - 3 * 0 : ℚ) = 291/25
      ∧ (12 + 3 * (0 : ℚ) + 4 * (21/25) + 3 * 0 : ℚ) = 384/25
      ∧ (4 - 4 * (0 : ℚ) - 21/25 - 0 : ℚ) = 79/25 :=
  macwilliams_normal_form 1 0 (21/25) 0 (15 - 4 * (21/25) - 3 * 0)
    (12 + 3 * 0 + 4 * (21/25) + 3 * 0) (4 - 4 * 0 - 21/25 - 0)
    rfl rfl rfl rfl rfl rfl rfl

end

end SixQubit.Orbit36Enum
