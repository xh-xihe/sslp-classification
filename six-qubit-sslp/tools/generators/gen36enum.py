#!/usr/bin/env python3
"""Generate `SixQubit/Orbit36Enum.lean`: the unique Shor--Laflamme weight
enumerator of the order-five moment orbit 36.

The chapter is `documents/20260821/supplementary.tex`, subsection
"The unique weight enumerator on orbit 36" (line 1006).

Everything combinatorial (fiber incidences, Walsh signs, flip masks) is computed
here from the fiber `S_0` of `a* = (1,1,1,1,2,3)` and emitted as `by decide`
facts, so the Lean file never re-derives it.

Bit order: index `i` of a `SS.BitString 6` is the paper's qubit `i+1`.
"""

import io
import os
from fractions import Fraction
from itertools import product

# ----------------------------------------------------------------------------
# combinatorial data
# ----------------------------------------------------------------------------

PTS = {
    0: ("u", "000000"), 1: ("v", "000011"),
    2: ("s1", "011110"), 3: ("s2", "101110"),
    4: ("s3", "110110"), 5: ("s4", "111010"),
    6: ("e12", "110001"), 7: ("e13", "101001"), 8: ("e14", "100101"),
    9: ("e23", "011001"), 10: ("e24", "010101"), 11: ("e34", "001101"),
}


def bits(s):
    return tuple(int(ch) for ch in s)


def comp(t):
    return tuple(1 - x for x in t)


def xor(a, b):
    return tuple(x ^ y for x, y in zip(a, b))


def dot(a, b):
    return sum(x * y for x, y in zip(a, b)) % 2


def pwt(f, z):
    return sum(1 for i in range(6) if f[i] or z[i])


S0 = {k: bits(v[1]) for k, v in PTS.items()}
S1 = {k: comp(t) for k, t in S0.items()}
INV0 = {v: k for k, v in S0.items()}

ALL = list(product([0, 1], repeat=6))


def pairs_of(f):
    return sorted({tuple(sorted((k, INV0[xor(S0[k], f)])))
                   for k in S0 if xor(S0[k], f) in INV0})


M0 = (0, 0, 0, 0, 0, 0)
MASK45 = (0, 0, 0, 0, 1, 1)

EDGE_MASKS = []
for _i, _j in [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]:
    _f = tuple(1 if k in (_i, _j) else 0 for k in range(6))
    _V, _W = _i + 1, _j + 1
    _K, _L = sorted(set([1, 2, 3, 4]) - {_V, _W})
    EDGE_MASKS.append((_f, _V, _W, _K, _L))

W3_AB, W3_C = [], []
for _f in ALL:
    if sum(_f) != 3:
        continue
    _pr = pairs_of(_f)
    if not _pr:
        continue
    (W3_AB if len(_pr) == 1 else W3_C).append((_f, _pr))

PROB = {k: (Fraction(1, 10) if k < 6 else Fraction(1, 15)) for k in range(12)}

VERTY = {1: 2, 2: 3, 3: 4, 4: 5}
EDGEY = {(1, 2): 6, (1, 3): 7, (1, 4): 8, (2, 3): 9, (2, 4): 10, (3, 4): 11}


def blit(t):
    return "bs " + " ".join(("true" if x else "false") for x in t)


def bname(t):
    return "bt" + "".join(str(x) for x in t)


def mnm(t):
    return "mk" + "".join(str(x) for x in t)


def frac(v):
    v = Fraction(v)
    if v.denominator == 1:
        return str(v.numerator)
    if v.numerator < 0:
        return "-({}/{})".format(-v.numerator, v.denominator)
    return "{}/{}".format(v.numerator, v.denominator)


# ----------------------------------------------------------------------------
# emission helpers
# ----------------------------------------------------------------------------

OUT = []


def w(s=""):
    OUT.append(s)


def chain(n):
    if n == 1:
        return "Finset.sum_singleton"
    return ", ".join(["Finset.sum_insert (by decide)"] * (n - 1) + ["Finset.sum_singleton"])


def signsimp(vals):
    names = []
    if any(not v for v in vals):
        names.append("SS.signC_false")
    if any(v for v in vals):
        names.append("SS.signC_true")
    return names


EMITTED_SIGN = set()


def sign_lemma(z, k, top):
    nm = "sg{}_{}_{}".format("T" if top else "B", "".join(str(x) for x in z), k)
    if nm not in EMITTED_SIGN:
        EMITTED_SIGN.add(nm)
        val = dot(z, S1[k] if top else S0[k])
        w("theorem {} : SS.bdot {} {}{} = {} := by decide".format(
            nm, bname(z), "z" if top else "y", k, "true" if val else "false"))
    return nm


MOMENT_HYP = """    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5))
            (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5))
            (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)))"""

ROWS = [
    ("ho0", "ex1 w0"), ("ho1", "ex1 w2"), ("ho2", "ex1 w3"), ("ho3", "ex1 w4"),
    ("ho4", "ex2 w0"), ("ho5", "ex2 w1"), ("ho6", "ex2 w3"), ("ho7", "ex2 w4"),
    ("ho8", "ex3 w0"), ("ho9", "ex3 w1"), ("ho10", "ex3 w2"), ("ho11", "ex3 w4"),
    ("ho12", "ex4 w0"), ("ho13", "ex4 w1"), ("ho14", "ex4 w2"), ("ho15", "ex4 w3"),
    ("ho16", "ex15 w0"), ("ho17", "ex25 w0"), ("ho18", "ex35 w0"), ("ho19", "ex45 w0"),
    ("ho20", "ex56 w0"),
]
ROWS_HYP = "\n".join("    ({} : offSum c d {} = 0)".format(n, a) for n, a in ROWS)
ROWS_ARGS = " ".join(n for n, _ in ROWS)
EX16_HYP = "    (ho21 : offSum c d ex16 w0 = 0)"
SUPPORT_HYP = "    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)"


# ----------------------------------------------------------------------------
# header + hand-written lemmas
# ----------------------------------------------------------------------------

HEADER = r"""import Mathlib

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
"""

HELPERS = r"""
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
"""


def emit_colouring():
    rs = {1: "r1", 2: "r2", 3: "r3", 4: "r4"}
    cs = {(1, 2): "c12", (1, 3): "c13", (1, 4): "c14",
          (2, 3): "c23", (2, 4): "c24", (3, 4): "c34"}

    def cn(a, b):
        return cs[tuple(sorted((a, b)))]

    colour = {(1, 2): 0, (3, 4): 0, (1, 3): 1, (2, 4): 1, (1, 4): 2, (2, 3): 2}
    colexpr = {0: "mu", 1: "w * mu", 2: "w ^ 2 * mu"}
    hname = {(1, 2): "h12", (3, 4): "h34", (1, 3): "h13", (2, 4): "h24",
             (1, 4): "h14", (2, 3): "h23"}

    w("/-! ## 4.  The six weight-two moduli, from the edge colouring -/")
    w()
    w("/-- **Every `K_4` edge mask has `normSq G = 1/900`.**  Stated for an abstract")
    w("primitive cube root `w`, so that it applies verbatim to both branches of the")
    w("colouring disjunction of `Orbit36Phase.phase_rigidity`. -/")
    w("theorem edges_of_colouring {r1 r2 r3 r4 c12 c13 c14 c23 c24 c34 mu w : ℂ}")
    w("    (hw : w ^ 2 + w + 1 = 0) (hs : star w = w ^ 2)")
    w("    (p1 : Complex.normSq r1 = 1/10) (p2 : Complex.normSq r2 = 1/10)")
    w("    (p3 : Complex.normSq r3 = 1/10) (p4 : Complex.normSq r4 = 1/10)")
    w("    (hmu : Complex.normSq mu = 1/1500)")
    w("    (n1 : r1 ≠ 0) (n2 : r2 ≠ 0) (n3 : r3 ≠ 0) (n4 : r4 ≠ 0)")
    w("    (h12 : r1 * r2 * c12 = mu) (h34 : r3 * r4 * c34 = mu)")
    w("    (h13 : r1 * r3 * c13 = w * mu) (h24 : r2 * r4 * c24 = w * mu)")
    w("    (h14 : r1 * r4 * c14 = w ^ 2 * mu) (h23 : r2 * r3 * c23 = w ^ 2 * mu) :")
    concl = ["Complex.normSq (star {} * {} + star {} * {} + star {} * {}) = 1/900".format(
        rs[W_], rs[V], cn(V, K), cn(W_, K), cn(V, L), cn(W_, L))
        for (f, V, W_, K, L) in EDGE_MASKS]
    w("    " + ("\n      ∧ ".join(concl)) + " := by")
    w("  refine ⟨" + ", ".join(["?_"] * 6) + "⟩")
    for (f, V, W_, K, L) in EDGE_MASKS:
        mVK = "{} * {} * {}".format(rs[V], rs[K], cn(V, K))
        mWK = "{} * {} * {}".format(rs[W_], rs[K], cn(W_, K))
        mVL = "{} * {} * {}".format(rs[V], rs[L], cn(V, L))
        mWL = "{} * {} * {}".format(rs[W_], rs[L], cn(W_, L))
        cVK = colour[tuple(sorted((V, K)))]
        cWK = colour[tuple(sorted((W_, K)))]
        cVL = colour[tuple(sorted((V, L)))]
        cWL = colour[tuple(sorted((W_, L)))]
        assert cVK == cWL and cWK == cVL and cVK != cWK
        pairname = "colourPair_" + "".join(str(x) for x in sorted((cVK, cWK)))
        w("  · have hVK : {} = {} := by linear_combination {}".format(
            mVK, colexpr[cVK], hname[tuple(sorted((V, K)))]))
        w("    have hWK : {} = {} := by linear_combination {}".format(
            mWK, colexpr[cWK], hname[tuple(sorted((W_, K)))]))
        w("    have hVL : {} = {} := by linear_combination {}".format(
            mVL, colexpr[cVL], hname[tuple(sorted((V, L)))]))
        w("    have hWL : {} = {} := by linear_combination {}".format(
            mWL, colexpr[cWL], hname[tuple(sorted((W_, L)))]))
        w("    have hcross : star ({}) * ({}) + star ({}) * ({}) = -(1/1500 : ℂ) := by".format(
            mVK, mWK, mVL, mWL))
        w("      rw [hVK, hWK, hVL, hWL, {} hw hs, SixQubit.star_mul_self, hmu]".format(pairname))
        w("      norm_num")
        w("    refine normSq_of_triple (edge_G p{} p{} p{} p{} hcross n{} n{}) ?_".format(
            V, W_, K, L, V, W_))
        w("    rw [map_mul, normSq_star, p{}, p{}]".format(W_, V))
        w("    norm_num")
    w()


# ----------------------------------------------------------------------------
# bitstring literals
# ----------------------------------------------------------------------------

ZSETS = {}


def emit_bits():
    used = set([M0, MASK45])
    for (f, V, W_, K, L) in EDGE_MASKS:
        used.add(f)
    for f, _ in W3_AB + W3_C:
        used.add(f)
    for f in [M0] + [m[0] for m in EDGE_MASKS] + [MASK45]:
        zs = sorted([z for z in ALL if pwt(f, z) == 2])
        ZSETS[f] = zs
        used.update(zs)
    w("/-! ## 5.  The flip masks and dressings that occur -/")
    w()
    for t in sorted(used):
        w("def {} : SS.BitString 6 := {}".format(bname(t), blit(t)))
    w()


# ----------------------------------------------------------------------------
# the X_1 X_6 row and the antiunitary normal form
# ----------------------------------------------------------------------------

def emit_topform():
    w("/-! ## 6.  The `X_1 X_6` row and the antiunitary normal form -/")
    w()
    w("/-- The flip mask of `X_1 X_6`.  This is the one Knill--Laflamme row beyond the")
    w("twenty-one of `Orbit36.magnitudes_forced` that the enumerator needs: it ties the")
    w("top anchor `A` to the bottom anchor `a`. -/")
    w("def ex16 : SS.BitString 6 := bs true false false false false true")
    w()
    w("theorem inc_ex16 : S1.filter (fun y => SS.bxor y ex16 ∈ S0) = {z0, z2} := by decide")
    w("theorem flip_ex16_0 : SS.bxor z0 ex16 = y2 := by decide")
    w("theorem flip_ex16_2 : SS.bxor z2 ex16 = y0 := by decide")
    w("theorem sg_ex16_w0_0 : SS.bdot w0 z0 = false := by decide")
    w("theorem sg_ex16_w0_2 : SS.bdot w0 z2 = false := by decide")
    w()
    w("theorem ex_ex16_w0 (c d : SS.BitString 6 -> ℂ) :")
    w("    offSum c d ex16 w0 = star (c y2) * d z0 + star (c y0) * d z2 := by")
    w("  unfold offSum")
    w("  rw [inc_ex16]")
    w("  rw [Finset.sum_insert (by decide), Finset.sum_singleton]")
    w("  rw [flip_ex16_0, flip_ex16_2]")
    w("  simp only [sg_ex16_w0_0, sg_ex16_w0_2, SixQubit.signMul_false]")
    w()
    w("/-- **The antiunitary normal form.**  A single unit phase `tau` relates every top")
    w("amplitude to the conjugate of the corresponding bottom amplitude, with a minus")
    w("sign on the four vertex and six edge amplitudes and a plus sign on the two")
    w("last-coordinate anchors.  This is `|1_L> = Z_5 Z_6 X^{(x)6} K |0_L>` up to the")
    w("logical basis phase `tau`. -/")
    w("structure TopForm (c d : SS.BitString 6 -> ℂ) (tau : ℂ) : Prop where")
    w("  unit : star tau * tau = 1")
    for k in range(12):
        rhs = ("tau * star (c y{})".format(k) if k < 2
               else "-(tau * star (c y{}))".format(k))
        w("  t{} : d z{} = {}".format(k, k, rhs))
    w()
    w("set_option maxHeartbeats 1600000 in")
    w("/-- **Every exact orbit-36 solution is in antiunitary normal form.**  The four")
    w("`X_i X_5` rows produce `tau` and the four vertex relations, the `X_1 X_6` row")
    w("propagates it to the anchor `a`, and the `X_i Z_j` pair relations propagate it to")
    w("the six edges. -/")
    w("theorem top_form (c d : SS.BitString 6 -> ℂ)")
    w(MOMENT_HYP)
    w(ROWS_HYP)
    w(EX16_HYP + " :")
    w("    ∃ tau : ℂ, TopForm c d tau := by")
    w("  obtain ⟨-, k1, -, -, -, -, -, -, -, -, -, -, -, l1, -, -, -, -, -, -, -, -, -, -⟩ :=")
    w("    magnitudes_forced c d hm " + ROWS_ARGS)
    w("  obtain ⟨-, n1, n2, n3, n4, n5, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=")
    w("    full_support c d hm " + ROWS_ARGS)
    for n, a in ROWS[:20]:
        w("  rw [ex_{}] at {}".format(a.replace(" ", "_"), n))
    w("  rw [ex_ex16_w0] at ho21")
    w("  obtain ⟨q1, q2, q3, -⟩ :=")
    w("    SixQubit.K4Kernel.starSum_of_dressings (c1 := c y6) (c2 := c y7)")
    w("      (c3 := c y8) (r1 := c y3) (r2 := c y4) (r3 := c y5) (R1 := d z3)")
    w("      (R2 := d z4) (R3 := d z5) (C1 := d z6) (C2 := d z7) (C3 := d z8)")
    w("      (by linear_combination ho0) (by linear_combination ho1)")
    w("      (by linear_combination ho2) (by linear_combination ho3)")
    w("  obtain ⟨-, q4, q5, -⟩ :=")
    w("    SixQubit.K4Kernel.starSum_of_dressings (c1 := c y6) (c2 := c y9)")
    w("      (c3 := c y10) (r1 := c y2) (r2 := c y4) (r3 := c y5) (R1 := d z2)")
    w("      (R2 := d z4) (R3 := d z5) (C1 := d z6) (C2 := d z9) (C3 := d z10)")
    w("      (by linear_combination ho4) (by linear_combination ho5)")
    w("      (by linear_combination ho6) (by linear_combination ho7)")
    w("  obtain ⟨-, -, q6, -⟩ :=")
    w("    SixQubit.K4Kernel.starSum_of_dressings (c1 := c y7) (c2 := c y9)")
    w("      (c3 := c y11) (r1 := c y2) (r2 := c y3) (r3 := c y5) (R1 := d z2)")
    w("      (R2 := d z3) (R3 := d z5) (C1 := d z7) (C2 := d z9) (C3 := d z11)")
    w("      (by linear_combination ho8) (by linear_combination ho9)")
    w("      (by linear_combination ho10) (by linear_combination ho11)")
    for k in range(1, 6):
        w("  have s{} : star (c y{}) ≠ 0 := star_ne_zero.mpr n{}".format(k, k, k))
    w("  obtain ⟨tau, hB⟩ : ∃ t : ℂ, d z1 = t * star (c y1) :=")
    w("    ⟨d z1 / star (c y1), (div_mul_cancel₀ _ s1).symm⟩")
    w("  have hu : Complex.normSq tau = 1 := by")
    w("    have hq := congrArg Complex.normSq hB")
    w("    rw [map_mul, normSq_star, k1, l1] at hq")
    w("    linarith")
    w("  have hunit : star tau * tau = 1 := by")
    w("    rw [SixQubit.star_mul_self, hu]; norm_num")
    for (k, hyp) in [(2, "ho16"), (3, "ho17"), (4, "ho18"), (5, "ho19")]:
        w("  have t{} : d z{} = -(tau * star (c y{})) := by".format(k, k, k))
        w("    have h : star (c y1) * (d z{} + tau * star (c y{})) = 0 := by".format(k, k))
        w("      linear_combination {} - star (c y{}) * hB".format(hyp, k))
        w("    linear_combination (mul_eq_zero.mp h).resolve_left s1")
    w("  have t0 : d z0 = tau * star (c y0) := by")
    w("    have h : star (c y2) * (d z0 - tau * star (c y0)) = 0 := by")
    w("      linear_combination ho21 - star (c y0) * t2")
    w("    linear_combination (mul_eq_zero.mp h).resolve_left s2")
    for (e, v, q) in [(6, 3, "q1"), (7, 4, "q2"), (8, 5, "q3"),
                      (9, 4, "q4"), (10, 5, "q5"), (11, 5, "q6")]:
        w("  have t{} : d z{} = -(tau * star (c y{})) := by".format(e, e, e))
        w("    have h : star (c y{}) * (d z{} + tau * star (c y{})) = 0 := by".format(v, e, e))
        w("      linear_combination -{} + star (c y{}) * t{}".format(q, e, v))
        w("    linear_combination (mul_eq_zero.mp h).resolve_left s{}".format(v))
    w("  exact ⟨tau, hunit, t0, hB, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11⟩")
    w()



# ----------------------------------------------------------------------------
# incidence / flip facts and the per-mask projector-trace split
# ----------------------------------------------------------------------------

# every flip mask of Hamming weight at most three that joins two fiber points,
# as (mask, incidence pairs, kind)
#   'diag'  the trivial mask, twelve fixed points
#   'even'  a weight-two mask; both amplitudes of a pair carry the same Theta sign
#   'odd'   a weight-three mask pairing an anchor with an edge (opposite signs)
#   'tri'   an exceptional weight-three mask {i,5,6}
MASKS = ([(M0, [(k, k) for k in range(12)], "diag")]
         + [(f, pairs_of(f), "even") for (f, V, W_, K, L) in EDGE_MASKS]
         + [(MASK45, pairs_of(MASK45), "even")]
         + [(f, pr, "odd") for f, pr in W3_AB]
         + [(f, pr, "tri") for f, pr in W3_C])
GM2 = [m[0] for m in MASKS if sum(m[0]) <= 2]
GM3 = [m[0] for m in MASKS]


def nest(terms):
    out = terms[-1]
    for t in reversed(terms[:-1]):
        out = "{} + ({})".format(t, out)
    return out


def starsimp(idx):
    """simp set for pushing `star` through a top amplitude of index `idx`."""
    if idx >= 2:
        return "simp only [star_neg, star_mul', star_star]"
    return "simp only [star_mul', star_star]"


def emit_incidences():
    w("/-! ## 7.  Fiber incidences, and the projector trace of each incident mask -/")
    w()
    for f, pr, kind in MASKS:
        nm = mnm(f)
        fixed = (kind == "diag")
        pts = []
        for (p, q) in pr:
            pts += [p] if fixed else [p, q]
        w("theorem incB_{} : S0.filter (fun s => SS.bxor s {} ∈ S0) = {{{}}} := by decide"
          .format(nm, bname(f), ", ".join("y{}".format(k) for k in pts)))
        w("theorem incT_{} : S1.filter (fun s => SS.bxor s {} ∈ S1) = {{{}}} := by decide"
          .format(nm, bname(f), ", ".join("z{}".format(k) for k in pts)))
        for (p, q) in pr:
            w("theorem flB_{}_{} : SS.bxor y{} {} = y{} := by decide"
              .format(nm, p, p, bname(f), q))
            w("theorem flT_{}_{} : SS.bxor z{} {} = z{} := by decide"
              .format(nm, p, p, bname(f), q))
            if not fixed:
                w("theorem flB_{}_{} : SS.bxor y{} {} = y{} := by decide"
                  .format(nm, q, q, bname(f), p))
                w("theorem flT_{}_{} : SS.bxor z{} {} = z{} := by decide"
                  .format(nm, q, q, bname(f), p))
        w()
        w("/-- The projector trace of every Pauli with flip mask `{}`, as a bottom"
          .format("".join(str(x) for x in f)))
        w("bracket and a top bracket over the incidences of that mask. -/")
        w("theorem split_{} (c d : SS.BitString 6 -> ℂ)".format(nm))
        w(SUPPORT_HYP)
        w("    (zz : SS.BitString 6) :")
        w("    projTrace c d ⟨{}, zz⟩".format(bname(f)))
        w("      = Complex.I ^ (SS.PauliString.mk {} zz).numY".format(bname(f)))
        w("          * (" + nest(botterms(pr, fixed)) + ")")
        w("        + Complex.I ^ (SS.PauliString.mk {} zz).numY".format(bname(f)))
        w("          * (" + nest(topterms(pr, fixed)) + ") := by")
        w("  rw [projTrace, SS.innerC_pauliAct_support S0 S0 c c _ hc hc,")
        w("    SS.innerC_pauliAct_support S1 S1 d d _ hd hd]")
        w("  rw [show (SS.PauliString.mk {} zz).x = {} from rfl, incB_{}, incT_{}]"
          .format(bname(f), bname(f), nm, nm))
        n = len(pts)
        w("  rw [" + chain(n) + ",")
        w("    " + chain(n) + "]")
        w("  rw [show (SS.PauliString.mk {} zz).z = zz from rfl]".format(bname(f)))
        flips = []
        for (p, q) in pr:
            flips += ["flB_{}_{}".format(nm, p)]
            if not fixed:
                flips += ["flB_{}_{}".format(nm, q)]
        for (p, q) in pr:
            flips += ["flT_{}_{}".format(nm, p)]
            if not fixed:
                flips += ["flT_{}_{}".format(nm, q)]
        w("  rw [" + ", ".join(flips) + "]")
        w()


def botterms(pr, fixed):
    out = []
    for (p, q) in pr:
        out.append("SS.signC (SS.bdot zz y{}) (star (c y{}) * c y{})".format(p, q, p))
        if not fixed:
            out.append("SS.signC (SS.bdot zz y{}) (star (c y{}) * c y{})".format(q, p, q))
    return out


def topterms(pr, fixed):
    out = []
    for (p, q) in pr:
        out.append("SS.signC (SS.bdot zz z{}) (star (d z{}) * d z{})".format(p, q, p))
        if not fixed:
            out.append("SS.signC (SS.bdot zz z{}) (star (d z{}) * d z{})".format(q, p, q))
    return out


# ----------------------------------------------------------------------------
# A_3 machinery
# ----------------------------------------------------------------------------

TRI_HYP = {}


def emit_a3_masks():
    w("/-! ## 8.  `A_3 = 0`: every weight-three projector trace vanishes -/")
    w()
    w("/-- The twenty-four flip masks of Hamming weight at most three that join two")
    w("points of a fiber.  Every weight-three Pauli has its flip mask here or has no")
    w("incidence at all. -/")
    w("def gm3 : Finset (SS.BitString 6) :=")
    w("  {" + ", ".join(bname(f) for f in GM3) + "}")
    w()
    w("/-- Every other mask of Hamming weight at most three is inert on both fibers:")
    w("the chapter's residue condition, decided over all sixty-four masks. -/")
    w("theorem masks3 : ∀ f : SS.BitString 6, SS.hammingWt f ≤ 3 →")
    w("    f ∈ gm3 ∨ (S0.filter (fun s => SS.bxor s f ∈ S0) = ∅")
    w("        ∧ S1.filter (fun s => SS.bxor s f ∈ S1) = ∅) := by decide")
    w()
    for f, pr, kind in MASKS:
        nm = mnm(f)
        fixed = (kind == "diag")
        if kind == "tri":
            continue
        # sign relation between the top Walsh signs and the bottom ones
        conj = []
        for (p, q) in pr:
            if kind == "odd":
                conj.append("SS.bdot zz z{} = SS.bdot zz y{}".format(p, q))
                conj.append("SS.bdot zz z{} = SS.bdot zz y{}".format(q, p))
            elif fixed:
                conj.append("SS.bdot zz z{} = !(SS.bdot zz y{})".format(p, p))
            else:
                conj.append("SS.bdot zz z{} = !(SS.bdot zz y{})".format(p, q))
                conj.append("SS.bdot zz z{} = !(SS.bdot zz y{})".format(q, p))
        w("theorem sgn3_{} : ∀ zz : SS.BitString 6, (SS.PauliString.mk {} zz).wt = 3 →"
          .format(nm, bname(f)))
        w("    " + "\n      ∧ ".join(conj) + " := by decide")
        w()
        if kind == "odd":
            w("/-- Weight-three mask `{}`: the anchor `{}` and the edge `{}` carry opposite"
              .format("".join(str(x) for x in f), PTS[pr[0][0]][0], PTS[pr[0][1]][0]))
            w("`Theta`-signs, so the top bracket is the negative of the bottom one. -/")
        elif fixed:
            w("/-- A weight-three Pauli with trivial flip mask is diagonal with an odd")
            w("`z`-mask, and complementation reverses every one of its Walsh signs. -/")
        else:
            w("/-- Weight-two flip mask `{}` carrying a weight-three Pauli: the extra `Z`"
              .format("".join(str(x) for x in f)))
            w("outside the mask makes complementation reverse every Walsh sign. -/")
        w("theorem a3_{} (c d : SS.BitString 6 -> ℂ)".format(nm))
        w(SUPPORT_HYP)
        w("    (tau : ℂ) (htf : TopForm c d tau) :")
        w("    ∀ zz : SS.BitString 6, (SS.PauliString.mk {} zz).wt = 3 →".format(bname(f)))
        w("      projTrace c d ⟨{}, zz⟩ = 0 := by".format(bname(f)))
        w("  intro zz hz")
        nconj = len(conj)
        w("  obtain ⟨" + ", ".join("e{}".format(i) for i in range(1, nconj + 1))
          + "⟩ := sgn3_{} zz hz".format(nm))
        us = []
        for (p, q) in pr:
            sgn = "-(" if kind == "odd" else ""
            cl = ")" if kind == "odd" else ""
            w("  have uA{} : star (d z{}) * d z{} = {}star (c y{}) * c y{}{} := by"
              .format(p, q, p, sgn, p, q, cl))
            w("    rw [htf.t{}]".format(p) if p == q
              else "    rw [htf.t{}, htf.t{}]".format(p, q))
            w("    " + starsimp(q))
            w("    linear_combination ({}(c y{} * star (c y{}))) * htf.unit"
              .format("-" if kind == "odd" else "", q, p))
            us.append("uA{}".format(p))
            if not fixed:
                w("  have uB{} : star (d z{}) * d z{} = {}star (c y{}) * c y{}{} := by"
                  .format(p, p, q, sgn, q, p, cl))
                w("    rw [htf.t{}, htf.t{}]".format(p, q))
                w("    " + starsimp(p))
                w("    linear_combination ({}(c y{} * star (c y{}))) * htf.unit"
                  .format("-" if kind == "odd" else "", p, q))
                us.append("uB{}".format(p))
        w("  rw [split_{} c d hc hd zz]".format(nm))
        w("  rw [" + ", ".join("e{}".format(i) for i in range(1, nconj + 1)) + "]")
        w("  rw [" + ", ".join(us) + "]")
        w("  rw [← mul_add]")
        w("  refine mul_eq_zero_of_right _ ?_")
        w("  simp only [{}]".format("signC_neg" if kind == "odd" else "signC_not"))
        w("  ring")
        w()
    for f, pr, kind in MASKS:
        if kind != "tri":
            continue
        nm = mnm(f)
        conj = []
        for (p, q) in pr[1:]:
            conj.append("SS.bdot zz y{} = SS.bdot zz y{}".format(p, pr[0][0]))
            conj.append("SS.bdot zz y{} = SS.bdot zz y{}".format(q, pr[0][1]))
        for (p, q) in pr[1:]:
            conj.append("SS.bdot zz z{} = SS.bdot zz z{}".format(p, pr[0][0]))
            conj.append("SS.bdot zz z{} = SS.bdot zz z{}".format(q, pr[0][1]))
        w("theorem sgn3_{} : ∀ zz : SS.BitString 6, (SS.PauliString.mk {} zz).wt = 3 →"
          .format(nm, bname(f)))
        w("    " + "\n      ∧ ".join(conj) + " := by decide")
        tri = " + ".join("star (c y{}) * c y{}".format(p, q) for (p, q) in pr)
        TRI_HYP[f] = (tri, pr)
        w()
        w("/-- Exceptional weight-three mask `{}` -- the chapter's `f = {{i,5,6}}`.  Its"
          .format("".join(str(x) for x in f)))
        w("three incidences carry a common Walsh sign on each side, so each bracket is a")
        w("triangle sum opposite the flipped vertex. -/")
        w("theorem a3_{} (c d : SS.BitString 6 -> ℂ)".format(nm))
        w(SUPPORT_HYP)
        w("    (tau : ℂ) (htf : TopForm c d tau)")
        w("    (htri : {} = 0) :".format(tri))
        w("    ∀ zz : SS.BitString 6, (SS.PauliString.mk {} zz).wt = 3 →".format(bname(f)))
        w("      projTrace c d ⟨{}, zz⟩ = 0 := by".format(bname(f)))
        w("  have hs := congrArg star htri")
        w("  simp only [star_add, star_mul', star_star, star_zero] at hs")
        w("  have hX : " + " + ".join("star (c y{}) * c y{}".format(q, p) for (p, q) in pr)
          + " = 0 := by linear_combination hs")
        w("  intro zz hz")
        w("  obtain ⟨" + ", ".join("e{}".format(i) for i in range(1, 9))
          + "⟩ := sgn3_{} zz hz".format(nm))
        us = []
        for (p, q) in pr:
            w("  have uA{} : star (d z{}) * d z{} = star (c y{}) * c y{} := by"
              .format(p, q, p, p, q))
            w("    rw [htf.t{}, htf.t{}]".format(p, q))
            w("    " + starsimp(q))
            w("    linear_combination (c y{} * star (c y{})) * htf.unit".format(q, p))
            w("  have uB{} : star (d z{}) * d z{} = star (c y{}) * c y{} := by"
              .format(p, p, q, q, p))
            w("    rw [htf.t{}, htf.t{}]".format(p, q))
            w("    " + starsimp(p))
            w("    linear_combination (c y{} * star (c y{})) * htf.unit".format(p, q))
            us += ["uA{}".format(p), "uB{}".format(p)]
        w("  rw [split_{} c d hc hd zz]".format(nm))
        w("  rw [" + ", ".join("e{}".format(i) for i in range(1, 9)) + "]")
        w("  rw [" + ", ".join(us) + "]")
        w("  rw [← mul_add]")
        w("  refine mul_eq_zero_of_right _ ?_")
        w("  have hb := sixSum (SS.bdot zz y{}) (SS.bdot zz y{}) hX htri"
          .format(pr[0][0], pr[0][1]))
        w("  have ht := sixSum (SS.bdot zz z{}) (SS.bdot zz z{}) htri hX"
          .format(pr[0][0], pr[0][1]))
        w("  linear_combination hb + ht")
        w()


def triangle_call(f, pr, branch):
    """Order the three triangle vertices so that the edges opposite them carry the
    colours (mu, w mu, w^2 mu) in the order `triangle_sum` expects."""
    if branch == 0:
        col = {(1, 2): 0, (3, 4): 0, (1, 3): 1, (2, 4): 1, (1, 4): 2, (2, 3): 2}
    else:
        col = {(1, 2): 0, (3, 4): 0, (1, 3): 2, (2, 4): 2, (1, 4): 1, (2, 3): 1}
    hname = {(1, 2): "hp12", (3, 4): "hp34", (1, 3): "b1", (2, 4): "b2",
             (1, 4): "b3", (2, 3): "b4"}
    verts = [p for p, _ in pr]
    tri = [v for v in (1, 2, 3, 4) if VERTY[v] in verts]
    assert len(tri) == 3

    def ce(a, b):
        return col[tuple(sorted((a, b)))]
    for perm in [(tri[0], tri[1], tri[2]), (tri[0], tri[2], tri[1]),
                 (tri[1], tri[0], tri[2]), (tri[1], tri[2], tri[0]),
                 (tri[2], tri[0], tri[1]), (tri[2], tri[1], tri[0])]:
        a, b, cc = perm
        if ce(b, cc) == 0 and ce(a, cc) == 1 and ce(a, b) == 2:
            return dict(ya=VERTY[a], yb=VERTY[b], yc=VERTY[cc],
                        eA=EDGEY[tuple(sorted((b, cc)))],
                        eB=EDGEY[tuple(sorted((a, cc)))],
                        eC=EDGEY[tuple(sorted((a, b)))],
                        hA=hname[tuple(sorted((b, cc)))],
                        hB=hname[tuple(sorted((a, cc)))],
                        hC=hname[tuple(sorted((a, b)))])
    raise AssertionError((f, tri, branch))


# ----------------------------------------------------------------------------
# weight-two values
# ----------------------------------------------------------------------------

def bottom_form(f, z, pr):
    sp = [dot(z, S0[p]) for p, q in pr]
    sq = [dot(z, S0[q]) for p, q in pr]
    n = len(pr)
    if all(x == 0 for x in sp + sq):
        return ("P", 1)
    if all(x == 1 for x in sp + sq):
        return ("P", -1)
    if (sp[0] == 0 and sq[0] == 1 and all(sp[k] == 1 for k in range(1, n))
            and all(sq[k] == 0 for k in range(1, n))):
        return ("M", 1)
    if (sp[0] == 1 and sq[0] == 0 and all(sp[k] == 0 for k in range(1, n))
            and all(sq[k] == 1 for k in range(1, n))):
        return ("M", -1)
    raise AssertionError((f, z, sp, sq))


def gexpr(pr):
    terms = ["star (c y{}) * c y{}".format(pr[0][1], pr[0][0])]
    for (p, q) in pr[1:]:
        terms.append("star (c y{}) * c y{}".format(p, q))
    return " + ".join(terms)


def gbar(pr):
    terms = ["star (c y{}) * c y{}".format(pr[0][0], pr[0][1])]
    for (p, q) in pr[1:]:
        terms.append("star (c y{}) * c y{}".format(q, p))
    return " + ".join(terms)


DIAG_VALS = []


def emit_diag_values():
    zs = [M0] + ZSETS[M0]
    w("/-! ## 9.  The diagonal masks: the identity and the fifteen `Z_i Z_j` rows -/")
    w()
    for z in zs:
        for k in range(12):
            sign_lemma(z, k, False)
            sign_lemma(z, k, True)
    w()
    for z in zs:
        bot = sum((-1) ** dot(z, S0[k]) * PROB[k] for k in range(12))
        top = sum((-1) ** dot(z, S1[k]) * PROB[k] for k in range(12))
        assert bot == top, (z, bot, top)
        DIAG_VALS.append((z, bot))
    w("set_option maxHeartbeats 3200000 in")
    w("/-- **The diagonal projector traces.**  A trivial flip mask makes both fibers")
    w("fully incident, and complementation matches the two probability vectors, so the")
    w("trace is twice the bottom Walsh sum.  The forced magnitudes evaluate all sixteen:")
    w("`1` for the identity, `1/15` on the six `K_4` edges, `+-1/5` on the eight rows")
    w("joining a vertex to a last coordinate, and `-3/5` on `Z_5 Z_6` -- exactly the")
    w("chapter's weight-two table. -/")
    w("theorem diag_values (c d : SS.BitString 6 -> ℂ)")
    w(SUPPORT_HYP)
    for k in range(12):
        w("    (k{} : Complex.normSq (c y{}) = {})".format(k, k, frac(PROB[k])))
    for k in range(12):
        w("    (l{} : Complex.normSq (d z{}) = {})".format(k, k, frac(PROB[k])))
    conj = ["Complex.normSq (projTrace c d ⟨{}, {}⟩) = {}".format(
        bname(M0), bname(z), frac(4 * v * v)) for z, v in DIAG_VALS]
    w("    : " + "\n      ∧ ".join(conj) + " := by")
    w("  refine ⟨" + ", ".join(["?_"] * len(DIAG_VALS)) + "⟩")
    for z, v in DIAG_VALS:
        pt = "(SS.PauliString.mk {} {})".format(bname(M0), bname(z))
        w("  · have h : projTrace c d ⟨{}, {}⟩".format(bname(M0), bname(z)))
        w("        = Complex.I ^ {}.numY * (2 * (({} : ℝ) : ℂ)) := by".format(pt, frac(v)))
        w("      rw [split_{} c d hc hd {}]".format(mnm(M0), bname(z)))
        svals = [dot(z, S0[k]) for k in range(12)] + [dot(z, S1[k]) for k in range(12)]
        names = ([sign_lemma(z, k, False) for k in range(12)]
                 + [sign_lemma(z, k, True) for k in range(12)])
        w("      simp only [" + ", ".join(names) + ",")
        w("        " + ", ".join(signsimp(svals)) + ", SixQubit.star_mul_self]")
        w("      rw [" + ", ".join("k{}".format(k) for k in range(12)) + ",")
        w("        " + ", ".join("l{}".format(k) for k in range(12)) + "]")
        w("      push_cast")
        w("      ring")
        w("    rw [h, normSq_I_pow_mul, normSq_two_mul, Complex.normSq_ofReal]")
        w("    norm_num")
    w()


def emit_edge_values():
    w("/-! ## 10.  The seven non-diagonal weight-two masks -/")
    w()
    masks = [(f, pairs_of(f)) for (f, V, W_, K, L) in EDGE_MASKS]
    masks.append((MASK45, pairs_of(MASK45)))
    info = []
    for f, pr in masks:
        G = gexpr(pr)
        forms = [(z, bottom_form(f, z, pr)) for z in ZSETS[f]]
        info.append((f, pr, G, forms))
        for z, _ in forms:
            for (p, q) in pr:
                sign_lemma(z, p, False)
                sign_lemma(z, q, False)
                sign_lemma(z, p, True)
                sign_lemma(z, q, True)
    w()
    for f, pr, G, forms in info:
        nm = mnm(f)
        Gb = gbar(pr)
        edge = pr[0][0] >= 2
        w("set_option maxHeartbeats 1600000 in")
        w("/-- The four dressings of the flip mask `{}`.  Their projector traces are"
          .format("".join(str(x) for x in f)))
        w("`+-2 (G + conj G)` and `+-2 (G - conj G)`, so this mask contributes")
        w("`32 * normSq G` to the weight-two sum. -/")
        w("theorem vals_{} (c d : SS.BitString 6 -> ℂ)".format(nm))
        w(SUPPORT_HYP)
        w("    (tau : ℂ) (htf : TopForm c d tau) :")
        conj = []
        for z, (kind, sgn) in forms:
            op = "+" if kind == "P" else "-"
            conj.append(
                "Complex.normSq (projTrace c d ⟨{}, {}⟩)\n        = 4 * Complex.normSq (({}) {} star ({}))"
                .format(bname(f), bname(z), G, op, G))
        w("    " + "\n      ∧ ".join(conj) + " := by")
        w("  refine ⟨" + ", ".join(["?_"] * len(forms)) + "⟩")
        for z, (kind, sgn) in forms:
            op = "+" if kind == "P" else "-"
            core = "(({}) {} star ({}))".format(G, op, G)
            coreX = "(({}) {} ({}))".format(G, op, Gb)
            V = core if sgn == 1 else "(-{})".format(core)
            VX = coreX if sgn == 1 else "(-{})".format(coreX)
            pt = "(SS.PauliString.mk {} {})".format(bname(f), bname(z))
            w("  · have h : projTrace c d ⟨{}, {}⟩".format(bname(f), bname(z)))
            w("        = Complex.I ^ {}.numY * (2 * {}) := by".format(pt, V))
            w("      rw [split_{} c d hc hd {}]".format(nm, bname(z)))
            names, svals = [], []
            for (p, q) in pr:
                names += [sign_lemma(z, p, False), sign_lemma(z, q, False)]
                svals += [dot(z, S0[p]), dot(z, S0[q])]
            for (p, q) in pr:
                names += [sign_lemma(z, p, True), sign_lemma(z, q, True)]
                svals += [dot(z, S1[p]), dot(z, S1[q])]
            w("      simp only [" + ", ".join(names) + ",")
            w("        " + ", ".join(signsimp(svals)) + "]")
            tops = []
            for (p, q) in pr:
                tops += ["htf.t{}".format(p), "htf.t{}".format(q)]
            w("      rw [" + ", ".join(tops) + "]")
            sset = (["star_neg"] if edge else []) + ["star_mul'", "star_star"]
            if len(pr) > 1:
                sset.append("star_add")
            w("      simp only [" + ", ".join(sset) + "]")
            w("      linear_combination (Complex.I ^ {}.numY * {}) * htf.unit".format(pt, VX))
            if sgn == 1:
                w("    rw [h, normSq_I_pow_mul, normSq_two_mul]")
            else:
                w("    rw [h, normSq_I_pow_mul, normSq_two_mul, Complex.normSq_neg]")
        w()
    return info


# ----------------------------------------------------------------------------
# the enumerator theorems
# ----------------------------------------------------------------------------

def emit_enumerator(info):
    gm2 = list(GM2)
    w("/-! ## 11.  The enumerator coefficients -/")
    w()
    w("/-- The eight flip masks of Hamming weight at most two that join two points of a")
    w("fiber. -/")
    w("def gm2 : Finset (SS.BitString 6) :=")
    w("  {" + ", ".join(bname(f) for f in gm2) + "}")
    w()
    w("theorem masks2 : ∀ f : SS.BitString 6, SS.hammingWt f ≤ 2 →")
    w("    f ∈ gm2 ∨ (S0.filter (fun s => SS.bxor s f ∈ S0) = ∅")
    w("        ∧ S1.filter (fun s => SS.bxor s f ∈ S1) = ∅) := by decide")
    w()
    w("theorem masks0 : ∀ f : SS.BitString 6, SS.hammingWt f ≤ 0 → f = {} := by decide"
      .format(bname(M0)))
    w()
    for f in gm2:
        w("def Zs{} : Finset (SS.BitString 6) :=".format(mnm(f)))
        w("  {" + ", ".join(bname(z) for z in ZSETS[f]) + "}")
        w()
        w("theorem zset_{} : ∀ zz : SS.BitString 6, zz ∉ Zs{} →".format(mnm(f), mnm(f)))
        w("    (SS.PauliString.mk {} zz).wt ≠ 2 := by decide".format(bname(f)))
        w()
    w("def Zs0 : Finset (SS.BitString 6) := {" + bname(M0) + "}")
    w()
    w("theorem zset_0 : ∀ zz : SS.BitString 6, zz ∉ Zs0 →")
    w("    (SS.PauliString.mk {} zz).wt ≠ 0 := by decide".format(bname(M0)))
    w()
    w("/-- The enumerator sum, split into an outer sum over flip masks and an inner sum")
    w("over dressings. -/")
    w("theorem AEnum_split (c d : SS.BitString 6 -> ℂ) (j : ℕ) :")
    w("    AEnum c d j = (∑ f : SS.BitString 6, ∑ zz : SS.BitString 6,")
    w("        if (SS.PauliString.mk f zz).wt = j")
    w("          then Complex.normSq (projTrace c d ⟨f, zz⟩) else 0) / 4 := by")
    w("  rw [AEnum, paulisOfWeight, Finset.sum_filter, Fintype.sum_prod_type]")
    w()

    # ------------------------------------------------ A_0
    w("set_option maxHeartbeats 1600000 in")
    w("/-- **`A_0 = 1`.**  The identity is the only weight-zero Pauli, and its projector")
    w("trace is the sum of the two normalizations. -/")
    w("theorem A0_value (c d : SS.BitString 6 -> ℂ)")
    w(SUPPORT_HYP)
    w(MOMENT_HYP)
    w(ROWS_HYP + " :")
    w("    AEnum c d 0 = 1 := by")
    w("  obtain ⟨" + ", ".join("k{}".format(i) for i in range(12)) + ", "
      + ", ".join("l{}".format(i) for i in range(12)) + "⟩ :=")
    w("    magnitudes_forced c d hm " + ROWS_ARGS)
    w("  obtain ⟨v0, " + ", ".join(["-"] * 15) + "⟩ :=")
    w("    diag_values c d hc hd " + " ".join("k{}".format(i) for i in range(12))
      + " " + " ".join("l{}".format(i) for i in range(12)))
    w("  have hin : (∑ zz : SS.BitString 6,")
    w("      if (SS.PauliString.mk {} zz).wt = 0".format(bname(M0)))
    w("        then Complex.normSq (projTrace c d ⟨{}, zz⟩) else 0) = 4 := by".format(bname(M0)))
    w("    rw [← Finset.sum_subset (Finset.subset_univ Zs0)")
    w("        (fun zz _ hzz => by rw [if_neg (zset_0 zz hzz)])]")
    w("    simp only [Zs0, Finset.sum_singleton]")
    w("    rw [if_pos (by decide : (SS.PauliString.mk {} {}).wt = 0), v0]".format(
        bname(M0), bname(M0)))
    w("  rw [AEnum_split]")
    w("  have hout : (∑ f : SS.BitString 6, ∑ zz : SS.BitString 6,")
    w("      if (SS.PauliString.mk f zz).wt = 0")
    w("        then Complex.normSq (projTrace c d ⟨f, zz⟩) else 0)")
    w("      = ∑ f ∈ Zs0, ∑ zz : SS.BitString 6,")
    w("      if (SS.PauliString.mk f zz).wt = 0")
    w("        then Complex.normSq (projTrace c d ⟨f, zz⟩) else 0 := by")
    w("    refine (Finset.sum_subset (Finset.subset_univ Zs0) ?_).symm")
    w("    intro f _ hf")
    w("    refine Finset.sum_eq_zero (fun zz _ => ?_)")
    w("    by_cases hw : (SS.PauliString.mk f zz).wt = 0")
    w("    · refine absurd (Finset.mem_singleton.mpr (masks0 f ?_)) hf")
    w("      have h1 := hammingWt_x_le_wt (SS.PauliString.mk f zz)")
    w("      rw [hw] at h1")
    w("      exact h1")
    w("    · rw [if_neg hw]")
    w("  rw [hout]")
    w("  simp only [Zs0, Finset.sum_singleton]")
    w("  rw [hin]")
    w("  norm_num")
    w()

    # ------------------------------------------------ A_2
    w("set_option maxHeartbeats 3200000 in")
    w("/-- **`A_2 = 21/25` for every exact orbit-36 solution.** -/")
    w("theorem A2_value (c d : SS.BitString 6 -> ℂ)")
    w(SUPPORT_HYP)
    w(MOMENT_HYP)
    w(ROWS_HYP)
    w(EX16_HYP + " :")
    w("    AEnum c d 2 = 21/25 := by")
    w("  obtain ⟨" + ", ".join("k{}".format(i) for i in range(12)) + ", "
      + ", ".join("l{}".format(i) for i in range(12)) + "⟩ :=")
    w("    magnitudes_forced c d hm " + ROWS_ARGS)
    w("  obtain ⟨-, -, n2, n3, n4, n5, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=")
    w("    full_support c d hm " + ROWS_ARGS)
    w("  obtain ⟨tau, htf⟩ := top_form c d hm " + ROWS_ARGS + " ho21")
    w("  obtain ⟨mu, hmu, hp12, hp34, hcol⟩ := phase_rigidity c d hm " + ROWS_ARGS)
    w("  have hG : " + "\n      ∧ ".join(
        "Complex.normSq ({}) = 1/900".format(gexpr(pairs_of(f)))
        for (f, V, W_, K, L) in EDGE_MASKS) + " := by")
    w("    rcases hcol with ⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3, b4⟩")
    w("    · exact edges_of_colouring rho_quadratic star_rho k2 k3 k4 k5 hmu n2 n3 n4 n5")
    w("        hp12 hp34 b1 b2 b3 b4")
    w("    · exact edges_of_colouring rho_sq_quadratic star_rho_sq k2 k3 k4 k5 hmu")
    w("        n2 n3 n4 n5 hp12 hp34 b1 b2")
    w("        (by linear_combination b3 - (rho * mu) * rho_pow_three)")
    w("        (by linear_combination b4 - (rho * mu) * rho_pow_three)")
    w("  obtain ⟨" + ", ".join("g{}".format(i) for i in range(1, 7)) + "⟩ := hG")
    w("  have g7 : Complex.normSq (star (c y1) * c y0) = 1/100 := by")
    w("    rw [map_mul, normSq_star, k1, k0]; norm_num")
    w("  obtain ⟨" + ", ".join("v{}".format(i) for i in range(16)) + "⟩ :=")
    w("    diag_values c d hc hd " + " ".join("k{}".format(i) for i in range(12))
      + " " + " ".join("l{}".format(i) for i in range(12)))
    for idx, (f, pr, G, forms) in enumerate(info):
        w("  obtain ⟨" + ", ".join("a{}{}".format(idx, t) for t in range(len(forms)))
          + "⟩ := vals_{} c d hc hd tau htf".format(mnm(f)))
    # inner reductions
    w("  have hin0 : (∑ zz : SS.BitString 6,")
    w("      if (SS.PauliString.mk {} zz).wt = 2".format(bname(M0)))
    w("        then Complex.normSq (projTrace c d ⟨{}, zz⟩) else 0)".format(bname(M0)))
    rhs = " + ".join("({})".format(frac(4 * v * v)) for z, v in DIAG_VALS[1:])
    w("      = " + rhs + " := by")
    w("    rw [← Finset.sum_subset (Finset.subset_univ Zs{})".format(mnm(M0)))
    w("        (fun zz _ hzz => by rw [if_neg (zset_{} zz hzz)])]".format(mnm(M0)))
    w("    simp only [Zs{}]".format(mnm(M0)))
    w("    rw [" + chain(len(ZSETS[M0])) + "]")
    for z in ZSETS[M0]:
        w("    rw [if_pos (by decide : (SS.PauliString.mk {} {}).wt = 2)]".format(
            bname(M0), bname(z)))
    w("    rw [" + ", ".join("v{}".format(i) for i in range(1, 16)) + "]")
    w("    norm_num")
    for idx, (f, pr, G, forms) in enumerate(info):
        w("  have hin{} : (∑ zz : SS.BitString 6,".format(idx + 1))
        w("      if (SS.PauliString.mk {} zz).wt = 2".format(bname(f)))
        w("        then Complex.normSq (projTrace c d ⟨{}, zz⟩) else 0)".format(bname(f)))
        parts = []
        for t, (z, (kind, sgn)) in enumerate(forms):
            op = "+" if kind == "P" else "-"
            parts.append("4 * Complex.normSq (({}) {} star ({}))".format(G, op, G))
        w("      = " + "\n        + ".join(parts) + " := by")
        w("    rw [← Finset.sum_subset (Finset.subset_univ Zs{})".format(mnm(f)))
        w("        (fun zz _ hzz => by rw [if_neg (zset_{} zz hzz)])]".format(mnm(f)))
        w("    simp only [Zs{}]".format(mnm(f)))
        w("    rw [" + chain(len(forms)) + "]")
        for z, _ in forms:
            w("    rw [if_pos (by decide : (SS.PauliString.mk {} {}).wt = 2)]".format(
                bname(f), bname(z)))
        w("    rw [" + ", ".join("a{}{}".format(idx, t) for t in range(len(forms))) + "]")
        w("    ring")
    w("  rw [AEnum_split]")
    w("  have hout : (∑ f : SS.BitString 6, ∑ zz : SS.BitString 6,")
    w("      if (SS.PauliString.mk f zz).wt = 2")
    w("        then Complex.normSq (projTrace c d ⟨f, zz⟩) else 0)")
    w("      = ∑ f ∈ gm2, ∑ zz : SS.BitString 6,")
    w("      if (SS.PauliString.mk f zz).wt = 2")
    w("        then Complex.normSq (projTrace c d ⟨f, zz⟩) else 0 := by")
    w("    refine (Finset.sum_subset (Finset.subset_univ gm2) ?_).symm")
    w("    intro f _ hf")
    w("    refine Finset.sum_eq_zero (fun zz _ => ?_)")
    w("    by_cases hw : (SS.PauliString.mk f zz).wt = 2")
    w("    · rw [if_pos hw]")
    w("      obtain ⟨e0, e1⟩ := (masks2 f (by")
    w("        have h1 := hammingWt_x_le_wt (SS.PauliString.mk f zz)")
    w("        rw [hw] at h1")
    w("        exact h1)).resolve_left hf")
    w("      rw [projTrace_no_incidence hc hd e0 e1, Complex.normSq_zero]")
    w("    · rw [if_neg hw]")
    w("  rw [hout]")
    w("  simp only [gm2]")
    w("  rw [" + chain(8) + "]")
    w("  rw [" + ", ".join("hin{}".format(i) for i in range(8)) + "]")
    for idx, (f, pr, G, forms) in enumerate(info):
        w("  have s{} := normSq_split ({})".format(idx, G))
    w("  linarith [" + ", ".join("s{}".format(i) for i in range(len(info)))
      + ", " + ", ".join("g{}".format(i) for i in range(1, 8)) + "]")
    w()

    # ------------------------------------------------ A_3
    w("set_option maxHeartbeats 3200000 in")
    w("/-- **`A_3 = 0` for every exact orbit-36 solution.** -/")
    w("theorem A3_value (c d : SS.BitString 6 -> ℂ)")
    w(SUPPORT_HYP)
    w(MOMENT_HYP)
    w(ROWS_HYP)
    w(EX16_HYP + " :")
    w("    AEnum c d 3 = 0 := by")
    w("  obtain ⟨" + ", ".join(("k{}".format(i) if i in (2, 3, 4, 5) else "-")
                               for i in range(12)) + ", " + ", ".join(["-"] * 12) + "⟩ :=")
    w("    magnitudes_forced c d hm " + ROWS_ARGS)
    w("  obtain ⟨-, -, n2, n3, n4, n5, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=")
    w("    full_support c d hm " + ROWS_ARGS)
    w("  obtain ⟨tau, htf⟩ := top_form c d hm " + ROWS_ARGS + " ho21")
    w("  obtain ⟨mu, -, hp12, hp34, hcol⟩ := phase_rigidity c d hm " + ROWS_ARGS)
    w("  have htri : " + "\n      ∧ ".join(TRI_HYP[f][0] + " = 0" for f, _ in W3_C) + " := by")
    w("    rcases hcol with ⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3, b4⟩")
    for branch in (0, 1):
        w("    · refine ⟨" + ", ".join(["?_"] * len(W3_C)) + "⟩")
        for f, pr in W3_C:
            t = triangle_call(f, pr, branch)
            w("      · linear_combination triangle_sum (r2 := c y{}) (r3 := c y{})".format(
                t["ya"], t["yb"]))
            w("          (r4 := c y{}) (c34 := c y{}) (c24 := c y{}) (c23 := c y{})".format(
                t["yc"], t["eA"], t["eB"], t["eC"]))
            w("          (mu := mu) k{} k{} k{}".format(t["ya"], t["yb"], t["yc"]))
            w("          (by linear_combination {}) (by linear_combination {})".format(
                t["hA"], t["hB"]))
            w("          (by linear_combination {}) n{} n{} n{}".format(
                t["hC"], t["ya"], t["yb"], t["yc"]))
    w("  obtain ⟨" + ", ".join("tr{}".format(i) for i in range(len(W3_C))) + "⟩ := htri")
    w("  refine AEnum_eq_zero ?_")
    w("  rintro ⟨xx, zz⟩ hP")
    w("  have hle : SS.hammingWt xx ≤ 3 := by")
    w("    have h1 := hammingWt_x_le_wt (SS.PauliString.mk xx zz)")
    w("    rw [hP] at h1")
    w("    exact h1")
    w("  rcases masks3 xx hle with hin | ⟨e0, e1⟩")
    w("  · simp only [gm3, Finset.mem_insert, Finset.mem_singleton] at hin")
    allmasks = list(GM3)
    w("    rcases hin with " + " | ".join(["h"] * len(allmasks)))
    for f in allmasks:
        nm = mnm(f)
        extra = ""
        if f in TRI_HYP:
            extra = " tr{}".format([g for g, _ in W3_C].index(f))
        w("    · subst h")
        w("      exact a3_{} c d hc hd tau htf{} zz hP".format(nm, extra))
    w("  · exact projTrace_no_incidence hc hd e0 e1")
    w()


def emit_final():
    w("/-! ## 12.  The unique enumerator -/")
    w()
    w("set_option maxHeartbeats 3200000 in")
    w("/-- **The unique Shor--Laflamme weight enumerator on orbit 36.**")
    w()
    w("The first four coefficients are *derived*: the only inputs are the two support")
    w("conditions, one `MomentSystem`, and twenty-two vanishing Knill--Laflamme rows.")
    w("The remaining three are read off from the quantum MacWilliams normal form of a")
    w("`((6,2,3))` code, which enters as the three displayed hypotheses `hmw4, hmw5,")
    w("`hmw6` -- exactly Eq. (o36MacWilliamsnormalform) of the chapter.  That relation")
    w("holds for every `((6,2,3))` code and is *not* proved here. -/")
    w("theorem unique_enumerator (c d : SS.BitString 6 -> ℂ)")
    w(SUPPORT_HYP)
    w(MOMENT_HYP)
    w(ROWS_HYP)
    w(EX16_HYP)
    w("    (A4 A5 A6 : ℝ)")
    w("    (hmw4 : A4 = 15 - 4 * AEnum c d 2 - 3 * AEnum c d 3)")
    w("    (hmw5 : A5 = 12 + 3 * AEnum c d 1 + 4 * AEnum c d 2 + 3 * AEnum c d 3)")
    w("    (hmw6 : A6 = 4 - 4 * AEnum c d 1 - AEnum c d 2 - AEnum c d 3) :")
    w("    AEnum c d 0 = 1 ∧ AEnum c d 1 = 0 ∧ AEnum c d 2 = 21/25 ∧ AEnum c d 3 = 0")
    w("      ∧ A4 = 291/25 ∧ A5 = 384/25 ∧ A6 = 79/25 := by")
    w("  have h0 : AEnum c d 0 = 1 := A0_value c d hc hd hm " + ROWS_ARGS)
    w("  have h1 : AEnum c d 1 = 0 := A1_eq_zero c d hc hd hm")
    w("  have h2 : AEnum c d 2 = 21/25 := A2_value c d hc hd hm " + ROWS_ARGS + " ho21")
    w("  have h3 : AEnum c d 3 = 0 := A3_value c d hc hd hm " + ROWS_ARGS + " ho21")
    w("  refine ⟨h0, h1, h2, h3, ?_, ?_, ?_⟩")
    w("  · rw [hmw4, h2, h3]; norm_num")
    w("  · rw [hmw5, h1, h2, h3]; norm_num")
    w("  · rw [hmw6, h1, h2, h3]; norm_num")
    w()
    w("/-- The same closure performed over `ℚ` by")
    w("`Orbit36Phase.macwilliams_normal_form`, which is the shape the chapter states. -/")
    w("theorem unique_enumerator_rat :")
    w("    (1 : ℚ) = 1 ∧ (0 : ℚ) = 0 ∧ (21/25 : ℚ) = 21/25 ∧ (0 : ℚ) = 0")
    w("      ∧ (15 - 4 * (21/25 : ℚ) - 3 * 0 : ℚ) = 291/25")
    w("      ∧ (12 + 3 * (0 : ℚ) + 4 * (21/25) + 3 * 0 : ℚ) = 384/25")
    w("      ∧ (4 - 4 * (0 : ℚ) - 21/25 - 0 : ℚ) = 79/25 :=")
    w("  macwilliams_normal_form 1 0 (21/25) 0 (15 - 4 * (21/25) - 3 * 0)")
    w("    (12 + 3 * 0 + 4 * (21/25) + 3 * 0) (4 - 4 * 0 - 21/25 - 0)")
    w("    rfl rfl rfl rfl rfl rfl rfl")
    w()


def main():
    w(HEADER.rstrip("\n"))
    w(HELPERS)
    emit_colouring()
    emit_bits()
    emit_topform()
    emit_incidences()
    emit_a3_masks()
    emit_diag_values()
    info = emit_edge_values()
    emit_enumerator(info)
    emit_final()
    w("end")
    w()
    w("end SixQubit.Orbit36Enum")
    path = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..",
                                        "SixQubit", "Orbit36Enum.lean"))
    with io.open(path, "w", encoding="utf-8", newline="\n") as fh:
        fh.write("\n".join(OUT) + "\n")
    print("wrote", path, len(OUT), "lines")


if __name__ == "__main__":
    main()
