"""Generator for SixQubit/Orbit36Enum4.lean.

Closes the last conditional gap of the orbit-36 chapter: the Shor--Laflamme
coefficients A_4, A_5 and A_6 of an arbitrary exact orbit-36 solution, computed
directly (no MacWilliams hypothesis).

The mathematics
---------------
Write S0 = {y_0, ..., y_11} for the bottom fiber and S1 = complement S0.  For a
Pauli (f, zz) the projector trace splits as

    Tr (E Pi) = i^{#Y} * (B + T),

where B runs over the pairs {j, k} of S0 with y_j xor y_k = f and T over the
mirrored pairs of S1.  The antiunitary normal form `TopForm` turns each top
product into (conj tau * tau) times the conjugate of the corresponding bottom
product, with a sign eps_j eps_k that is +1 unless exactly one of j, k is an
anchor (y_0 or y_1).  That sign is CONSTANT on every incident mask, so writing

    e_f  = eps_j eps_k,   q = zz . f,   P = zz . 1^6,

one finds  T = e_f (-1)^{q+P} B, hence

    Tr (E Pi) = 0                                   if e_f != (-1)^{q+P},
    Tr (E Pi) = i^{#Y} * 2 * (E + (-1)^q conj E)    otherwise,

with E = sum over pairs of (-1)^{zz . y_k} conj(c y_j) c y_k.  Since the Pauli
weight is |f| + |zz outside f| and q + P = |zz outside f| mod 2, the liveness
test depends only on the weight: a mask f contributes to weight w exactly when
(-1)^{w - |f|} = e_f.  This is the parametric lemma `pv...` (live) and `zv...`
(dead) generated below, one per incident mask.

Everything else is bookkeeping: for each (mask, weight) the admissible dressings
are enumerated, each contributes 4 * normSq (E +- conj E), and the sum collapses
through `normSq_split` onto normSq of the four sign patterns of E.  Only two
inputs beyond the forced magnitudes are needed: the edge identity
3 G = conj(r_W) r_V on the six K_4 masks (weights 4 and 6) and the triangle
identity G = 0 on the four exceptional masks (weight 5).
"""

import itertools
from fractions import Fraction as F

# ----------------------------------------------------------------- fiber data

def bs(*b):
    return tuple(b)

Y = [
    bs(0, 0, 0, 0, 0, 0),   # y0  u
    bs(0, 0, 0, 0, 1, 1),   # y1  v
    bs(0, 1, 1, 1, 1, 0),   # y2  s1
    bs(1, 0, 1, 1, 1, 0),   # y3  s2
    bs(1, 1, 0, 1, 1, 0),   # y4  s3
    bs(1, 1, 1, 0, 1, 0),   # y5  s4
    bs(1, 1, 0, 0, 0, 1),   # y6  e12
    bs(1, 0, 1, 0, 0, 1),   # y7  e13
    bs(1, 0, 0, 1, 0, 1),   # y8  e14
    bs(0, 1, 1, 0, 0, 1),   # y9  e23
    bs(0, 1, 0, 1, 0, 1),   # y10 e24
    bs(0, 0, 1, 1, 0, 1),   # y11 e34
]
EPS = [1, 1] + [-1] * 10
QQ = [F(1, 10)] * 6 + [F(1, 15)] * 6
ONES = (1, 1, 1, 1, 1, 1)
MASKS = [tuple(t) for t in itertools.product([0, 1], repeat=6)]


def xr(a, b):
    return tuple(x ^ y for x, y in zip(a, b))


def wt(a):
    return sum(a)


def dot(a, b):
    return sum(x * y for x, y in zip(a, b)) % 2


def nm(f):
    return "".join(map(str, f))


def pwt(f, zz):
    return len(set(i for i in range(6) if f[i] or zz[i]))


EXISTING_BT = {
    '000000', '000001', '000010', '000011', '000100', '000101', '000110',
    '000111', '001000', '001001', '001010', '001011', '001100', '001101',
    '001110', '010000', '010001', '010010', '010011', '010100', '010101',
    '010110', '011000', '011001', '011010', '100000', '100001', '100010',
    '100011', '100100', '100101', '100110', '101000', '101001', '101010',
    '110000', '110001', '110010',
}
EXISTING_SPLIT = {
    '000000', '110000', '101000', '100100', '011000', '010100', '001100',
    '000011', '001101', '001110', '010101', '010110', '011001', '011010',
    '100101', '100110', '101001', '101010', '110001', '110010', '000111',
    '001011', '010011', '100011',
}

# orientation: mask -> [(j, k)] with X = star (c y_j) * c y_k, base bool = y_k
ORI = {
    '110000': [(3, 2), (7, 9), (8, 10)],
    '101000': [(4, 2), (6, 9), (8, 11)],
    '100100': [(5, 2), (6, 10), (7, 11)],
    '011000': [(4, 3), (6, 7), (10, 11)],
    '010100': [(5, 3), (6, 8), (9, 11)],
    '001100': [(5, 4), (7, 8), (9, 10)],
    '000011': [(1, 0)],
    '000111': [(2, 9), (3, 7), (4, 6)],
    '001011': [(2, 10), (3, 8), (5, 6)],
    '010011': [(2, 11), (4, 8), (5, 7)],
    '100011': [(3, 11), (4, 10), (5, 9)],
    '111100': [(6, 11), (7, 10), (8, 9)],
    '011111': [(3, 6), (4, 7), (5, 8)],
    '101111': [(2, 6), (4, 9), (5, 10)],
    '110111': [(2, 7), (3, 9), (5, 11)],
    '111011': [(2, 8), (3, 10), (4, 11)],
}
for _k in range(2, 12):
    ORI[nm(Y[_k])] = [(0, _k)]
    ORI[nm(xr(Y[1], Y[_k]))] = [(1, _k)]

# sanity: the orientation table lists exactly the incident nontrivial masks
_INC = {}
for _f in MASKS:
    _p = [(j, k) for j in range(12) for k in range(j + 1, 12) if xr(Y[j], Y[k]) == _f]
    if _p and _f != tuple([0] * 6):
        _INC[nm(_f)] = _p
assert set(_INC) == set(ORI), (set(_INC) ^ set(ORI))
for _f, _p in _INC.items():
    assert sorted(tuple(sorted(t)) for t in ORI[_f]) == sorted(_p), _f
    _es = {EPS[j] * EPS[k] for (j, k) in _p}
    assert len(_es) == 1, _f

MASK_ORDER = (
    ['000000', '000011']
    + ['110000', '101000', '100100', '011000', '010100', '001100']
    + ['110001', '110010', '101001', '101010', '100101', '100110',
       '011001', '011010', '010101', '010110', '001101', '001110']
    + ['000111', '001011', '010011', '100011']
    + ['011110', '011101', '101110', '101101', '110110', '110101',
       '111010', '111001']
    + ['111100']
    + ['011111', '101111', '110111', '111011']
)
assert len(MASK_ORDER) == 37
assert set(MASK_ORDER) == set(ORI) | {'000000'}


def efac(f):
    p = ORI[f][0]
    return EPS[p[0]] * EPS[p[1]]


def incidence(f):
    """Ordered incidence list: for each pair, the base index then its partner."""
    out = []
    for (j, k) in ORI[f]:
        out.append(k)
        out.append(j)
    return out


def partner(f, i):
    ft = tuple(int(ch) for ch in f)
    for t in range(12):
        if xr(Y[t], ft) == Y[i]:
            return t
    raise ValueError


def dressings(f, w):
    ft = tuple(int(ch) for ch in f)
    return [zz for zz in MASKS if pwt(ft, zz) == w]


def live(f, w):
    return (-1) ** (w - wt(tuple(int(ch) for ch in f))) == efac(f)


# ------------------------------------------------------------------- emitters

L = []


def out(s=""):
    L.append(s)


def cy(i):
    return "c y%d" % i


def dz(i):
    return "d z%d" % i


def Xexp(j, k):
    return "star (c y%d) * c y%d" % (j, k)


def Xsexp(j, k):
    return "c y%d * star (c y%d)" % (j, k)


def signed_sum(terms):
    """terms: list of (sign, string) -> 'a - b + c' with the first sign folded."""
    s = ""
    for i, (sg, t) in enumerate(terms):
        if i == 0:
            s = t if sg > 0 else "-(%s)" % t
        else:
            s += (" + " if sg > 0 else " - ") + t
    return s


def pattern_expr(f, signs, starred):
    pr = ORI[f]
    terms = []
    for idx, (j, k) in enumerate(pr):
        terms.append((signs[idx], Xsexp(j, k) if starred else Xexp(j, k)))
    return signed_sum(terms)


def frac(x):
    x = F(x)
    if x.denominator == 1:
        return str(x.numerator)
    return "%d/%d" % (x.numerator, x.denominator)


# ------------------------------------------------------------------- preamble

out("""import Mathlib

import SS.FullKL
import SS.HilbertKL
import SixQubit.Common
import SixQubit.K4Kernel
import SixQubit.Orbit36
import SixQubit.Orbit36Phase
import SixQubit.Orbit36Enum

/-!
# The unconditional Shor--Laflamme enumerator of orbit 36

`SixQubit.Orbit36Enum` evaluates `A_0, ..., A_3` for an arbitrary exact orbit-36
solution and then *assumes* the quantum MacWilliams normal form to reach
`A_4, A_5, A_6`.  This module removes that assumption: it computes the three
remaining coefficients the same way, directly from the forced magnitudes, the
edge three-colouring and the antiunitary normal form.  The outcome is the
unconditional

    (A_0, ..., A_6) = (1, 0, 21/25, 0, 291/25, 384/25, 79/25).

## The mechanism

For a Pauli `(f, zz)` the projector trace splits over the pairs `{j, k}` of the
bottom fiber with `y_j xor y_k = f` and over the mirrored pairs of the top
fiber.  `TopForm` turns every top product into `conj tau * tau` times the
conjugate of the matching bottom product, times the sign `eps_j eps_k`, which is
`+1` unless exactly one of `j, k` is an anchor (`y_0` or `y_1`).  That sign is
constant on each incident mask, so with `q = zz . f` and `P = zz . 1^6`

    T = e_f * (-1)^(q + P) * B,

and therefore

* `Tr (E Pi) = 0` when `e_f != (-1)^(q+P)`  (`zv...` below), and
* `Tr (E Pi) = i^{#Y} * 2 * (E + (-1)^q conj E)` otherwise (`pv...` below),

where `E = sum over pairs of (-1)^(zz . y_k) conj (c y_j) (c y_k)`.  Because the
Pauli weight is `|f|` plus the number of `zz`-bits outside `f`, and `q + P` is
that same number mod two, a mask contributes to weight `w` exactly when
`(-1)^(w - |f|) = e_f`.  Each live dressing contributes
`4 * normSq (E +- conj E)`, and `normSq_split` collapses the dressings of a mask
in pairs onto `normSq` of the sign patterns of `E`.

Only two facts beyond the forced magnitudes enter: the edge identity
`3 G = conj (r_W) r_V` on the six `K_4` masks (used at weights four and six) and
the triangle identity `G = 0` on the four exceptional masks (weight five).  Both
are already proved in `SixQubit.Orbit36Enum` / `SixQubit.Orbit36Phase`; the
first is repackaged here as `edges_eq_of_colouring`.

Hypotheses are exactly those of `Orbit36Enum.A2_value`: the two support
conditions, one `MomentSystem`, and twenty-two vanishing Knill--Laflamme rows.

This file is generated by `tools/generators/gen36enum4.py`.
-/

namespace SixQubit.Orbit36Enum4

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

open SixQubit.K4Kernel (rho rho_quadratic rho_pow_three)
open SixQubit.Orbit36
open SixQubit.Orbit36Phase
open SixQubit.Orbit36Enum

set_option maxRecDepth 40000
set_option maxHeartbeats 1600000

/-! ## 1.  Sign bookkeeping and normSq algebra -/

/-- `(-1)^b` as a complex unit, so that Walsh signs become ring elements. -/
def sgn (b : Bool) : ℂ := if b then -1 else 1

theorem signC_eq (b : Bool) (t : ℂ) : SS.signC b t = sgn b * t := by
  cases b <;> simp [sgn, SS.signC]

theorem sgn_xor (a b : Bool) : sgn (xor a b) = sgn a * sgn b := by
  cases a <;> cases b <;> simp [sgn]

theorem sgn_not (b : Bool) : sgn (!b) = -sgn b := by
  cases b <;> simp [sgn]

theorem sgn_true : sgn true = -1 := rfl

theorem sgn_false : sgn false = 1 := rfl

theorem sgn_sq (b : Bool) : sgn b * sgn b = 1 := by
  cases b <;> simp [sgn]

/-- The parallelogram law. -/
theorem nsq_par (t u : ℂ) :
    Complex.normSq (t + u) + Complex.normSq (t - u)
      = 2 * Complex.normSq t + 2 * Complex.normSq u := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im]
  ring

/-- The four sign patterns of a three-term sum. -/
theorem nsq_four (a b e : ℂ) :
    Complex.normSq (a + b + e) + Complex.normSq (a + b - e)
      + Complex.normSq (a - b + e) + Complex.normSq (a - b - e)
      = 4 * (Complex.normSq a + Complex.normSq b + Complex.normSq e) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im]
  ring

/-- `3 t = 5 u` scales the modulus by `25/9`. -/
theorem nsq3_5 {t u : ℂ} (h : 3 * t = 5 * u) (hu : Complex.normSq u = 1/100) :
    Complex.normSq t = 25/900 := by
  have e1 : Complex.normSq (3 * t) = Complex.normSq (5 * u) := by rw [h]
  rw [map_mul, map_mul, hu] at e1
  have h3 : Complex.normSq (3 : ℂ) = 9 := by norm_num [Complex.normSq_apply]
  have h5 : Complex.normSq (5 : ℂ) = 25 := by norm_num [Complex.normSq_apply]
  rw [h3, h5] at e1
  linarith

/-- `3 t = -(2 u)` scales the modulus by `4/9`. -/
theorem nsq3_2 {t u : ℂ} (h : 3 * t = -(2 * u)) (hu : Complex.normSq u = 1/100) :
    Complex.normSq t = 4/900 := by
  have e1 : Complex.normSq (3 * t) = Complex.normSq (-(2 * u)) := by rw [h]
  rw [Complex.normSq_neg, map_mul, map_mul, hu] at e1
  have h3 : Complex.normSq (3 : ℂ) = 9 := by norm_num [Complex.normSq_apply]
  have h2 : Complex.normSq (2 : ℂ) = 4 := by norm_num [Complex.normSq_apply]
  rw [h3, h2] at e1
  linarith

/-- `t = 2 u` scales the modulus by `4`. -/
theorem nsq_dbl {t u : ℂ} (h : t = 2 * u) :
    Complex.normSq t = 4 * Complex.normSq u := by
  rw [h, map_mul]
  norm_num [Complex.normSq_apply]

/-- `t = -(2 u)` scales the modulus by `4`. -/
theorem nsq_dbl_neg {t u : ℂ} (h : t = -(2 * u)) :
    Complex.normSq t = 4 * Complex.normSq u := by
  rw [h, Complex.normSq_neg, map_mul]
  norm_num [Complex.normSq_apply]

/-! ## 2.  The remaining flip masks -/
""")

# ------------------------------------------------------- new bt definitions
new_bt = [nm(f) for f in MASKS if nm(f) not in EXISTING_BT]
for s in new_bt:
    out("def bt%s : SS.BitString 6 := bs %s"
        % (s, " ".join("true" if ch == '1' else "false" for ch in s)))
out()

out("""/-! ## 3.  The projector trace of the thirteen remaining incident masks -/
""")

for f in MASK_ORDER:
    if f in EXISTING_SPLIT:
        continue
    ft = tuple(int(ch) for ch in f)
    inc = incidence(f)
    out("theorem incB_mk%s : S0.filter (fun s => SS.bxor s bt%s ∈ S0) = {%s} := by decide"
        % (f, f, ", ".join("y%d" % i for i in inc)))
    out("theorem incT_mk%s : S1.filter (fun s => SS.bxor s bt%s ∈ S1) = {%s} := by decide"
        % (f, f, ", ".join("z%d" % i for i in inc)))
    for i in inc:
        out("theorem flB_mk%s_%d : SS.bxor y%d bt%s = y%d := by decide"
            % (f, i, i, f, partner(f, i)))
        out("theorem flT_mk%s_%d : SS.bxor z%d bt%s = z%d := by decide"
            % (f, i, i, f, partner(f, i)))
    out()
    bot = ""
    top = ""
    for t, i in enumerate(inc):
        p = partner(f, i)
        bb = "SS.signC (SS.bdot zz y%d) (star (c y%d) * c y%d)" % (i, p, i)
        tt = "SS.signC (SS.bdot zz z%d) (star (d z%d) * d z%d)" % (i, p, i)
        if t == 0:
            bot, top = bb, tt
        else:
            bot += " + (" + bb
            top += " + (" + tt
    bot += ")" * (len(inc) - 1)
    top += ")" * (len(inc) - 1)
    out("/-- The projector trace of every Pauli with flip mask `%s`, as a bottom" % f)
    out("bracket and a top bracket over the incidences of that mask. -/")
    out("theorem split_mk%s (c d : SS.BitString 6 -> ℂ)" % f)
    out("    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)")
    out("    (zz : SS.BitString 6) :")
    out("    projTrace c d ⟨bt%s, zz⟩" % f)
    out("      = Complex.I ^ (SS.PauliString.mk bt%s zz).numY" % f)
    out("          * (%s)" % bot)
    out("        + Complex.I ^ (SS.PauliString.mk bt%s zz).numY" % f)
    out("          * (%s) := by" % top)
    out("  rw [projTrace, SS.innerC_pauliAct_support S0 S0 c c _ hc hc,")
    out("    SS.innerC_pauliAct_support S1 S1 d d _ hd hd]")
    out("  rw [show (SS.PauliString.mk bt%s zz).x = bt%s from rfl, incB_mk%s, incT_mk%s]"
        % (f, f, f, f))
    ins = ", ".join(["Finset.sum_insert (by decide)"] * (len(inc) - 1) + ["Finset.sum_singleton"])
    out("  rw [%s," % ins)
    out("    %s]" % ins)
    out("  rw [show (SS.PauliString.mk bt%s zz).z = zz from rfl]" % f)
    out("  rw [%s]" % ", ".join(["flB_mk%s_%d" % (f, i) for i in inc]
                                + ["flT_mk%s_%d" % (f, i) for i in inc]))
    out()

out("""/-! ## 4.  The edge identity, in equation form -/

/-- **`3 G = conj (r_W) r_V` on all six `K_4` edges.**  This is
`Orbit36Enum.edges_of_colouring` with the intermediate equation of
`Orbit36Enum.edge_G` kept instead of its modulus; weights four and six need the
equation, not just `normSq G = 1/900`. -/
theorem edges_eq_of_colouring {r1 r2 r3 r4 c12 c13 c14 c23 c24 c34 mu w : ℂ}
    (hw : w ^ 2 + w + 1 = 0) (hs : star w = w ^ 2)
    (p1 : Complex.normSq r1 = 1/10) (p2 : Complex.normSq r2 = 1/10)
    (p3 : Complex.normSq r3 = 1/10) (p4 : Complex.normSq r4 = 1/10)
    (hmu : Complex.normSq mu = 1/1500)
    (n1 : r1 ≠ 0) (n2 : r2 ≠ 0) (n3 : r3 ≠ 0) (n4 : r4 ≠ 0)
    (h12 : r1 * r2 * c12 = mu) (h34 : r3 * r4 * c34 = mu)
    (h13 : r1 * r3 * c13 = w * mu) (h24 : r2 * r4 * c24 = w * mu)
    (h14 : r1 * r4 * c14 = w ^ 2 * mu) (h23 : r2 * r3 * c23 = w ^ 2 * mu) :
    3 * (star r2 * r1 + star c13 * c23 + star c14 * c24) = star r2 * r1
      ∧ 3 * (star r3 * r1 + star c12 * c23 + star c14 * c34) = star r3 * r1
      ∧ 3 * (star r4 * r1 + star c12 * c24 + star c13 * c34) = star r4 * r1
      ∧ 3 * (star r3 * r2 + star c12 * c13 + star c24 * c34) = star r3 * r2
      ∧ 3 * (star r4 * r2 + star c12 * c14 + star c23 * c34) = star r4 * r2
      ∧ 3 * (star r4 * r3 + star c13 * c14 + star c23 * c24) = star r4 * r3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hcross : star (r1 * r3 * c13) * (r2 * r3 * c23)
        + star (r1 * r4 * c14) * (r2 * r4 * c24) = -(1/1500 : ℂ) := by
      rw [h13, h23, h14, h24, colourPair_12 hw hs, SixQubit.star_mul_self, hmu]
      norm_num
    exact edge_G p1 p2 p3 p4 hcross n1 n2
  · have hcross : star (r1 * r2 * c12) * (r3 * r2 * c23)
        + star (r1 * r4 * c14) * (r3 * r4 * c34) = -(1/1500 : ℂ) := by
      rw [h12, show r3 * r2 * c23 = w ^ 2 * mu by linear_combination h23, h14, h34,
        colourPair_02 hw hs, SixQubit.star_mul_self, hmu]
      norm_num
    exact edge_G p1 p3 p2 p4 hcross n1 n3
  · have hcross : star (r1 * r2 * c12) * (r4 * r2 * c24)
        + star (r1 * r3 * c13) * (r4 * r3 * c34) = -(1/1500 : ℂ) := by
      rw [h12, show r4 * r2 * c24 = w * mu by linear_combination h24, h13,
        show r4 * r3 * c34 = mu by linear_combination h34,
        colourPair_01 hw hs, SixQubit.star_mul_self, hmu]
      norm_num
    exact edge_G p1 p4 p2 p3 hcross n1 n4
  · have hcross : star (r2 * r1 * c12) * (r3 * r1 * c13)
        + star (r2 * r4 * c24) * (r3 * r4 * c34) = -(1/1500 : ℂ) := by
      rw [show r2 * r1 * c12 = mu by linear_combination h12,
        show r3 * r1 * c13 = w * mu by linear_combination h13, h24, h34,
        colourPair_01 hw hs, SixQubit.star_mul_self, hmu]
      norm_num
    exact edge_G p2 p3 p1 p4 hcross n2 n3
  · have hcross : star (r2 * r1 * c12) * (r4 * r1 * c14)
        + star (r2 * r3 * c23) * (r4 * r3 * c34) = -(1/1500 : ℂ) := by
      rw [show r2 * r1 * c12 = mu by linear_combination h12,
        show r4 * r1 * c14 = w ^ 2 * mu by linear_combination h14, h23,
        show r4 * r3 * c34 = mu by linear_combination h34,
        colourPair_02 hw hs, SixQubit.star_mul_self, hmu]
      norm_num
    exact edge_G p2 p4 p1 p3 hcross n2 n4
  · have hcross : star (r3 * r1 * c13) * (r4 * r1 * c14)
        + star (r3 * r2 * c23) * (r4 * r2 * c24) = -(1/1500 : ℂ) := by
      rw [show r3 * r1 * c13 = w * mu by linear_combination h13,
        show r4 * r1 * c14 = w ^ 2 * mu by linear_combination h14,
        show r3 * r2 * c23 = w ^ 2 * mu by linear_combination h23,
        show r4 * r2 * c24 = w * mu by linear_combination h24,
        colourPair_12 hw hs, SixQubit.star_mul_self, hmu]
      norm_num
    exact edge_G p3 p4 p1 p2 hcross n3 n4

/-! ## 5.  The Walsh-sign relations and the parametric projector traces -/
""")


# ------------------------------------------------- rel / pv / zv per mask
def emit_mask_lemmas(f):
    ft = tuple(int(ch) for ch in f)
    pr = ORI[f]
    ef = efac(f)
    conj_rel = []
    for (j, k) in pr:
        conj_rel.append("SS.bdot zz y%d = xor (SS.bdot zz y%d) (SS.bdot zz bt%s)" % (j, k, f))
    for (j, k) in pr:
        conj_rel.append("SS.bdot zz z%d = xor (SS.bdot zz y%d) (SS.bdot zz (SS.ones 6))"
                        % (k, k))
        conj_rel.append("SS.bdot zz z%d = xor (xor (SS.bdot zz y%d) (SS.bdot zz bt%s)) "
                        "(SS.bdot zz (SS.ones 6))" % (j, k, f))
    out("theorem rel_mk%s : ∀ zz : SS.BitString 6," % f)
    for t, s in enumerate(conj_rel):
        out(("    " if t == 0 else "  ∧ ") + s)
    out("    := by decide")
    out()

    Eexp = " + ".join("sgn (SS.bdot zz y%d) * (%s)" % (k, Xexp(j, k)) for (j, k) in pr)
    EexpC = " + ".join("SS.signC (SS.bdot zz y%d) (%s)" % (k, Xexp(j, k)) for (j, k) in pr)
    EsexpC = " + ".join("SS.signC (SS.bdot zz y%d) (%s)" % (k, Xsexp(j, k)) for (j, k) in pr)
    ipow = "Complex.I ^ (SS.PauliString.mk bt%s zz).numY" % f
    hyp_live = ("SS.bdot zz (SS.ones 6) = SS.bdot zz bt%s" % f if ef == 1
                else "SS.bdot zz (SS.ones 6) = !(SS.bdot zz bt%s)" % f)
    hyp_dead = ("SS.bdot zz (SS.ones 6) = !(SS.bdot zz bt%s)" % f if ef == 1
                else "SS.bdot zz (SS.ones 6) = SS.bdot zz bt%s" % f)
    names = ", ".join("q%d" % t for t in range(len(conj_rel)))
    inc = incidence(f)
    ulist = ", ".join("u%d" % i for i in inc)

    def emit_u(indent):
        for i in inc:
            p = partner(f, i)
            sgp = 1 if p <= 1 else -1
            sgi = 1 if i <= 1 else -1
            body = "c y%d * star (c y%d)" % (p, i)
            tgt = body if sgp * sgi == 1 else "-(%s)" % body
            coef = body if sgp * sgi == 1 else "-(%s)" % body
            st = (["star_neg"] if sgp == -1 else []) + ["star_mul'", "star_star"]
            out(indent + "have u%d : star (d z%d) * d z%d = %s := by" % (i, p, i, tgt))
            out(indent + "  rw [htf.t%d, htf.t%d]" % (p, i))
            out(indent + "  simp only [%s]" % ", ".join(st))
            out(indent + "  linear_combination (%s) * htf.unit" % coef)

    for tag, hyp, sgnfac in (("pv", hyp_live, 1), ("zv", hyp_dead, -1)):
        simpset = "signC_eq, sgn_xor" + (", sgn_not" if "!" in hyp else "")
        out("/-- The %s projector traces of the flip mask `%s`. -/"
            % ("live" if tag == "pv" else "dead", f))
        out("theorem %s%s (c d : SS.BitString 6 -> ℂ)" % (tag, f))
        out("    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)")
        out("    (tau : ℂ) (htf : TopForm c d tau) (zz : SS.BitString 6)")
        out("    (hl : %s) :" % hyp)
        if tag == "pv":
            out("    projTrace c d ⟨bt%s, zz⟩" % f)
            out("      = %s" % ipow)
            out("        * (2 * ((%s)" % EexpC)
            out("            + SS.signC (SS.bdot zz bt%s) (%s))) := by" % (f, EsexpC))
        else:
            out("    projTrace c d ⟨bt%s, zz⟩ = 0 := by" % f)
        out("  obtain ⟨%s⟩ := rel_mk%s zz" % (names, f))
        emit_u("  ")
        out("  rw [split_mk%s c d hc hd zz, %s," % (f, ulist))
        out("    %s, hl]" % names)
        out("  simp only [%s]" % simpset)
        if sgnfac == 1:
            out("  linear_combination (%s * (%s)) * sgn_sq (SS.bdot zz bt%s)"
                % (ipow, Eexp, f))
        else:
            out("  linear_combination (-(%s * (%s))) * sgn_sq (SS.bdot zz bt%s)"
                % (ipow, Eexp, f))
        out()


# diagonal
out("theorem rel_mk000000 : ∀ zz : SS.BitString 6,")
for i in range(12):
    out(("    " if i == 0 else "  ∧ ")
        + "SS.bdot zz z%d = xor (SS.bdot zz y%d) (SS.bdot zz (SS.ones 6))" % (i, i))
out("    := by decide")
out()
_diagE = " + ".join("sgn (SS.bdot zz y%d) * (star (c y%d) * c y%d)" % (i, i, i)
                    for i in range(12))
_diagEC = " + ".join("SS.signC (SS.bdot zz y%d) (star (c y%d) * c y%d)" % (i, i, i)
                     for i in range(12))
_dnames = ", ".join("q%d" % i for i in range(12))
_dipow = "Complex.I ^ (SS.PauliString.mk bt000000 zz).numY"
_dulist = ", ".join("u%d" % i for i in range(12))


def emit_diag_u():
    for i in range(12):
        st = (["star_neg"] if i > 1 else []) + ["star_mul'", "star_star"]
        out("  have u%d : star (d z%d) * d z%d = star (c y%d) * c y%d := by"
            % (i, i, i, i, i))
        out("    rw [htf.t%d]" % i)
        out("    simp only [%s]" % ", ".join(st))
        out("    linear_combination (c y%d * star (c y%d)) * htf.unit" % (i, i))


out("/-- The even diagonal projector traces. -/")
out("theorem pv000000 (c d : SS.BitString 6 -> ℂ)")
out("    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)")
out("    (tau : ℂ) (htf : TopForm c d tau) (zz : SS.BitString 6)")
out("    (hl : SS.bdot zz (SS.ones 6) = false) :")
out("    projTrace c d ⟨bt000000, zz⟩")
out("      = %s * (2 * (%s)) := by" % (_dipow, _diagEC))
out("  obtain ⟨%s⟩ := rel_mk000000 zz" % _dnames)
emit_diag_u()
out("  rw [split_mk000000 c d hc hd zz, %s," % _dulist)
out("    %s, hl]" % _dnames)
out("  simp only [signC_eq, Bool.xor_false]")
out("  ring")
out()
out("/-- The odd diagonal projector traces vanish. -/")
out("theorem zv000000 (c d : SS.BitString 6 -> ℂ)")
out("    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)")
out("    (tau : ℂ) (htf : TopForm c d tau) (zz : SS.BitString 6)")
out("    (hl : SS.bdot zz (SS.ones 6) = true) :")
out("    projTrace c d ⟨bt000000, zz⟩ = 0 := by")
out("  obtain ⟨%s⟩ := rel_mk000000 zz" % _dnames)
emit_diag_u()
out("  rw [split_mk000000 c d hc hd zz, %s," % _dulist)
out("    %s, hl]" % _dnames)
out("  simp only [signC_eq, Bool.xor_true, sgn_not]")
out("  ring")
out()

for f in MASK_ORDER:
    if f == '000000':
        continue
    emit_mask_lemmas(f)

# ---------------------------------------------------------- the mask index
out("""/-! ## 6.  The masks that are incident on the fibers -/

/-- The thirty-seven flip masks that join two points of a fiber (the trivial mask
included).  Every other mask has no incidence at all. -/""")
out("def gm : Finset (SS.BitString 6) :=")
out("  {%s}" % ", ".join("bt" + f for f in MASK_ORDER))
out()
out("theorem masksG : ∀ f : SS.BitString 6, f ∈ gm")
out("    ∨ (S0.filter (fun s => SS.bxor s f ∈ S0) = ∅")
out("        ∧ S1.filter (fun s => SS.bxor s f ∈ S1) = ∅) := by decide")
out()

out("/-! ## 7.  The inner sums, one flip mask and one weight at a time -/")
out()

# --------------------------------------------------- inner sums per (mask, w)
HINS = {}


def emit_inner(f, w):
    ft = tuple(int(ch) for ch in f)
    ds = dressings(f, w)
    name = "w%d_%s" % (w, f)
    hyp = []
    args = []

    if not ds:
        out("theorem %s (c d : SS.BitString 6 -> ℂ) :" % name)
        out("    (∑ zz : SS.BitString 6, if (SS.PauliString.mk bt%s zz).wt = %d" % (f, w))
        out("        then Complex.normSq (projTrace c d ⟨bt%s, zz⟩) else 0) = 0 := by" % f)
        out("  refine Finset.sum_eq_zero (fun zz _ => ?_)")
        out("  rw [if_neg (nod_%s zz)]" % name)
        out()
        HINS[(f, w)] = (name, [], F(0))
        return

    if f != '000000' and not live(f, w):
        ef = efac(f)
        deadstr = ("SS.bdot zz (SS.ones 6) = !(SS.bdot zz bt%s)" % f if ef == 1
                   else "SS.bdot zz (SS.ones 6) = SS.bdot zz bt%s" % f)
        out("theorem dead_%s : ∀ zz : SS.BitString 6," % name)
        out("    (SS.PauliString.mk bt%s zz).wt = %d → %s := by decide" % (f, w, deadstr))
        out()
        out("theorem %s (c d : SS.BitString 6 -> ℂ)" % name)
        out("    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)")
        out("    (tau : ℂ) (htf : TopForm c d tau) :")
        out("    (∑ zz : SS.BitString 6, if (SS.PauliString.mk bt%s zz).wt = %d" % (f, w))
        out("        then Complex.normSq (projTrace c d ⟨bt%s, zz⟩) else 0) = 0 := by" % f)
        out("  refine Finset.sum_eq_zero (fun zz _ => ?_)")
        out("  by_cases hw : (SS.PauliString.mk bt%s zz).wt = %d" % (f, w))
        out("  · rw [if_pos hw, zv%s c d hc hd tau htf zz (dead_%s zz hw), "
            "Complex.normSq_zero]" % (f, name))
        out("  · rw [if_neg hw]")
        out()
        HINS[(f, w)] = (name, ["c", "d", "hc", "hd", "tau", "htf"], F(0))
        return

    if f == '000000' and w % 2 == 1:
        out("theorem dead_%s : ∀ zz : SS.BitString 6," % name)
        out("    (SS.PauliString.mk bt000000 zz).wt = %d → "
            "SS.bdot zz (SS.ones 6) = true := by decide" % w)
        out()
        out("theorem %s (c d : SS.BitString 6 -> ℂ)" % name)
        out("    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)")
        out("    (tau : ℂ) (htf : TopForm c d tau) :")
        out("    (∑ zz : SS.BitString 6, if (SS.PauliString.mk bt000000 zz).wt = %d" % w)
        out("        then Complex.normSq (projTrace c d ⟨bt000000, zz⟩) else 0) = 0 := by")
        out("  refine Finset.sum_eq_zero (fun zz _ => ?_)")
        out("  by_cases hw : (SS.PauliString.mk bt000000 zz).wt = %d" % w)
        out("  · rw [if_pos hw, zv000000 c d hc hd tau htf zz (dead_%s zz hw), "
            "Complex.normSq_zero]" % name)
        out("  · rw [if_neg hw]")
        out()
        HINS[(f, w)] = (name, ["c", "d", "hc", "hd", "tau", "htf"], F(0))
        return

    # live
    zs = "Zs%s" % name
    out("def %s : Finset (SS.BitString 6) :=" % zs)
    out("  {%s}" % ", ".join("bt" + nm(zz) for zz in ds))
    out()
    out("theorem zset_%s : ∀ zz : SS.BitString 6, zz ∉ %s →" % (name, zs))
    out("    (SS.PauliString.mk bt%s zz).wt ≠ %d := by decide" % (f, w))
    out()

    if f == '000000':
        emit_diag_inner(f, w, ds, zs, name)
    else:
        emit_pair_inner(f, w, ds, zs, name)


def emit_diag_inner(f, w, ds, zs, name):
    ks = ["k%d" % i for i in range(12)]
    out("theorem %s (c d : SS.BitString 6 -> ℂ)" % name)
    out("    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)")
    out("    (tau : ℂ) (htf : TopForm c d tau)")
    for i in range(12):
        out("    (k%d : Complex.normSq (c y%d) = %s)" % (i, i, frac(QQ[i])))
    tot = F(0)
    vals = []
    for zz in ds:
        s = sum(((-1) ** dot(zz, Y[i])) * QQ[i] for i in range(12))
        vals.append(s)
        tot += 4 * s * s
    out("    : (∑ zz : SS.BitString 6, if (SS.PauliString.mk bt000000 zz).wt = %d" % w)
    out("        then Complex.normSq (projTrace c d ⟨bt000000, zz⟩) else 0) = %s := by"
        % frac(tot))
    out("  rw [← Finset.sum_subset (Finset.subset_univ %s)" % zs)
    out("      (fun zz _ hzz => by rw [if_neg (zset_%s zz hzz)])]" % name)
    out("  simp only [%s]" % zs)
    ins = ", ".join(["Finset.sum_insert (by decide)"] * (len(ds) - 1) + ["Finset.sum_singleton"])
    out("  rw [%s]" % ins)
    for zz in ds:
        out("  rw [if_pos (by decide : (SS.PauliString.mk bt000000 bt%s).wt = %d)]"
            % (nm(zz), w))
    for t, zz in enumerate(ds):
        v = vals[t]
        out("  have e%d : Complex.normSq (projTrace c d ⟨bt000000, bt%s⟩) = %s := by"
            % (t, nm(zz), frac(4 * v * v)))
        out("    have h : projTrace c d ⟨bt000000, bt%s⟩" % nm(zz))
        out("        = Complex.I ^ (SS.PauliString.mk bt000000 bt%s).numY "
            "* (2 * ((%s : ℝ) : ℂ)) := by" % (nm(zz), frac(v)))
        out("      rw [pv000000 c d hc hd tau htf bt%s (by decide)]" % nm(zz))
        bl = [dot(zz, Y[i]) for i in range(12)]
        sc = ([" SS.signC_true"] if any(bl) else []) + ([" SS.signC_false"] if not all(bl) else [])
        out("      simp only [%s," % ", ".join(
            "show SS.bdot bt%s y%d = %s from by decide"
            % (nm(zz), i, "true" if bl[i] else "false") for i in range(12)))
        out("       %s, SixQubit.star_mul_self]" % ",".join(sc))
        out("      rw [%s]" % ", ".join("k%d" % i for i in range(12)))
        out("      push_cast")
        out("      ring")
        out("    rw [h, normSq_I_pow_mul, normSq_two_mul, Complex.normSq_ofReal]")
        out("    norm_num")
    out("  rw [%s]" % ", ".join("e%d" % t for t in range(len(ds))))
    if len(ds) > 1:
        out("  norm_num")
    out()
    HINS[(f, w)] = (name, ["c", "d", "hc", "hd", "tau", "htf"] + ks, tot)


def emit_pair_inner(f, w, ds, zs, name):
    pr = ORI[f]
    npr = len(pr)
    ef = efac(f)
    idxs = sorted({i for p in pr for i in p})
    ks = ["k%d" % i for i in idxs]
    needG = f in ('110000', '101000', '100100', '011000', '010100', '001100')
    needT = f in ('000111', '001011', '010011', '100011')

    # classify dressings
    info = []
    for zz in ds:
        q = dot(zz, tuple(int(ch) for ch in f))
        vec = [dot(zz, Y[k]) for (j, k) in pr]
        flip = (vec[0] == 1)
        canon = tuple(1 - v if flip else v for v in vec)
        signs = tuple(1 - 2 * v for v in canon)
        info.append((zz, q, signs, flip))

    patterns = sorted({s for (_, _, s, _) in info}, reverse=True)
    mult = {}
    for (_, q, s, _) in info:
        mult[(s, q)] = mult.get((s, q), 0) + 1

    out("theorem %s (c d : SS.BitString 6 -> ℂ)" % name)
    out("    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)")
    out("    (tau : ℂ) (htf : TopForm c d tau)")
    for i in idxs:
        out("    (k%d : Complex.normSq (c y%d) = %s)" % (i, i, frac(QQ[i])))
    if needG:
        out("    (hg : 3 * (%s) = %s)"
            % (" + ".join(Xexp(j, k) for (j, k) in pr), Xexp(*pr[0])))
    if needT:
        out("    (ht : %s = 0)" % " + ".join(Xexp(j, k) for (j, k) in pr))

    tot = F(0)
    for (s, q), m in mult.items():
        pass
    # value bookkeeping
    nsqval = {}
    if npr == 1:
        nsqval[patterns[0]] = QQ[pr[0][0]] * QQ[pr[0][1]]
    elif needG:
        base = QQ[pr[0][0]] * QQ[pr[0][1]]
        for p in patterns:
            if p == (1, 1, 1):
                nsqval[p] = base / 9
            elif p == (1, -1, -1):
                nsqval[p] = base * 25 / 9
            else:
                nsqval[p] = None
    elif needT:
        for p in patterns:
            if p == (1, -1, -1):
                nsqval[p] = 4 * QQ[pr[0][0]] * QQ[pr[0][1]]
            elif p == (1, -1, 1):
                nsqval[p] = 4 * QQ[pr[1][0]] * QQ[pr[1][1]]
            elif p == (1, 1, -1):
                nsqval[p] = 4 * QQ[pr[2][0]] * QQ[pr[2][1]]
            else:
                nsqval[p] = None
    else:
        for p in patterns:
            nsqval[p] = None
    for (s, q), m in mult.items():
        pass

    for p in patterns:
        m0 = mult.get((p, 0), 0)
        m1 = mult.get((p, 1), 0)
        assert m0 == m1, (f, w, p)
    # exact total
    if npr == 1:
        tot = 16 * mult[(patterns[0], 0)] * nsqval[patterns[0]]
    else:
        for p in patterns:
            v = nsqval[p]
            if v is None:
                v = None
            tot = None if v is None else tot
        # compute numerically below
        tot = F(0)
        for p in patterns:
            m = mult[(p, 0)]
            v = nsqval[p]
            if v is not None:
                tot += 16 * m * v
            else:
                tot = None
                break
        if tot is None:
            # remaining case: K_4 masks at weight four (patterns 2 and 3 paired)
            tot = F(0)
            base = QQ[pr[0][0]] * QQ[pr[0][1]]
            for p in patterns:
                m = mult[(p, 0)]
                v = nsqval[p]
                if v is not None:
                    tot += 16 * m * v
            # the two mixed patterns
            mm = [p for p in patterns if nsqval[p] is None]
            if needG:
                s23 = 2 * base + 2 * (2 * QQ[pr[1][0]] * QQ[pr[1][1]]
                                      + 2 * QQ[pr[2][0]] * QQ[pr[2][1]]
                                      - base * 4 / 9)
                assert len(mm) == 2
                assert mult[(mm[0], 0)] == mult[(mm[1], 0)]
                tot += 16 * mult[(mm[0], 0)] * s23
            else:
                assert len(mm) == 4 and not needT
                s4 = 4 * sum(QQ[j] * QQ[k] for (j, k) in pr)
                assert len({mult[(p, 0)] for p in mm}) == 1
                tot += 16 * mult[(mm[0], 0)] * s4

    out("    : (∑ zz : SS.BitString 6, if (SS.PauliString.mk bt%s zz).wt = %d" % (f, w))
    out("        then Complex.normSq (projTrace c d ⟨bt%s, zz⟩) else 0) = %s := by"
        % (f, frac(tot)))
    out("  rw [← Finset.sum_subset (Finset.subset_univ %s)" % zs)
    out("      (fun zz _ hzz => by rw [if_neg (zset_%s zz hzz)])]" % name)
    out("  simp only [%s]" % zs)
    ins = ", ".join(["Finset.sum_insert (by decide)"] * (len(ds) - 1) + ["Finset.sum_singleton"])
    out("  rw [%s]" % ins)
    for zz in ds:
        out("  rw [if_pos (by decide : (SS.PauliString.mk bt%s bt%s).wt = %d)]"
            % (f, nm(zz), w))
    # per-dressing values
    for t, (zz, q, signs, flip) in enumerate(info):
        P = pattern_expr(f, signs, False)
        Ps = pattern_expr(f, signs, True)
        op = "+" if q == 0 else "-"
        inner = "(%s) %s (%s)" % (P, op, Ps)
        signed = ("-(%s)" % inner) if flip else inner
        out("  have e%d : Complex.normSq (projTrace c d ⟨bt%s, bt%s⟩)" % (t, f, nm(zz)))
        out("      = 4 * Complex.normSq (%s) := by" % inner)
        out("    have h : projTrace c d ⟨bt%s, bt%s⟩" % (f, nm(zz)))
        out("        = Complex.I ^ (SS.PauliString.mk bt%s bt%s).numY * (2 * (%s)) := by"
            % (f, nm(zz), signed))
        out("      rw [pv%s c d hc hd tau htf bt%s (by decide)]" % (f, nm(zz)))
        bl = [dot(zz, Y[k]) for (j, k) in pr] + [q]
        shows = ["show SS.bdot bt%s y%d = %s from by decide"
                 % (nm(zz), k, "true" if dot(zz, Y[k]) else "false") for (j, k) in pr]
        shows.append("show SS.bdot bt%s bt%s = %s from by decide"
                     % (nm(zz), f, "true" if q else "false"))
        sc = ([" SS.signC_true"] if any(bl) else []) + ([" SS.signC_false"] if not all(bl) else [])
        out("      simp only [%s," % ", ".join(shows))
        out("       %s]" % ",".join(sc))
        if any(bl):
            out("      ring")
        if flip:
            out("    rw [h, normSq_I_pow_mul, normSq_two_mul, Complex.normSq_neg]")
        else:
            out("    rw [h, normSq_I_pow_mul, normSq_two_mul]")
    out("  rw [%s]" % ", ".join("e%d" % t for t in range(len(info))))
    # split facts
    facts = []
    for t, p in enumerate(patterns):
        P = pattern_expr(f, p, False)
        Ps = pattern_expr(f, p, True)
        out("  have s%d : Complex.normSq ((%s) + (%s)) + Complex.normSq ((%s) - (%s))"
            % (t, P, Ps, P, Ps))
        out("      = 4 * Complex.normSq (%s) := by" % P)
        st = []
        if any(x > 0 for x in p[1:]):
            st.append("star_add")
        if any(x < 0 for x in p[1:]):
            st.append("star_sub")
        st += ["star_mul'", "star_star"]
        out("    have hh : (%s) = star (%s) := by" % (Ps, P))
        out("      simp only [%s]" % ", ".join(st))
        out("    rw [hh]")
        out("    exact normSq_split _")
        facts.append("s%d" % t)
    # value facts
    if npr == 1:
        (j, k) = pr[0]
        out("  have v0 : Complex.normSq (%s) = %s := by" % (Xexp(j, k), frac(QQ[j] * QQ[k])))
        out("    rw [map_mul, normSq_star, k%d, k%d]" % (j, k))
        out("    norm_num")
        facts.append("v0")
    elif needG:
        base = QQ[pr[0][0]] * QQ[pr[0][1]]
        G = " + ".join(Xexp(j, k) for (j, k) in pr)
        X1 = Xexp(*pr[0])
        out("  have hx1 : Complex.normSq (%s) = %s := by" % (X1, frac(base)))
        out("    rw [map_mul, normSq_star, k%d, k%d]" % (pr[0][0], pr[0][1]))
        out("    norm_num")
        for t in (1, 2):
            (j, k) = pr[t]
            out("  have hx%d : Complex.normSq (%s) = %s := by"
                % (t + 1, Xexp(j, k), frac(QQ[j] * QQ[k])))
            out("    rw [map_mul, normSq_star, k%d, k%d]" % (j, k))
            out("    norm_num")
        facts += ["hx1", "hx2", "hx3"]
        if (1, 1, 1) in patterns:
            out("  have vg : Complex.normSq (%s) = 1/900 :=" % G)
            out("    normSq_of_triple hg hx1")
            facts.append("vg")
        if (1, -1, -1) in patterns:
            out("  have vm : Complex.normSq (%s) = 25/900 := by"
                % pattern_expr(f, (1, -1, -1), False))
            out("    refine nsq3_5 ?_ hx1")
            out("    linear_combination -hg")
            facts.append("vm")
        mm = [p for p in patterns if nsqval[p] is None]
        if mm:
            D = "%s - (%s)" % (Xexp(*pr[1]), Xexp(*pr[2]))
            S = "%s + %s" % (Xexp(*pr[1]), Xexp(*pr[2]))
            out("  have vs : Complex.normSq (%s) = 4/900 := by" % S)
            out("    refine nsq3_2 ?_ hx1")
            out("    linear_combination hg")
            out("  have vp : Complex.normSq (%s) + Complex.normSq (%s)"
                % (S, D))
            out("      = 2 * Complex.normSq (%s) + 2 * Complex.normSq (%s) :="
                % (Xexp(*pr[1]), Xexp(*pr[2])))
            out("    nsq_par _ _")
            out("  have vq : Complex.normSq (%s) + Complex.normSq (%s)"
                % (pattern_expr(f, mm[0], False), pattern_expr(f, mm[1], False)))
            out("      = 2 * Complex.normSq (%s) + 2 * Complex.normSq (%s) := by"
                % (X1, D))
            out("    have hz1 : (%s) = (%s) + (%s) := by ring"
                % (pattern_expr(f, mm[0], False), X1, D))
            out("    have hz2 : (%s) = (%s) - (%s) := by ring"
                % (pattern_expr(f, mm[1], False), X1, D))
            out("    rw [hz1, hz2]")
            out("    exact nsq_par _ _")
            facts += ["vs", "vp", "vq"]
    elif needT:
        for t in range(3):
            (j, k) = pr[t]
            out("  have hx%d : Complex.normSq (%s) = %s := by"
                % (t + 1, Xexp(j, k), frac(QQ[j] * QQ[k])))
            out("    rw [map_mul, normSq_star, k%d, k%d]" % (j, k))
            out("    norm_num")
        facts += ["hx1", "hx2", "hx3"]
        tri = {(1, -1, -1): 0, (1, -1, 1): 1, (1, 1, -1): 2}
        for p in patterns:
            u = tri[p]
            out("  have vt%d : Complex.normSq (%s) = 4 * Complex.normSq (%s) := by"
                % (u, pattern_expr(f, p, False), Xexp(*pr[u])))
            if u == 0:
                out("    refine nsq_dbl ?_")
                out("    linear_combination -ht")
            else:
                out("    refine nsq_dbl_neg ?_")
                out("    linear_combination ht")
            facts.append("vt%d" % u)
    else:
        for t in range(3):
            (j, k) = pr[t]
            out("  have hx%d : Complex.normSq (%s) = %s := by"
                % (t + 1, Xexp(j, k), frac(QQ[j] * QQ[k])))
            out("    rw [map_mul, normSq_star, k%d, k%d]" % (j, k))
            out("    norm_num")
        out("  have vf : Complex.normSq (%s) + Complex.normSq (%s)"
            % (pattern_expr(f, (1, 1, 1), False), pattern_expr(f, (1, 1, -1), False)))
        out("      + Complex.normSq (%s) + Complex.normSq (%s)"
            % (pattern_expr(f, (1, -1, 1), False), pattern_expr(f, (1, -1, -1), False)))
        out("      = 4 * (Complex.normSq (%s) + Complex.normSq (%s) + Complex.normSq (%s)) :="
            % (Xexp(*pr[0]), Xexp(*pr[1]), Xexp(*pr[2])))
        out("    nsq_four _ _ _")
        facts += ["hx1", "hx2", "hx3", "vf"]
    out("  linarith [%s]" % ", ".join(facts))
    out()
    HINS[(f, w)] = (name, ["c", "d", "hc", "hd", "tau", "htf"] + ks
                    + (["hg"] if needG else []) + (["ht"] if needT else []), tot)


# masks with no admissible dressing at a given weight need a `nod` lemma
for w in (4, 5, 6):
    for f in MASK_ORDER:
        if not dressings(f, w):
            out("theorem nod_w%d_%s : ∀ zz : SS.BitString 6, "
                "(SS.PauliString.mk bt%s zz).wt ≠ %d := by decide" % (w, f, f, w))
out()

for w in (4, 5, 6):
    out("/-! ### Weight %d -/" % w)
    out()
    for f in MASK_ORDER:
        emit_inner(f, w)

# ------------------------------------------------------------ final theorems
HO = [
    "(ho0 : offSum c d ex1 w0 = 0)", "(ho1 : offSum c d ex1 w2 = 0)",
    "(ho2 : offSum c d ex1 w3 = 0)", "(ho3 : offSum c d ex1 w4 = 0)",
    "(ho4 : offSum c d ex2 w0 = 0)", "(ho5 : offSum c d ex2 w1 = 0)",
    "(ho6 : offSum c d ex2 w3 = 0)", "(ho7 : offSum c d ex2 w4 = 0)",
    "(ho8 : offSum c d ex3 w0 = 0)", "(ho9 : offSum c d ex3 w1 = 0)",
    "(ho10 : offSum c d ex3 w2 = 0)", "(ho11 : offSum c d ex3 w4 = 0)",
    "(ho12 : offSum c d ex4 w0 = 0)", "(ho13 : offSum c d ex4 w1 = 0)",
    "(ho14 : offSum c d ex4 w2 = 0)", "(ho15 : offSum c d ex4 w3 = 0)",
    "(ho16 : offSum c d ex15 w0 = 0)", "(ho17 : offSum c d ex25 w0 = 0)",
    "(ho18 : offSum c d ex35 w0 = 0)", "(ho19 : offSum c d ex45 w0 = 0)",
    "(ho20 : offSum c d ex56 w0 = 0)", "(ho21 : offSum c d ex16 w0 = 0)",
]
HOS = " ".join("ho%d" % i for i in range(21))
MOM = """    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5))
            (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5))
            (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)))"""

TRI = """  have htri : star (c y2) * c y9 + star (c y3) * c y7 + star (c y4) * c y6 = 0
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
  obtain ⟨tr0, tr1, tr2, tr3⟩ := htri"""

EDG = """  have hG : 3 * (star (c y3) * c y2 + star (c y7) * c y9 + star (c y8) * c y10) = star (c y3) * c y2
      ∧ 3 * (star (c y4) * c y2 + star (c y6) * c y9 + star (c y8) * c y11) = star (c y4) * c y2
      ∧ 3 * (star (c y5) * c y2 + star (c y6) * c y10 + star (c y7) * c y11) = star (c y5) * c y2
      ∧ 3 * (star (c y4) * c y3 + star (c y6) * c y7 + star (c y10) * c y11) = star (c y4) * c y3
      ∧ 3 * (star (c y5) * c y3 + star (c y6) * c y8 + star (c y9) * c y11) = star (c y5) * c y3
      ∧ 3 * (star (c y5) * c y4 + star (c y7) * c y8 + star (c y9) * c y10) = star (c y5) * c y4 := by
    rcases hcol with ⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3, b4⟩
    · exact edges_eq_of_colouring rho_quadratic star_rho k2 k3 k4 k5 hmu n2 n3 n4 n5
        hp12 hp34 b1 b2 b3 b4
    · exact edges_eq_of_colouring rho_sq_quadratic star_rho_sq k2 k3 k4 k5 hmu
        n2 n3 n4 n5 hp12 hp34 b1 b2
        (by linear_combination b3 - (rho * mu) * rho_pow_three)
        (by linear_combination b4 - (rho * mu) * rho_pow_three)
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hG"""

GNAME = {'110000': 'g1', '101000': 'g2', '100100': 'g3',
         '011000': 'g4', '010100': 'g5', '001100': 'g6'}
TNAME = {'000111': 'tr0', '001011': 'tr1', '010011': 'tr2', '100011': 'tr3'}

VALUE = {4: '291/25', 5: '384/25', 6: '79/25'}

out("/-! ## 8.  The three remaining Shor--Laflamme coefficients -/")
out()
for w in (4, 5, 6):
    needG = any(HINS[(f, w)][1] and 'hg' in HINS[(f, w)][1] for f in MASK_ORDER)
    needT = any(HINS[(f, w)][1] and 'ht' in HINS[(f, w)][1] for f in MASK_ORDER)
    out("set_option maxHeartbeats 3200000 in")
    out("/-- **`A_%d = %s` for every exact orbit-36 solution.** -/" % (w, VALUE[w]))
    out("theorem A%d_value (c d : SS.BitString 6 -> ℂ)" % w)
    out("    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)")
    out(MOM)
    for h in HO:
        out("    " + h)
    out("    : AEnum c d %d = %s := by" % (w, VALUE[w]))
    out("  obtain ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, l0, l1, l2, l3, l4, "
        "l5, l6, l7, l8, l9, l10, l11⟩ :=")
    out("    magnitudes_forced c d hm %s" % HOS)
    if needG or needT:
        out("  obtain ⟨-, -, n2, n3, n4, n5, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, "
            "-, -, -⟩ :=")
        out("    full_support c d hm %s" % HOS)
    out("  obtain ⟨tau, htf⟩ := top_form c d hm %s ho21" % HOS)
    if needG or needT:
        out("  obtain ⟨mu, hmu, hp12, hp34, hcol⟩ := phase_rigidity c d hm %s" % HOS)
    if needG:
        out(EDG)
    if needT:
        out(TRI)
    out("  rw [AEnum_split]")
    out("  have hout : (∑ f : SS.BitString 6, ∑ zz : SS.BitString 6,")
    out("      if (SS.PauliString.mk f zz).wt = %d" % w)
    out("        then Complex.normSq (projTrace c d ⟨f, zz⟩) else 0)")
    out("      = ∑ f ∈ gm, ∑ zz : SS.BitString 6,")
    out("      if (SS.PauliString.mk f zz).wt = %d" % w)
    out("        then Complex.normSq (projTrace c d ⟨f, zz⟩) else 0 := by")
    out("    refine (Finset.sum_subset (Finset.subset_univ gm) ?_).symm")
    out("    intro f _ hf")
    out("    refine Finset.sum_eq_zero (fun zz _ => ?_)")
    out("    by_cases hw : (SS.PauliString.mk f zz).wt = %d" % w)
    out("    · rw [if_pos hw]")
    out("      obtain ⟨e0, e1⟩ := (masksG f).resolve_left hf")
    out("      rw [projTrace_no_incidence hc hd e0 e1, Complex.normSq_zero]")
    out("    · rw [if_neg hw]")
    out("  rw [hout]")
    out("  simp only [gm]")
    ins = ", ".join(["Finset.sum_insert (by decide)"] * (len(MASK_ORDER) - 1)
                    + ["Finset.sum_singleton"])
    out("  rw [%s]" % ins)
    calls = []
    for f in MASK_ORDER:
        name, argl, _ = HINS[(f, w)]
        a = []
        for x in argl:
            if x == 'hg':
                a.append(GNAME[f])
            elif x == 'ht':
                a.append(TNAME[f])
            else:
                a.append(x)
        calls.append("%s %s" % (name, " ".join(a)) if a else name)
    out("  rw [%s]" % ",\n    ".join(calls))
    out("  norm_num")
    out()

out("""set_option maxHeartbeats 1600000 in
/-- **The unconditional Shor--Laflamme enumerator of orbit 36.**  No MacWilliams
hypothesis: every coefficient is computed from the support conditions, the
moment system and the twenty-two Knill--Laflamme rows alone. -/
theorem enumerator_value (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)""")
out(MOM)
for h in HO:
    out("    " + h)
out("    : AEnum c d 0 = 1 ∧ AEnum c d 1 = 0 ∧ AEnum c d 2 = 21/25 ∧ AEnum c d 3 = 0")
out("      ∧ AEnum c d 4 = 291/25 ∧ AEnum c d 5 = 384/25 ∧ AEnum c d 6 = 79/25 :=")
out("  ⟨A0_value c d hc hd hm %s," % HOS)
out("   A1_eq_zero c d hc hd hm,")
out("   A2_value c d hc hd hm %s ho21," % HOS)
out("   A3_value c d hc hd hm %s ho21," % HOS)
out("   A4_value c d hc hd hm %s ho21," % HOS)
out("   A5_value c d hc hd hm %s ho21," % HOS)
out("   A6_value c d hc hd hm %s ho21⟩" % HOS)
out()
out("end")
out()
out("end SixQubit.Orbit36Enum4")

import io
import os
path = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.abspath(__file__)))), "SixQubit", "Orbit36Enum4.lean")
with io.open(path, "w", encoding="utf-8", newline="\n") as fh:
    fh.write("\n".join(L) + "\n")
print("wrote", path, len(L), "lines")
