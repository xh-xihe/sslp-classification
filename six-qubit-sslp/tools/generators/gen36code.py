"""Generator and exact checker for the orbit-36 existence witness.

Orbit 36, after the local-X conjugation of supplementary.tex line 344, is
represented by a* = (1,1,1,1,2,3), q = 5, fibers (S_0, S_4) with
S_4 = complement(S_0).  The canonical bottom word is

    |psi_0> = (1/sqrt 10)(|u> + |v> + sum_i |s_i>)
            + (1/sqrt 15)(|e12> + |e34> + w(|e13> + |e24>) + w^2(|e14> + |e23>))

with w = exp(2 pi i / 3), and |psi_1> = Z5 Z6 X^{tensor 6} K |psi_0>.

Everything is done in EXACT integer arithmetic.  Scaling |psi_0> by 2 sqrt 30
clears both radicals:

    (2 sqrt 30) / sqrt 10 = 2 sqrt 3,      (2 sqrt 30) / sqrt 15 = 2 sqrt 2,
    2 sqrt 2 * w   = -sqrt 2 + i sqrt 6,
    2 sqrt 2 * w^2 = -sqrt 2 - i sqrt 6,

so the scaled amplitudes lie in Z[sqrt 2, sqrt 3, i] -- eight INTEGER
coordinates.  That is the ring `ZQ` emitted into Lean; integers (unlike Rat)
reduce inside the Lean kernel.

The script
  1. rebuilds S_0 from `tools/core/orbit.py` and checks the twelve strings,
  2. checks the exact 154-Pauli Knill-Laflamme system in Z[sqrt2,sqrt3,i],
  3. cross-checks against floating point (probabilities 1/10 and 1/15 and the
     lambda_E table of supplementary.tex),
  4. emits `SixQubit/Orbit36Code.lean`.

Run:  python tools/generators/gen36code.py            (check + emit)
      python tools/generators/gen36code.py --check    (check only)
"""

from __future__ import annotations

import os
import sys
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "tools"))

from core.orbit import fiber  # noqa: E402

N = 6

# ---------------------------------------------------------------------------
# exact arithmetic in Z[sqrt 2, sqrt 3, i]
# ---------------------------------------------------------------------------
# an element is an 8-tuple (a0,a1,a2,a3,b0,b1,b2,b3) standing for
#   (a0 + a1 r2 + a2 r3 + a3 r6) + i (b0 + b1 r2 + b2 r3 + b3 r6)

ZERO = (0,) * 8


def rpmul(a, c):
    return (
        a[0] * c[0] + 2 * a[1] * c[1] + 3 * a[2] * c[2] + 6 * a[3] * c[3],
        a[0] * c[1] + a[1] * c[0] + 3 * a[2] * c[3] + 3 * a[3] * c[2],
        a[0] * c[2] + a[2] * c[0] + 2 * a[1] * c[3] + 2 * a[3] * c[1],
        a[0] * c[3] + a[3] * c[0] + a[1] * c[2] + a[2] * c[1],
    )


def zmul(x, y):
    A, B = x[:4], x[4:]
    C, D = y[:4], y[4:]
    re = tuple(p - q for p, q in zip(rpmul(A, C), rpmul(B, D)))
    im = tuple(p + q for p, q in zip(rpmul(A, D), rpmul(B, C)))
    return re + im


def zadd(x, y):
    return tuple(p + q for p, q in zip(x, y))


def zsub(x, y):
    return tuple(p - q for p, q in zip(x, y))


def zneg(x):
    return tuple(-p for p in x)


def zconj(x):
    return x[:4] + tuple(-p for p in x[4:])


def zfloat(x):
    import math

    r2, r3, r6 = math.sqrt(2), math.sqrt(3), math.sqrt(6)
    re = x[0] + x[1] * r2 + x[2] * r3 + x[3] * r6
    im = x[4] + x[5] * r2 + x[6] * r3 + x[7] * r6
    return complex(re, im)


# ---------------------------------------------------------------------------
# the fiber pair
# ---------------------------------------------------------------------------

ASTAR = [1, 1, 1, 1, 2, 3]
Q = 5

EXPECTED_S0 = {
    "u": "000000",
    "v": "000011",
    "s1": "011110",
    "s2": "101110",
    "s3": "110110",
    "s4": "111010",
    "e12": "110001",
    "e13": "101001",
    "e14": "100101",
    "e23": "011001",
    "e24": "010101",
    "e34": "001101",
}


def cmpl(s):
    return "".join("1" if ch == "0" else "0" for ch in s)


def mask(s):
    """bit i of the mask is character i of the string (leftmost char = bit 0)"""
    return sum(1 << i for i in range(N) if s[i] == "1")


def unmask(m):
    return "".join("1" if (m >> i) & 1 else "0" for i in range(N))


def check_fibers():
    S0 = fiber(ASTAR, Q, 0)
    S4 = fiber(ASTAR, Q, 4)
    assert sorted(S0) == sorted(EXPECTED_S0.values()), sorted(S0)
    assert sorted(S4) == sorted(cmpl(s) for s in S0)
    assert len(S0) == 12 and len(S4) == 12
    return S0, S4


# ---------------------------------------------------------------------------
# the scaled canonical amplitudes
# ---------------------------------------------------------------------------

R3 = (0, 0, 2, 0, 0, 0, 0, 0)            #  2 sqrt 3
R2 = (0, 2, 0, 0, 0, 0, 0, 0)            #  2 sqrt 2
R2W = (0, -1, 0, 0, 0, 0, 0, 1)          #  2 sqrt 2 * w   = -sqrt2 + i sqrt6
R2W2 = (0, -1, 0, 0, 0, 0, 0, -1)        #  2 sqrt 2 * w^2 = -sqrt2 - i sqrt6


def build_amps():
    E = EXPECTED_S0
    amp0 = {}
    for k in ("u", "v", "s1", "s2", "s3", "s4"):
        amp0[mask(E[k])] = R3
    amp0[mask(E["e12"])] = R2
    amp0[mask(E["e34"])] = R2
    amp0[mask(E["e13"])] = R2W
    amp0[mask(E["e24"])] = R2W
    amp0[mask(E["e14"])] = R2W2
    amp0[mask(E["e23"])] = R2W2
    # psi_1 (y) = (-1)^{y5+y6} conj(psi_0 (complement y));  qubits 5,6 are bits 4,5
    amp1 = {}
    for m, val in amp0.items():
        y = 63 - m
        sgn = ((y >> 4) & 1) + ((y >> 5) & 1)
        w = zconj(val)
        amp1[y] = zneg(w) if sgn % 2 else w
    assert len(amp0) == 12 and len(amp1) == 12
    return amp0, amp1


def get(amp, m):
    return amp.get(m, ZERO)


# ---------------------------------------------------------------------------
# exact Knill--Laflamme check over the 154 weight-<=2 Paulis
# ---------------------------------------------------------------------------


def popcount(m):
    return bin(m).count("1")


def bdot(k, s):
    return popcount(k & s) % 2


def matelt(ampj, ampk, supk, m, k):
    """sum_{s in supp k} (-1)^{k.s} conj(ampj (s xor m)) ampk (s)"""
    acc = ZERO
    for s in supk:
        t = zmul(zconj(get(ampj, s ^ m)), get(ampk, s))
        if bdot(k, s):
            t = zneg(t)
        acc = zadd(acc, t)
    return acc


def numY(m, k):
    return popcount(m & k)


def check_kl(amp0, amp1):
    sup0 = sorted(amp0)
    sup1 = sorted(amp1)
    npauli = 0
    table = {}
    for m in range(64):
        for k in range(64):
            if popcount(m | k) > 2:
                continue
            npauli += 1
            d0 = matelt(amp0, amp0, sup0, m, k)
            d1 = matelt(amp1, amp1, sup1, m, k)
            o01 = matelt(amp0, amp1, sup1, m, k)
            o10 = matelt(amp1, amp0, sup0, m, k)
            assert zsub(d0, d1) == ZERO, ("diag", m, k, d0, d1)
            assert o01 == ZERO, ("off01", m, k, o01)
            assert o10 == ZERO, ("off10", m, k, o10)
            table[(m, k)] = d0
    assert npauli == 154, npauli
    return table


# ---------------------------------------------------------------------------
# floating point cross-check of the lambda_E table
# ---------------------------------------------------------------------------


def paulilabel(m, k):
    """label of the Pauli i^{#Y} X^m Z^k, qubits numbered 1..6"""
    out = []
    for i in range(N):
        xb, zb = (m >> i) & 1, (k >> i) & 1
        c = {(0, 0): None, (1, 0): "X", (0, 1): "Z", (1, 1): "Y"}[(xb, zb)]
        if c:
            out.append("%s%d" % (c, i + 1))
    return "".join(out) if out else "I"


def check_table(table):
    """lambda_E = i^{#Y} * (1/120) * table[(m,k)]; compare with the paper."""
    import math

    expect = {}
    for i, j in combinations(range(4), 2):
        for c in ("X", "Z", "Y"):
            expect["%s%d%s%d" % (c, i + 1, c, j + 1)] = 1 / 15
    for i in range(4):
        expect["Z%dZ5" % (i + 1)] = 1 / 5
        expect["Z%dZ6" % (i + 1)] = -1 / 5
    expect["X5X6"] = 1 / 5
    expect["Y5Y6"] = -1 / 5
    expect["Z5Z6"] = -3 / 5
    expect["I"] = 1.0

    got = {}
    for (m, k), val in table.items():
        lam = (1j ** numY(m, k)) * zfloat(val) / 120.0
        assert abs(lam.imag) < 1e-9, (m, k, lam)
        if abs(lam.real) > 1e-9:
            got[paulilabel(m, k)] = lam.real
    assert set(got) == set(expect), (sorted(set(got) ^ set(expect)))
    for key in expect:
        assert abs(got[key] - expect[key]) < 1e-9, (key, got[key], expect[key])
    return got


def check_probabilities(amp0, amp1):
    import math

    for amp in (amp0, amp1):
        tot = 0.0
        n10 = n15 = 0
        for m, val in amp.items():
            p = abs(zfloat(val)) ** 2 / 120.0
            tot += p
            if abs(p - 0.1) < 1e-12:
                n10 += 1
            elif abs(p - 1 / 15) < 1e-12:
                n15 += 1
            else:
                raise AssertionError((m, p))
        assert abs(tot - 1.0) < 1e-12, tot
        assert n10 == 6 and n15 == 6, (n10, n15)


# ---------------------------------------------------------------------------
# Lean emission
# ---------------------------------------------------------------------------

BOOLS = {"0": "false", "1": "true"}

NAMES0 = ["u", "v", "s1", "s2", "s3", "s4",
          "e12", "e13", "e14", "e23", "e24", "e34"]
VERT = NAMES0[:6]
EDGE = NAMES0[6:]


def lean_bs(s):
    return "bs " + " ".join("%-5s" % BOOLS[c] for c in s)


def zq_lit(x):
    return "z8 " + " ".join(("(%d)" % v) if v < 0 else str(v) for v in x)


PREAMBLE = r'''import Mathlib

import SS.HilbertKL
import SS.QSqrt235iC

/-!
# Orbit 36: the canonical pair is an exact `((6,2,3))` code

GENERATED by `tools/generators/gen36code.py`; do not edit by hand.

Orbit 36 is the unique realizable order-five moment orbit of the six-qubit
classification.  After the local-`X` conjugation of `supplementary.tex`
(section "Rigidity of the order-five orbit 36") it is represented by
`a* = (1,1,1,1,2,3)`, `q = 5`, with fibers `(S_0, S_4)`, `S_4 = complement S_0`,
both of size twelve.  Writing a string as `x1x2x3x4;x5x6`, the canonical pair is

```
|psi_0> = (1/sqrt 10) (|u> + |v> + sum_i |s_i>)
        + (1/sqrt 15) (|e12> + |e34> + w (|e13> + |e24>) + w^2 (|e14> + |e23>))
|psi_1> = Z_5 Z_6 X^{tensor 6} K |psi_0>
```

with `w = exp (2 pi i / 3)` and `K` complex conjugation in the computational
basis.  This file proves `canonical_is_code : SS.HasDistance ![c36, d36] 3`,
i.e. the genuine Knill--Laflamme conditions of `SS/HilbertKL.lean` for every
Pauli of weight at most two, together with normalization, orthogonality, the
exact support, and the twelve probabilities `1/10` and `1/15` in each word.

## How the kernel sees it

Scaling by `2 * sqrt 30` clears both radicals:
`(2 sqrt 30)/sqrt 10 = 2 sqrt 3`, `(2 sqrt 30)/sqrt 15 = 2 sqrt 2`,
`2 sqrt 2 * w = -sqrt 2 + i sqrt 6`, `2 sqrt 2 * w^2 = -sqrt 2 - i sqrt 6`.
Every scaled amplitude therefore lies in `Z[sqrt 2, sqrt 3, i]`, carried here as
eight INTEGER coordinates (`ZQ`).  Integers reduce inside the Lean kernel where
rationals do not, so the 154 weight-`<= 2` constraints become a single `decide`
over mask pairs `m, k < 64`, and `matElt_eq` transports the exact sums back to
genuine complex matrix elements.

No `sorry`, no `native_decide`.
-/

set_option maxRecDepth 40000

namespace SixQubit.Orbit36Code

open scoped BigOperators

/-! ## The ring `Z[sqrt 2, sqrt 3, i]` in eight integer coordinates -/

/-- `a0 + a1 r2 + a2 r3 + a3 r6 + i (b0 + b1 r2 + b2 r3 + b3 r6)` with
`r2 = sqrt 2`, `r3 = sqrt 3`, `r6 = sqrt 2 * sqrt 3`. -/
structure ZQ where
  a0 : Int
  a1 : Int
  a2 : Int
  a3 : Int
  b0 : Int
  b1 : Int
  b2 : Int
  b3 : Int
deriving DecidableEq

/-- Positional constructor for the generated amplitude tables. -/
def z8 (a0 a1 a2 a3 b0 b1 b2 b3 : Int) : ZQ := ⟨a0, a1, a2, a3, b0, b1, b2, b3⟩

namespace ZQ

def zero : ZQ := z8 0 0 0 0 0 0 0 0

def add (x y : ZQ) : ZQ :=
  ⟨x.a0 + y.a0, x.a1 + y.a1, x.a2 + y.a2, x.a3 + y.a3,
   x.b0 + y.b0, x.b1 + y.b1, x.b2 + y.b2, x.b3 + y.b3⟩

def neg (x : ZQ) : ZQ :=
  ⟨-x.a0, -x.a1, -x.a2, -x.a3, -x.b0, -x.b1, -x.b2, -x.b3⟩

def sub (x y : ZQ) : ZQ := add x (neg y)

def conj (x : ZQ) : ZQ :=
  ⟨x.a0, x.a1, x.a2, x.a3, -x.b0, -x.b1, -x.b2, -x.b3⟩

/-- Multiplication.  The two `zero` guards come first, so the kernel never
reaches the sixty-four integer products when an amplitude vanishes. -/
def mul (x y : ZQ) : ZQ :=
  if x = zero then zero else if y = zero then zero else
  ⟨(x.a0*y.a0 + 2*x.a1*y.a1 + 3*x.a2*y.a2 + 6*x.a3*y.a3)
     - (x.b0*y.b0 + 2*x.b1*y.b1 + 3*x.b2*y.b2 + 6*x.b3*y.b3),
   (x.a0*y.a1 + x.a1*y.a0 + 3*x.a2*y.a3 + 3*x.a3*y.a2)
     - (x.b0*y.b1 + x.b1*y.b0 + 3*x.b2*y.b3 + 3*x.b3*y.b2),
   (x.a0*y.a2 + x.a2*y.a0 + 2*x.a1*y.a3 + 2*x.a3*y.a1)
     - (x.b0*y.b2 + x.b2*y.b0 + 2*x.b1*y.b3 + 2*x.b3*y.b1),
   (x.a0*y.a3 + x.a3*y.a0 + x.a1*y.a2 + x.a2*y.a1)
     - (x.b0*y.b3 + x.b3*y.b0 + x.b1*y.b2 + x.b2*y.b1),
   (x.a0*y.b0 + 2*x.a1*y.b1 + 3*x.a2*y.b2 + 6*x.a3*y.b3)
     + (x.b0*y.a0 + 2*x.b1*y.a1 + 3*x.b2*y.a2 + 6*x.b3*y.a3),
   (x.a0*y.b1 + x.a1*y.b0 + 3*x.a2*y.b3 + 3*x.a3*y.b2)
     + (x.b0*y.a1 + x.b1*y.a0 + 3*x.b2*y.a3 + 3*x.b3*y.a2),
   (x.a0*y.b2 + x.a2*y.b0 + 2*x.a1*y.b3 + 2*x.a3*y.b1)
     + (x.b0*y.a2 + x.b2*y.a0 + 2*x.b1*y.a3 + 2*x.b3*y.a1),
   (x.a0*y.b3 + x.a3*y.b0 + x.a1*y.b2 + x.a2*y.b1)
     + (x.b0*y.a3 + x.b3*y.a0 + x.b1*y.a2 + x.b2*y.a1)⟩

/-- Multiply by `(-1)` when the boolean is `true`. -/
def signMul (b : Bool) (x : ZQ) : ZQ := if b then neg x else x

lemma neg_zero : ZQ.neg ZQ.zero = ZQ.zero := by decide

lemma mul_zero_right (x : ZQ) : ZQ.mul x ZQ.zero = ZQ.zero := by
  by_cases h : x = ZQ.zero <;> simp [ZQ.mul, h]

lemma signMul_zero (b : Bool) : ZQ.signMul b ZQ.zero = ZQ.zero := by
  cases b
  · rfl
  · exact neg_zero

end ZQ

/-! ## The embedding into `ℂ` -/

noncomputable section

/-- The real number `a0 + a1 sqrt 2 + a2 sqrt 3 + a3 sqrt 6`. -/
def rz (a0 a1 a2 a3 : Int) : ℝ := SS.rp (a0 : ℚ) (a1 : ℚ) (a2 : ℚ) (a3 : ℚ)

/-- Real part of the embedding. -/
def toCre (x : ZQ) : ℝ := rz x.a0 x.a1 x.a2 x.a3

/-- Imaginary part of the embedding. -/
def toCim (x : ZQ) : ℝ := rz x.b0 x.b1 x.b2 x.b3

/-- The embedding `ZQ → ℂ`. -/
def toC (x : ZQ) : ℂ := ⟨toCre x, toCim x⟩

@[simp] lemma toC_re (x : ZQ) : (toC x).re = toCre x := rfl
@[simp] lemma toC_im (x : ZQ) : (toC x).im = toCim x := rfl

lemma rz_add (a0 a1 a2 a3 c0 c1 c2 c3 : Int) :
    rz (a0 + c0) (a1 + c1) (a2 + c2) (a3 + c3)
      = rz a0 a1 a2 a3 + rz c0 c1 c2 c3 := by
  simp only [rz]; push_cast; exact SS.rp_add _ _ _ _ _ _ _ _

lemma rz_sub (a0 a1 a2 a3 c0 c1 c2 c3 : Int) :
    rz (a0 - c0) (a1 - c1) (a2 - c2) (a3 - c3)
      = rz a0 a1 a2 a3 - rz c0 c1 c2 c3 := by
  simp only [rz]; push_cast; exact SS.rp_sub _ _ _ _ _ _ _ _

lemma rz_neg (a0 a1 a2 a3 : Int) :
    rz (-a0) (-a1) (-a2) (-a3) = -rz a0 a1 a2 a3 := by
  simp only [rz]; push_cast; exact SS.rp_neg _ _ _ _

lemma rz_mul (a0 a1 a2 a3 c0 c1 c2 c3 : Int) :
    rz a0 a1 a2 a3 * rz c0 c1 c2 c3
      = rz (a0*c0 + 2*a1*c1 + 3*a2*c2 + 6*a3*c3)
           (a0*c1 + a1*c0 + 3*a2*c3 + 3*a3*c2)
           (a0*c2 + a2*c0 + 2*a1*c3 + 2*a3*c1)
           (a0*c3 + a3*c0 + a1*c2 + a2*c1) := by
  simp only [rz]; push_cast; exact SS.rp_mul _ _ _ _ _ _ _ _

lemma rz_intCast (a : Int) : rz a 0 0 0 = (a : ℝ) := by
  simp [rz, SS.rp]

@[simp] lemma toC_zero : toC ZQ.zero = 0 := by
  apply Complex.ext <;> simp [toCre, toCim, ZQ.zero, z8, rz, SS.rp]

lemma toC_intCast (a : Int) : toC (z8 a 0 0 0 0 0 0 0) = (a : ℂ) := by
  apply Complex.ext <;> simp [toCre, toCim, z8, rz_intCast]

lemma toC_add (x y : ZQ) : toC (ZQ.add x y) = toC x + toC y := by
  apply Complex.ext <;>
    simp only [toC_re, toC_im, Complex.add_re, Complex.add_im, toCre, toCim,
      ZQ.add] <;>
    exact rz_add _ _ _ _ _ _ _ _

lemma toC_neg (x : ZQ) : toC (ZQ.neg x) = -toC x := by
  apply Complex.ext <;>
    simp only [toC_re, toC_im, Complex.neg_re, Complex.neg_im, toCre, toCim,
      ZQ.neg] <;>
    exact rz_neg _ _ _ _

lemma toC_sub (x y : ZQ) : toC (ZQ.sub x y) = toC x - toC y := by
  rw [ZQ.sub, toC_add, toC_neg]; ring

lemma toC_conj (x : ZQ) : toC (ZQ.conj x) = star (toC x) := by
  apply Complex.ext
  · simp only [toC_re, Complex.star_def, Complex.conj_re, toCre, ZQ.conj]
  · simp only [toC_im, Complex.star_def, Complex.conj_im, toCim, ZQ.conj]
    exact rz_neg _ _ _ _

lemma toC_mul (x y : ZQ) : toC (ZQ.mul x y) = toC x * toC y := by
  by_cases hx : x = ZQ.zero
  · rw [hx, show ZQ.mul ZQ.zero y = ZQ.zero from by simp [ZQ.mul], toC_zero,
      zero_mul]
  by_cases hy : y = ZQ.zero
  · rw [hy, ZQ.mul_zero_right, toC_zero, mul_zero]
  apply Complex.ext
  · simp only [toC_re, toC_im, Complex.mul_re, toCre, toCim, ZQ.mul, if_neg hx,
      if_neg hy]
    rw [rz_mul, rz_mul, ← rz_sub]
  · simp only [toC_re, toC_im, Complex.mul_im, toCre, toCim, ZQ.mul, if_neg hx,
      if_neg hy]
    rw [rz_mul, rz_mul, ← rz_add]

lemma toC_signMul (b : Bool) (x : ZQ) :
    toC (ZQ.signMul b x) = SS.signC b (toC x) := by
  cases b
  · rfl
  · exact toC_neg x

end

/-! ## Bitstrings, masks, and the two fibers -/

def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]

/-- The integer mask of a bitstring: coordinate `i` is bit `i`. -/
def num (x : SS.BitString 6) : Nat :=
  (if x 0 then 1 else 0) + (if x 1 then 2 else 0) + (if x 2 then 4 else 0)
    + (if x 3 then 8 else 0) + (if x 4 then 16 else 0) + (if x 5 then 32 else 0)

/-- The bitstring of an integer mask. -/
def nbit (m : Nat) : SS.BitString 6 := fun i => Nat.testBit m i.val

theorem nbit_num : ∀ x : SS.BitString 6, nbit (num x) = x := by decide

theorem num_lt : ∀ x : SS.BitString 6, num x < 64 := by decide

'''

FIBER_BLOCK = r'''
def S0 : Finset (SS.BitString 6) := L0.toFinset
def S1 : Finset (SS.BitString 6) := L1.toFinset

theorem L0_nodup : L0.Nodup := by decide
theorem L1_nodup : L1.Nodup := by decide

/-- The angle vector `a* = (1,1,1,1,2,3)` of the conjugated representative. -/
def av : Fin 6 → ZMod 5 := ![1, 1, 1, 1, 2, 3]

/-- `S_0` is exactly the residue-0 fiber, decided over all 64 strings. -/
theorem S0_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 0) = S0 := by decide

/-- `S_1` is exactly the residue-4 fiber, decided over all 64 strings. -/
theorem S1_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 4) = S1 := by decide

/-- The second fiber is the complement of the first. -/
theorem S1_eq_complement : S1 = S0.image SS.complement := by decide

/-! ## The scaled amplitudes

`c0z` and `c1z` are `2 * sqrt 30` times the two canonical logical words. -/
'''

TAIL_A = r'''
/-! ## The exact matrix-element sums -/

/-- One term of a matrix-element sum: `(-1)^{z.s} conj (cj (s xor x)) * ck s`. -/
def zterm (cj ck : SS.BitString 6 → ZQ) (x z s : SS.BitString 6) : ZQ :=
  ZQ.signMul (SS.bdot z s) (ZQ.mul (ZQ.conj (cj (SS.bxor s x))) (ck s))

/-- Exact sum of a `ZQ`-valued function over a list of bitstrings. -/
def zsum (L : List (SS.BitString 6)) (f : SS.BitString 6 → ZQ) : ZQ :=
  (L.map f).foldr ZQ.add ZQ.zero

/-- The exact matrix element `<psi_j| P(x,z) |psi_k>` without the `i^{#Y}`
prefactor; `Lk` is a support list for `ck`. -/
def zmat (cj ck : SS.BitString 6 → ZQ) (Lk : List (SS.BitString 6))
    (x z : SS.BitString 6) : ZQ :=
  zsum Lk (zterm cj ck x z)

/-! ## The finite certificate

For each Pauli `P(x,z)` the certificate checks four things: the two diagonal
elements agree, both off-diagonal elements vanish, and -- unless `(x,z)` is one
of the thirty entries of `tblCodes` -- the diagonal element itself vanishes. -/

/-- A Pauli `P(x,z)` on six qubits, encoded as `64 * num x + num z`. -/
def pcode (x z : SS.BitString 6) : Nat := 64 * num x + num z

/-- The thirty weight-`<= 2` Paulis with a nonzero diagonal scalar `lambda_E`;
every other weight-`<= 2` Pauli has `lambda_E = 0`. -/
def tblCodes : List Nat :=
@@TBLCODES@@

/-- Membership test for `tblCodes`. -/
def inTable (x z : SS.BitString 6) : Bool := tblCodes.contains (pcode x z)

def checkB (x z : SS.BitString 6) : Bool :=
  decide (ZQ.sub (zmat c0z c0z L0 x z) (zmat c1z c1z L1 x z) = ZQ.zero)
    && decide (zmat c0z c1z L1 x z = ZQ.zero)
    && decide (zmat c1z c0z L0 x z = ZQ.zero)
    && (inTable x z || decide (zmat c0z c0z L0 x z = ZQ.zero))

set_option maxHeartbeats 4000000 in
/-- **The 154 weight-`<= 2` Knill--Laflamme constraints**, decided by the kernel
over all mask pairs.  The guard rejects the 3942 pairs of Pauli weight three or
more before any ring arithmetic is reached. -/
theorem check_all : ∀ m < 64, ∀ k < 64,
    (⟨nbit m, nbit k⟩ : SS.PauliString 6).wt ≤ 2 →
    checkB (nbit m) (nbit k) = true := by decide

/-- The certificate holds for every Pauli of weight at most two. -/
theorem checkB_of_wt (P : SS.PauliString 6) (hw : P.wt ≤ 2) :
    checkB P.x P.z = true := by
  have hx := nbit_num P.x
  have hz := nbit_num P.z
  have h := check_all (num P.x) (num_lt _) (num P.z) (num_lt _)
    (by rw [hx, hz]; exact hw)
  rwa [hx, hz] at h

/-- The exact squared norm of the scaled bottom word: `6*12 + 6*8 = 120`. -/
theorem zmat_id_c0z :
    zmat c0z c0z L0 (fun _ => false) (fun _ => false) = z8 120 0 0 0 0 0 0 0 := by
  decide

/-- The identity Pauli has no `Y` factors. -/
theorem idPauli_numY :
    (⟨fun _ => false, fun _ => false⟩ : SS.PauliString 6).numY = 0 := by decide

/-- The identity Pauli has weight zero. -/
theorem idPauli_wt :
    (⟨fun _ => false, fun _ => false⟩ : SS.PauliString 6).wt ≤ 2 := by decide

/-! ## Transport to genuine complex matrix elements -/

noncomputable section

/-- The normalizing scalar `1 / (2 sqrt 30)`. -/
def sc : ℂ := ((Real.sqrt 30 : ℝ) : ℂ)⁻¹ / 2

lemma sqrt30_sq : ((Real.sqrt 30 : ℝ) : ℂ) * ((Real.sqrt 30 : ℝ) : ℂ) = 30 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 30)]
  norm_num

lemma sc_star : star sc = sc := by
  have h : sc = (((Real.sqrt 30)⁻¹ / 2 : ℝ) : ℂ) := by
    push_cast [sc]
    ring
  rw [h, Complex.star_def, Complex.conj_ofReal]

lemma sc_sq : star sc * sc = (120 : ℂ)⁻¹ := by
  rw [sc_star, sc, div_mul_div_comm, ← mul_inv, sqrt30_sq]
  norm_num

/-- The complex state attached to exact amplitudes, scaled to unit norm. -/
def stC (c : SS.BitString 6 → ZQ) : SS.State 6 ℂ := fun s => sc * toC (c s)

/-- `|0_L>` of the canonical pair. -/
def c36 : SS.State 6 ℂ := stC c0z

/-- `|1_L>` of the canonical pair. -/
def d36 : SS.State 6 ℂ := stC c1z

/-- `toC` turns a `zsum` into an ordinary sum over the list. -/
lemma toC_zsum (L : List (SS.BitString 6)) (f : SS.BitString 6 → ZQ) :
    toC (zsum L f) = (L.map (fun s => toC (f s))).sum := by
  unfold zsum
  induction L with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.foldr_cons, List.sum_cons, toC_add, ih]

lemma zterm_eq_zero {cj ck : SS.BitString 6 → ZQ} {x z s : SS.BitString 6}
    (h : ck s = ZQ.zero) : zterm cj ck x z s = ZQ.zero := by
  unfold zterm
  rw [h, ZQ.mul_zero_right, ZQ.signMul_zero]

/-- **The exact sums are the true Knill--Laflamme matrix elements.** -/
theorem matElt_eq (cj ck : SS.BitString 6 → ZQ) (Lk : List (SS.BitString 6))
    (hnd : Lk.Nodup) (hk : ∀ s, s ∉ Lk → ck s = ZQ.zero) (P : SS.PauliString 6) :
    SS.innerC (stC cj) (SS.pauliAct P (stC ck))
      = star sc * sc * (Complex.I ^ P.numY) * toC (zmat cj ck Lk P.x P.z) := by
  classical
  have hcong : ∀ s : SS.BitString 6,
      SS.signC (SS.bdot P.z s) (star (stC cj (SS.bxor s P.x)) * stC ck s)
        = star sc * sc * toC (zterm cj ck P.x P.z s) := by
    intro s
    unfold zterm stC
    rw [toC_signMul, toC_mul, toC_conj]
    cases SS.bdot P.z s <;>
      simp only [SS.signC_true, SS.signC_false, star_mul'] <;> ring
  have hsub : ∑ s : SS.BitString 6, toC (zterm cj ck P.x P.z s)
      = ∑ s ∈ Lk.toFinset, toC (zterm cj ck P.x P.z s) := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro s _ hs
    rw [zterm_eq_zero (hk s (by simpa using hs)), toC_zero]
  have hkey : ∑ s : SS.BitString 6,
      SS.signC (SS.bdot P.z s) (star (stC cj (SS.bxor s P.x)) * stC ck s)
        = star sc * sc * toC (zmat cj ck Lk P.x P.z) := by
    rw [Finset.sum_congr rfl (fun s _ => hcong s), ← Finset.mul_sum, hsub,
      List.sum_toFinset _ hnd, ← toC_zsum, zmat]
  rw [SS.innerC_pauliAct, hkey]
  ring

lemma offdiag01 (P : SS.PauliString 6) (hw : P.wt ≤ 2) :
    SS.innerC c36 (SS.pauliAct P d36) = 0 := by
  have h := checkB_of_wt P hw
  simp only [checkB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  show SS.innerC (stC c0z) (SS.pauliAct P (stC c1z)) = 0
  rw [matElt_eq c0z c1z L1 L1_nodup c1z_vanishes P, h.1.1.2, toC_zero, mul_zero]

lemma offdiag10 (P : SS.PauliString 6) (hw : P.wt ≤ 2) :
    SS.innerC d36 (SS.pauliAct P c36) = 0 := by
  have h := checkB_of_wt P hw
  simp only [checkB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  show SS.innerC (stC c1z) (SS.pauliAct P (stC c0z)) = 0
  rw [matElt_eq c1z c0z L0 L0_nodup c0z_vanishes P, h.1.2, toC_zero, mul_zero]

lemma diag_eq (P : SS.PauliString 6) (hw : P.wt ≤ 2) :
    SS.innerC d36 (SS.pauliAct P d36) = SS.innerC c36 (SS.pauliAct P c36) := by
  have h := checkB_of_wt P hw
  simp only [checkB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  have h0 : toC (ZQ.sub (zmat c0z c0z L0 P.x P.z) (zmat c1z c1z L1 P.x P.z)) = 0 := by
    rw [h.1.1.1, toC_zero]
  rw [toC_sub] at h0
  show SS.innerC (stC c1z) (SS.pauliAct P (stC c1z))
    = SS.innerC (stC c0z) (SS.pauliAct P (stC c0z))
  rw [matElt_eq c0z c0z L0 L0_nodup c0z_vanishes P,
    matElt_eq c1z c1z L1 L1_nodup c1z_vanishes P]
  linear_combination (-(star sc * sc * (Complex.I ^ P.numY))) * h0

/-! ## The main theorem -/

/-- **The canonical orbit-36 pair is an exact `((6,2,3))` code.**

`SS.HasDistance ![c36, d36] 3` is the genuine Knill--Laflamme statement: for
every Pauli `P` of weight at most two there is one scalar `c_P` with
`<psi_j| P |psi_k> = c_P * delta_{jk}`. -/
theorem canonical_is_code : SS.HasDistance ![c36, d36] 3 := by
  intro P hw
  have hw2 : P.wt ≤ 2 := hw
  refine ⟨SS.innerC c36 (SS.pauliAct P c36), ?_⟩
  intro j k
  fin_cases j <;> fin_cases k
  · show SS.innerC c36 (SS.pauliAct P c36) = _
    rw [if_pos rfl]
  · show SS.innerC c36 (SS.pauliAct P d36) = _
    rw [if_neg (by decide)]
    exact offdiag01 P hw2
  · show SS.innerC d36 (SS.pauliAct P c36) = _
    rw [if_neg (by decide)]
    exact offdiag10 P hw2
  · show SS.innerC d36 (SS.pauliAct P d36) = _
    rw [if_pos rfl]
    exact diag_eq P hw2

/-! ## Normalization, orthogonality and support -/

lemma bdot_zero_left (t : SS.BitString 6) :
    SS.bdot (fun _ => false) t = false := by
  simp [SS.bdot]

/-- The identity Pauli acts trivially. -/
lemma pauliAct_id (phi : SS.State 6 ℂ) :
    SS.pauliAct (⟨fun _ => false, fun _ => false⟩ : SS.PauliString 6) phi = phi := by
  funext t
  simp only [SS.pauliAct, idPauli_numY, pow_zero, one_mul, SS.bxor_zero,
    bdot_zero_left, SS.signC_false]

/-- `|0_L>` is a unit vector. -/
theorem c36_normalized : SS.innerC c36 c36 = 1 := by
  have h := matElt_eq c0z c0z L0 L0_nodup c0z_vanishes
    (⟨fun _ => false, fun _ => false⟩ : SS.PauliString 6)
  rw [pauliAct_id] at h
  show SS.innerC (stC c0z) (stC c0z) = 1
  rw [h, idPauli_numY, pow_zero, zmat_id_c0z, toC_intCast, sc_sq]
  norm_num

/-- `|1_L>` is a unit vector. -/
theorem d36_normalized : SS.innerC d36 d36 = 1 := by
  have h := diag_eq (⟨fun _ => false, fun _ => false⟩ : SS.PauliString 6) idPauli_wt
  rw [pauliAct_id, pauliAct_id] at h
  rw [h, c36_normalized]

/-- The two logical words are orthogonal. -/
theorem c36_orthogonal_d36 : SS.innerC c36 d36 = 0 := by
  have h := offdiag01 (⟨fun _ => false, fun _ => false⟩ : SS.PauliString 6) idPauli_wt
  rwa [pauliAct_id] at h

/-- `|0_L>` vanishes off the residue-0 fiber. -/
theorem c36_vanishes_off_S0 (s : SS.BitString 6) (hs : s ∉ S0) : c36 s = 0 := by
  show sc * toC (c0z s) = 0
  rw [c0z_vanishes s (by simpa [S0] using hs), toC_zero, mul_zero]

/-- `|1_L>` vanishes off the residue-4 fiber. -/
theorem d36_vanishes_off_S1 (s : SS.BitString 6) (hs : s ∉ S1) : d36 s = 0 := by
  show sc * toC (c1z s) = 0
  rw [c1z_vanishes s (by simpa [S1] using hs), toC_zero, mul_zero]

/-! ## The twelve probabilities of each logical word -/

lemma prob_of (c : SS.BitString 6 → ZQ) (s : SS.BitString 6) (n : Int)
    (h : ZQ.mul (ZQ.conj (c s)) (c s) = z8 n 0 0 0 0 0 0 0) :
    star (stC c s) * stC c s = (n : ℂ) / 120 := by
  show star (sc * toC (c s)) * (sc * toC (c s)) = _
  rw [star_mul', ← toC_conj]
  have hz : star sc * toC (ZQ.conj (c s)) * (sc * toC (c s))
      = (star sc * sc) * toC (ZQ.mul (ZQ.conj (c s)) (c s)) := by
    rw [toC_mul]; ring
  rw [hz, h, sc_sq, toC_intCast]
  ring
'''

TAIL_END = r'''
end

end SixQubit.Orbit36Code
'''



def table_entries():
    """the twenty-nine nonidentity weight-two Paulis of the lambda_E table"""
    ents = []
    for i, j in combinations(range(1, 5), 2):
        ents.append(("X%dX%d" % (i, j), i - 1, j - 1, (1, 0), (1, 0)))
        ents.append(("Y%dY%d" % (i, j), i - 1, j - 1, (1, 1), (1, 1)))
        ents.append(("Z%dZ%d" % (i, j), i - 1, j - 1, (0, 1), (0, 1)))
    for i in range(1, 5):
        ents.append(("Z%dZ5" % i, i - 1, 4, (0, 1), (0, 1)))
        ents.append(("Z%dZ6" % i, i - 1, 5, (0, 1), (0, 1)))
    ents.append(("X5X6", 4, 5, (1, 0), (1, 0)))
    ents.append(("Y5Y6", 4, 5, (1, 1), (1, 1)))
    ents.append(("Z5Z6", 4, 5, (0, 1), (0, 1)))
    return ents


def lean_bool(b):
    return "true" if b else "false"


def emit_lambda_table(table):
    """29 explicit lambda_E theorems, values read off the exact ZQ sums"""
    from fractions import Fraction as Fr

    out = []
    A = out.append
    A("""
/-! ## The diagonal scalars `lambda_E`

The closing table of the chapter.  `lambda_of` reads a diagonal scalar off the
exact `ZQ` sum; each entry below is then one `decide` for the number of `Y`
factors and one `decide` for the twelve-term sum. -/

lemma lambda_of (P : SS.PauliString 6) (n : Int) (e : Nat)
    (hy : P.numY = e) (hz : zmat c0z c0z L0 P.x P.z = z8 n 0 0 0 0 0 0 0) :
    SS.innerC c36 (SS.pauliAct P c36) = (Complex.I ^ e) * (n : ℂ) / 120 := by
  show SS.innerC (stC c0z) (SS.pauliAct P (stC c0z)) = _
  rw [matElt_eq c0z c0z L0 L0_nodup c0z_vanishes P, hy, hz, toC_intCast, sc_sq]
  ring
""")
    for name, i, j, ti, tj in table_entries():
        m = (ti[0] << i) | (tj[0] << j)
        k = (ti[1] << i) | (tj[1] << j)
        val = table[(m, k)]
        assert val[1:] == (0,) * 7, (name, val)
        n = val[0]
        e = popcount(m & k)
        assert e in (0, 2), (name, e)
        lam = Fr(n, 120) if e == 0 else -Fr(n, 120)
        lam_s = ("%d/%d" % (lam.numerator, lam.denominator)) if lam.denominator != 1             else str(lam.numerator)
        extra = ", Complex.I_sq" if e == 2 else ""
        A("""
/-- `lambda_E = %s` for `E = %s`. -/
theorem lambda_%s :
    SS.innerC c36 (SS.pauliAct
      (SS.pauli2 (%d : Fin 6) %d (%s, %s) (%s, %s)) c36) = %s := by
  rw [lambda_of _ (%s) %d (by decide) (by decide)%s]
  norm_num
""" % (lam_s, name, name, i, j,
       lean_bool(ti[0]), lean_bool(ti[1]), lean_bool(tj[0]), lean_bool(tj[1]),
       lam_s, ("(%d)" % n) if n < 0 else str(n), e, extra))
    A("""
/-- **Every other weight-`<= 2` Pauli has `lambda_E = 0`**, and all off-diagonal
matrix elements vanish (`offdiag01`, `offdiag10`).  Together with the twenty-nine
entries above and `c36_normalized` this is the closing table of the chapter. -/
theorem lambda_eq_zero (P : SS.PauliString 6) (hw : P.wt ≤ 2)
    (hns : inTable P.x P.z = false) :
    SS.innerC c36 (SS.pauliAct P c36) = 0 := by
  have h := checkB_of_wt P hw
  simp only [checkB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  have hzero : zmat c0z c0z L0 P.x P.z = ZQ.zero := by
    rcases h.2 with h1 | h1
    · rw [hns] at h1; simp at h1
    · exact h1
  show SS.innerC (stC c0z) (SS.pauliAct P (stC c0z)) = 0
  rw [matElt_eq c0z c0z L0 L0_nodup c0z_vanishes P, hzero, toC_zero, mul_zero]
""")
    return "".join(out)


def emit(amp0, amp1, table):
    E = EXPECTED_S0
    out = [PREAMBLE]
    A = out.append

    A("-- the twelve points of `S_0`, written x1x2x3x4;x5x6\n")
    for nm in NAMES0:
        s = E[nm]
        A("def p_%s : SS.BitString 6 := %s  -- %s;%s\n"
          % (nm, lean_bs(s), s[:4], s[4:]))
    A("\n-- the twelve points of `S_4 = complement S_0`\n")
    for nm in NAMES0:
        s = cmpl(E[nm])
        A("def q_%s : SS.BitString 6 := %s  -- %s;%s\n"
          % (nm, lean_bs(s), s[:4], s[4:]))
    A("\n/-- The six vertex points of `S_0`. -/\n")
    A("def LV0 : List (SS.BitString 6) := [%s]\n"
      % ", ".join("p_" + nm for nm in VERT))
    A("\n/-- The six edge points of `S_0`. -/\n")
    A("def LE0 : List (SS.BitString 6) := [%s]\n"
      % ", ".join("p_" + nm for nm in EDGE))
    A("\n/-- The six vertex points of `S_4`. -/\n")
    A("def LV1 : List (SS.BitString 6) := [%s]\n"
      % ", ".join("q_" + nm for nm in VERT))
    A("\n/-- The six edge points of `S_4`. -/\n")
    A("def LE1 : List (SS.BitString 6) := [%s]\n"
      % ", ".join("q_" + nm for nm in EDGE))
    A("\n/-- The support of `|psi_0>`. -/\n")
    A("def L0 : List (SS.BitString 6) := LV0 ++ LE0\n")
    A("\n/-- The support of `|psi_1>`. -/\n")
    A("def L1 : List (SS.BitString 6) := LV1 ++ LE1\n")
    A(FIBER_BLOCK)

    def amp_fn(name, amp, doc):
        A("\n" + doc + "\n")
        A("def %s (x : SS.BitString 6) : ZQ :=\n" % name)
        for idx, (m, val) in enumerate(sorted(amp.items())):
            pre = "  " + ("if" if idx == 0 else "else if")
            A("%s num x = %d then %s\n" % (pre, m, zq_lit(val)))
        A("  else ZQ.zero\n")

    amp_fn("c0z", amp0,
           "/-- `2 sqrt 30` times the canonical bottom word `|psi_0>`. -/")
    amp_fn("c1z", amp1,
           "/-- `2 sqrt 30` times the canonical top word `|psi_1>`. -/")

    A("\ntheorem c0z_vanishes : ∀ x : SS.BitString 6, x ∉ L0 → c0z x = ZQ.zero := by\n")
    A("  decide\n")
    A("\ntheorem c1z_vanishes : ∀ x : SS.BitString 6, x ∉ L1 → c1z x = ZQ.zero := by\n")
    A("  decide\n")
    codes = sorted(64 * m + k for (m, k), v in table.items() if v != ZERO)
    assert len(codes) == 30, len(codes)
    body = "  [" + ", ".join(str(c) for c in codes) + "]"
    A(TAIL_A.replace("@@TBLCODES@@", body))

    for word, cz, lv, le, lbl in (("c36", "c0z", "LV0", "LE0", "0"),
                                  ("d36", "c1z", "LV1", "LE1", "1")):
        A("""
/-- The six vertex amplitudes of `|psi_%s>` have probability `1/10`. -/
theorem %s_prob_vertex : ∀ s ∈ %s, star (%s s) * %s s = 1/10 := by
  intro s hs
  have h : ZQ.mul (ZQ.conj (%s s)) (%s s) = z8 12 0 0 0 0 0 0 0 := by
    revert hs; revert s; decide
  show star (stC %s s) * stC %s s = _
  rw [prob_of %s s 12 h]
  norm_num

/-- The six edge amplitudes of `|psi_%s>` have probability `1/15`. -/
theorem %s_prob_edge : ∀ s ∈ %s, star (%s s) * %s s = 1/15 := by
  intro s hs
  have h : ZQ.mul (ZQ.conj (%s s)) (%s s) = z8 8 0 0 0 0 0 0 0 := by
    revert hs; revert s; decide
  show star (stC %s s) * stC %s s = _
  rw [prob_of %s s 8 h]
  norm_num

/-- `|psi_%s>` has full twelve-term support. -/
theorem %s_ne_zero : ∀ s ∈ %s, %s s ≠ 0 := by
  intro s hs hz
  rcases List.mem_append.mp hs with h | h
  · have := %s_prob_vertex s h
    rw [hz, star_zero, zero_mul] at this
    norm_num at this
  · have := %s_prob_edge s h
    rw [hz, star_zero, zero_mul] at this
    norm_num at this
""" % (lbl, word, lv, word, word, cz, cz, cz, cz, cz,
       lbl, word, le, word, word, cz, cz, cz, cz, cz,
       lbl, word, "L" + lbl, word, word, word))

    A(emit_lambda_table(table))
    A(TAIL_END)
    return "".join(out)


def main():
    check_fibers()
    amp0, amp1 = build_amps()
    table = check_kl(amp0, amp1)
    got = check_table(table)
    check_probabilities(amp0, amp1)
    print("orbit 36 witness: fibers ok, 154 Pauli constraints ok,")
    print("  lambda_E table ok (%d nonzero entries), probabilities {1/10, 1/15} ok"
          % len(got))
    if "--check" in sys.argv:
        return
    text = emit(amp0, amp1, table)
    out = os.path.join(ROOT, "SixQubit", "Orbit36Code.lean")
    with open(out, "w", encoding="utf-8", newline="\n") as f:
        f.write(text)
    print("wrote %s (%d lines)" % (out, len(text.splitlines())))


if __name__ == "__main__":
    main()
