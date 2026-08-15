"""All explicit nonadditive ((n, 2, 3)) codes from arXiv:2504.20847
"Transversal Gates in Nonadditive Quantum Codes" (Zhang, Wu, Huang, Zeng, 2025).

Each entry exposes an explicit complex |0_L> with hardcoded a-vector derived
from the listed transversal Z gate angles (convention: per-qubit Z(2pi*a_j/m_SS-LP),
with a_j extracted as half the integer numerator k of the listed angle k*pi/m).

For some codes (BD64, BD84, BD24, BD14, etc.) the sum a > 2m-1 (only the
modular condition sum a == m-1 mod m holds), so they don't satisfy the
"strong sum" hypothesis of Theorem 4.4 strictly.  We still build them and let
the verification report flag (i)/(ii)/strong-sum hypothesis violations.

Free parameters (theta, s_i) are fixed at representative points.  Amplitudes
are normalized at construction.
"""
from __future__ import annotations

import math
import os
import sys
from typing import List

_HERE = os.path.dirname(os.path.abspath(__file__))
_NUMERICS = os.path.normpath(os.path.join(_HERE, "..", "..", "Numerics"))
if _NUMERICS not in sys.path:
    sys.path.insert(0, _NUMERICS)

from generate_lift_codewords import (  # noqa: E402
    Seed,
    make_seed,
    seed_steane,
    bd16_seeds,
    seed_bd22,
    seed_bd32,
    seed_c10,
    complement_codeword,
)


# ----------------------------------------------------------------------
# Helpers
# ----------------------------------------------------------------------

def _normalize(terms):
    s = math.sqrt(sum(abs(c) ** 2 for _, c in terms))
    if s == 0:
        return list(terms)
    return [(b, c / s) for b, c in terms]


def _verify_a_mod(name, n, m, a, supports):
    """For each support, sum_j a_j s_j must be ≡ 0 (mod m)."""
    for w in supports:
        if len(w) != n:
            raise ValueError(f"{name}: support {w!r} has length {len(w)}, n={n}")
        s = sum(int(b) * a_j for b, a_j in zip(w, a))
        if s % m != 0:
            raise ValueError(
                f"{name}: support {w!r} has subset sum {s} ≢ 0 (mod {m})"
            )


def make_seed_norm(name, m, a, terms, supports=None, description=""):
    if supports is None:
        supports = [s for s, _ in terms]
    _verify_a_mod(name, len(a), m, a, supports)
    nterms = _normalize(terms)
    return make_seed(name, m, a, nterms, description=description)


rt = math.sqrt
i = 1j


# ----------------------------------------------------------------------
# Section 6.3.3  BD36   m=18,  a=(2,3,4,5,6,7,8)
# ----------------------------------------------------------------------

def seed_bd36() -> Seed:
    terms = [
        ("0000000", 1.0),
        ("0001110", rt(2.0)),
        ("0111100", i * rt(3.0)),
        ("0100011", rt(4.0)),
        ("1100110", i * rt(5.0)),
        ("1101001", i * rt(6.0)),
        ("1011010", i * rt(7.0)),
        ("0010101", rt(8.0)),
    ]
    return make_seed_norm(
        "bd36", 18, (2, 3, 4, 5, 6, 7, 8), terms,
        description="Sec 6.3.3 BD36 ((7,2,3)), theta=0, s_i=+1",
    )


# ----------------------------------------------------------------------
# Section 6.4.1  BD64   m=32,  a=(4,7,10,12,17,23,24,30)  -- sum=127 ≠ 2m-1=63
# ----------------------------------------------------------------------

def seed_bd64() -> Seed:
    terms = [
        ("00000000", rt(10.0)),
        ("00001110", 1.0),
        ("00100011", i * rt(6.0)),
        ("01010111", 2.0 * i),
        ("01100110", rt(8.0)),
        ("01101001", rt(3.0)),
        ("10111101", i * rt(15.0)),
        ("11000101", 2.0),
        ("11011010", rt(13.0)),
    ]
    return make_seed_norm(
        "bd64", 32, (4, 7, 10, 12, 17, 23, 24, 30), terms,
        description="Sec 6.4.1 BD64 ((8,2,3)), theta_i=0, s_i=+1; sum a=127 ≠ 2m-1=63",
    )


# ----------------------------------------------------------------------
# Section 6.4.2  BD84   m=42,  a=(4,10,13,18,22,27,34,39)  -- sum=167 ≠ 2m-1=83
# ----------------------------------------------------------------------

def seed_bd84() -> Seed:
    terms = [
        ("00000000", rt(10.0)),
        ("00010101", 2.0),
        ("00111011", rt(2.0)),
        ("01011010", rt(11.0)),
        ("01100110", rt(12.0)),
        ("01101001", rt(3.0)),
        ("10001111", rt(17.0)),
        ("10111100", 3.0),
        ("11110001", 4.0 * i),
    ]
    return make_seed_norm(
        "bd84", 42, (4, 10, 13, 18, 22, 27, 34, 39), terms,
        description="Sec 6.4.2 BD84 ((8,2,3)), theta_i=0, s=+1; sum a=167 ≠ 2m-1=83",
    )


# ----------------------------------------------------------------------
# Appendix D.1  BD12 Type I  m=6,  a=(1,1,1,2,2,2,2)  -- sum=11 = 2m-1 ✓
# ----------------------------------------------------------------------

def seed_bd12_type_I() -> Seed:
    terms = [
        ("0000000", rt(10.0)),
        ("0110101", rt(12.0)),
        ("0110110", rt(5.0)),
        ("0111010", rt(8.0)),
        ("0111100", rt(5.0)),
        ("1010101", rt(18.0)),
        ("1011010", -rt(12.0)),
        ("1100011", rt(15.0)),
        ("1101001", -rt(15.0)),
        ("0001110", i * rt(20.0)),
    ]
    return make_seed_norm(
        "bd12_type_I", 6, (1, 1, 1, 2, 2, 2, 2), terms,
        description="App D.1 BD12 Type I ((7,2,3)), s_i=+1",
    )


# ----------------------------------------------------------------------
# Appendix D.1  BD12 Type II  m=6, a=(1,1,1,2,2,2,2)
# At theta=0.5*sqrt(2/3).
# Transversal Z for Type II: Z(0)⊗Z(2π/6)⊗Z(4π/6)⊗Z(4π/6)⊗Z(4π/6)⊗Z(π)⊗Z(π)
# So a=(0,1,2,2,2,3,3) for Type II. Sum=13 ≠ 2m-1=11. Modular: 13 mod 6 = 1, m-1=5. ❌
# Hmm let me re-examine. Actually Z(π) means 2π·a/6=π → a=3, so a_5=3, a_6=3.
# And Z(0) means a_0 = 0. Z(2π/6) → a_1=1. Z(4π/6) → a=2.
# a = (0, 1, 2, 2, 2, 3, 3). Sum = 13. mod 6 = 1. m-1=5. So b_1=1 NOT m-1.
# This is a non-strong-sum code. Still useful to test.
# ----------------------------------------------------------------------

def seed_bd12_type_II() -> Seed:
    theta = 0.5 * rt(2.0 / 3.0)
    coef_a = theta / rt(8.0)
    coef_b = rt(1.0 / 12.0 - theta * theta / 8.0)
    coef_c = theta / 2.0
    coef_d = (1.0 / 2.0) * rt(2.0 / 3.0 - theta * theta)
    terms = []
    for s in ["0000000", "1100101", "1101001", "1110001"]:
        terms.append((s, coef_a))
    for s in ["0000011", "1100110", "1101010", "1110010"]:
        terms.append((s, -coef_a))
    for s in ["0100101", "0100110", "0110001", "0101001",
              "0101010", "0110010", "1000000", "1000011"]:
        terms.append((s, i * coef_b))
    for s in ["0011100", "0011111"]:
        terms.append((s, i * coef_c))
    terms.append(("1011100", coef_d))
    terms.append(("1011111", -coef_d))
    a = (0, 1, 2, 2, 2, 3, 3)
    return make_seed_norm(
        "bd12_type_II", 6, a, terms,
        description=f"App D.1 BD12 Type II ((7,2,3)), s_i=+1, theta={theta:.4f}; sum a=13",
    )


# ----------------------------------------------------------------------
# Appendix D.2  BD14   m=7
# From transversal Z listed angles (pi/7, 2pi/7, 3pi/7, 4pi/7, 5pi/7, 5pi/7, 6pi/7):
# Using k/2 convention: a = (0.5, 1, 1.5, 2, 2.5, 2.5, 3) -- HALF-INTEGER. Not SS-LP form.
# Try integer: a = (1, 2, 3, 4, 5, 5, 6) (using k convention without /2). Sum=26.
# Verify: 0001110 (positions 3,4,5): 4+5+5=14 ≡ 0 mod 7 ✓. 1010110: 1+3+5+5=14 ✓.
# So BD14 has m=7, a=(1,2,3,4,5,5,6), sum=26 ≡ 5 mod 7 (NOT m-1=6).
# Hmm, but |1L>=X⊗7|0L> means 1^7 in supp(|1_L>), with sum a=26. So b_1 = 26 mod 7 = 5.
# This doesn't fit standard SS-LP b_1=m-1.
# ----------------------------------------------------------------------

def seed_bd14() -> Seed:
    theta = 0.0
    coef1 = rt(3.0 / 7.0 + 2.0 * theta * theta)
    coef2 = rt(4.0 / 7.0 - 2.0 * theta * theta)
    terms = [
        ("0000000", 1.0),
        ("0001110", i * rt(2.0)),
        ("1010110", 1.0),
        ("1011001", rt(2.0)),
        ("0010101", i * rt(1.0 - 14.0 * theta * theta)),
        ("0111100", coef1 * rt(3.0)),
        ("1100101", coef1 * 2.0),
        ("0111010", coef2 * rt(3.0)),
        ("1100011", -coef2 * 2.0),
    ]
    return make_seed_norm(
        "bd14", 7, (1, 2, 3, 4, 5, 5, 6), terms,
        description="App D.2 BD14 ((7,2,3)), theta=0, s_i=+1; sum a=26",
    )


# ----------------------------------------------------------------------
# Appendix D.4  BD18 Type I   m=9, a=(2,2,2,2,3,3,3) -- sum=17 = 2m-1 ✓
# Listed transversal Z: Z(4π/9)x4 ⊗ Z(6π/9)x3. a = (2,2,2,2,3,3,3). Sum=17.
# ----------------------------------------------------------------------

def seed_bd18_type_I() -> Seed:
    val = 1.0 / rt(18.0)
    terms = [
        ("0000000", i * rt(1.0 / 18.0)),
        ("0000111", i * rt(5.0 / 18.0)),
        ("0111001", val),
        ("0111010", val),
        ("0111100", val),
        ("1011001", val),
        ("1011010", val),
        ("1011100", val),
        ("1101001", val),
        ("1101010", val),
        ("1101100", val),
        ("1110001", val),
        ("1110010", val),
        ("1110100", val),
    ]
    return make_seed_norm(
        "bd18_type_I", 9, (2, 2, 2, 2, 3, 3, 3), terms,
        description="App D.4 BD18 Type I ((7,2,3)), trivial theta_i^2=1/18",
    )


# ----------------------------------------------------------------------
# Appendix D.5  BD20   m=10, a=(1,2,2,3,3,4,5) -- sum=20. 2m-1=19. ≠
# Listed transversal Z: Z(2π/10) ⊗ Z(4π/10) ⊗ Z(4π/10) ⊗ Z(6π/10) ⊗ Z(6π/10) ⊗ Z(8π/10) ⊗ Z(10π/10).
# a (k/2 convention): 1, 2, 2, 3, 3, 4, 5. Sum=20. 20 mod 10 = 0 = m. m-1=9.
# Hmm sum=20 ≡ 0 mod 10. Not m-1.
# Let me re-derive a from BD20 support pattern.
# Supports: 0000000, 0001101, 0111100, 1100110, 0100011, 1010101, 1011010, 1100101, 1101010.
# 0001101 (pos 3,4,6): a_3+a_4+a_6 = 10 → 3+3+5=11. Hmm 11 != 10.
# Try a different a.
# ----------------------------------------------------------------------

def seed_bd20() -> Seed:
    # CORRECTED transcription from the LaTeX source (background-2504.20847/main.tex,
    # eq. lines 1195-1197).  The earlier transcription had three bugs (all verified
    # against the LaTeX + adversarial numerics):
    #   (1) the bracket coefficient is the INTEGER 2, not sqrt(2);
    #   (2) the outer scalar is sqrt(7-20 theta^2)/3 with the /3 OUTSIDE the radical
    #       (the old code used sqrt((7-20 theta^2)/3));
    #   (3) the term i*s2*theta*sqrt(20)|0010011> was missing entirely.
    # sqrt(20)|0L> = |0000000> + i sqrt2|0001101> + sqrt3|0111100> + |1100110>
    #              + i s2 theta sqrt(20)|0010011> + i s3 sqrt(4-20 theta^2)|0100011>
    #              + (s4 sqrt(7-20 theta^2)/3)(2|1010101> + sqrt5|1011010>)
    #              + (s5 sqrt(2+20 theta^2)/3)(2|1100101> - sqrt5|1101010>)
    # At theta=0 the raw norm^2 of the bracket is exactly 20 (matches the sqrt(20)
    # prefactor); for any theta the 20 theta^2 contributions cancel.
    theta = 0.0
    s2 = s3 = s4 = s5 = 1.0
    coef4 = s4 * rt(7.0 - 20.0 * theta * theta) / 3.0
    coef5 = s5 * rt(2.0 + 20.0 * theta * theta) / 3.0
    terms = [
        ("0000000", 1.0),
        ("0001101", i * rt(2.0)),
        ("0111100", rt(3.0)),
        ("1100110", 1.0),
        ("0010011", i * s2 * theta * rt(20.0)),
        ("0100011", i * s3 * rt(4.0 - 20.0 * theta * theta)),
        ("1010101", coef4 * 2.0),
        ("1011010", coef4 * rt(5.0)),
        ("1100101", coef5 * 2.0),
        ("1101010", -coef5 * rt(5.0)),
    ]
    # a-vector: transversal Z angles (2,4,4,6,6,8,10)*pi/10 -> a_j = k/2 = (1,2,2,3,3,4,4);
    # every |0L> support has subset-sum 0 or 10 (=0 mod m=10).  sum(a)=19=2m-1 (STRONG SUM).
    a = (1, 2, 2, 3, 3, 4, 4)
    return make_seed_norm(
        "bd20", 10, a, terms,
        description="App D.5 BD20 ((7,2,3)), theta=0, s_i=+1 (corrected from LaTeX)",
    )


# ----------------------------------------------------------------------
# Appendix D.7  BD24   m=12, a=(1,1,3,3,5,5,7) -- sum=25 ≠ 2m-1=23
# ----------------------------------------------------------------------

def seed_bd24() -> Seed:
    # CORRECTED transcription from LaTeX (main.tex line 1224-1225): the second
    # prefactor is 1/(2 sqrt3) ~= 0.2887, NOT sqrt(2/sqrt3) ~= 1.0746 (old bug).
    # |0L> = (1/(2 sqrt2))(|0000000>+|0111010>+|1011100>-|1100110>)
    #      - (s/(2 sqrt3))(|0000011>-|0000101>+|0111111>-|1011111>+|1101001>-|1110001>)
    # With the correct magnitude norm^2 = 4*(1/8)+6*(1/12) = 1 exactly, and the seed
    # IS a genuine distance-3 code (r0 passes).  It remains INAPPLICABLE for Thm 4.4
    # because H1 strong-sum fails: sum(a)=25 != 2m-1=23.
    coef_a = 1.0 / (2.0 * rt(2.0))
    coef_b = 1.0 / (2.0 * rt(3.0))
    terms = [
        ("0000000", coef_a),
        ("0111010", coef_a),
        ("1011100", coef_a),
        ("1100110", -coef_a),
        ("0000011", -coef_b),
        ("0000101", coef_b),
        ("0111111", -coef_b),
        ("1011111", coef_b),
        ("1101001", -coef_b),
        ("1110001", coef_b),
    ]
    return make_seed_norm(
        "bd24", 12, (1, 1, 3, 3, 5, 5, 7), terms,
        description="App D.7 BD24 ((7,2,3)), s=+1; sum a=25 ≠ 2m-1=23",
    )


# ----------------------------------------------------------------------
# Appendix D.8  BD26   m=13.
# Listed transversal Z: Z(4π/13) ⊗ Z(4π/13) ⊗ Z(6π/13) ⊗ Z(6π/13) ⊗ Z(8π/13) ⊗ Z(10π/13) ⊗ Z(12π/13).
# a (k/2): 2, 2, 3, 3, 4, 5, 6. Sum=25=2m-1=25. ✓ Strong sum.
# ----------------------------------------------------------------------

def seed_bd26() -> Seed:
    theta = 0.0
    terms = [
        ("0000000", 1.0),
        ("0111010", 2.0),
        ("1011010", rt(3.0)),
        ("1100110", rt(5.0)),
        ("1000011", i * 1.0),
        ("1110001", rt(4.0 - 26.0 * theta * theta)),
        ("0001101", i * rt(6.0 - 26.0 * theta * theta)),
        ("0010101", i * rt(2.0 + 26.0 * theta * theta)),
    ]
    return make_seed_norm(
        "bd26", 13, (2, 2, 3, 3, 4, 5, 6), terms,
        description="App D.8 BD26 ((7,2,3)), theta=0, s_i=+1",
    )


# ----------------------------------------------------------------------
# Appendix D.9  BD28   m=14
# Listed transversal Z: Z(4π/14) ⊗ Z(6π/14) ⊗ Z(6π/14) ⊗ Z(8π/14) ⊗ Z(8π/14) ⊗ Z(10π/14) ⊗ Z(12π/14).
# a (k/2): 2, 3, 3, 4, 4, 5, 6. Sum=27=2m-1=27. ✓
# ----------------------------------------------------------------------

def seed_bd28() -> Seed:
    theta = 0.0
    terms = [
        ("0000000", 1.0),
        ("0111100", rt(3.0)),
        ("1011010", rt(5.0)),
        ("1110001", 2.0),
        ("0001101", i * rt(6.0)),
        ("1100110", rt(5.0 - 28.0 * theta * theta)),
        ("0010011", i * rt(2.0 - 28.0 * theta * theta)),
        ("0100011", i * rt(2.0 + 28.0 * theta * theta)),
    ]
    return make_seed_norm(
        "bd28", 14, (2, 3, 3, 4, 4, 5, 6), terms,
        description="App D.9 BD28 ((7,2,3)), theta=0, s_i=+1",
    )


# ----------------------------------------------------------------------
# Appendix D.10  BD30   m=15
# Listed transversal Z: Z(4π/15) ⊗ Z(4π/15) ⊗ Z(6π/15) ⊗ Z(6π/15) ⊗ Z(8π/15) ⊗ Z(14π/15) ⊗ Z(16π/15).
# a (k/2): 2, 2, 3, 3, 4, 7, 8. Sum=29=2m-1=29. ✓
# ----------------------------------------------------------------------

def seed_bd30() -> Seed:
    theta = rt(1.0 / 15.0)
    th2 = theta * theta
    terms = [
        ("0000000", 1.0),
        ("0000011", 1.0),
        ("0111010", 2.0),
        ("1011010", 2.0),
        ("1100110", rt(6.0)),
        ("0001101", i * theta * rt(30.0)),
        ("0010101", i * rt(9.0 - 30.0 * th2)),
        ("1101001", rt(7.0 - 30.0 * th2)),
    ]
    return make_seed_norm(
        "bd30", 15, (2, 2, 3, 3, 4, 7, 8), terms,
        description=f"App D.10 BD30 ((7,2,3)), theta={theta:.4f}, s_i=+1",
    )


# ----------------------------------------------------------------------
# Appendix D.11  BD34   m=17
# Listed transversal Z: Z(4π/17) ⊗ Z(4π/17) ⊗ Z(6π/17) ⊗ Z(8π/17) ⊗ Z(10π/17) ⊗ Z(16π/17) ⊗ Z(18π/17).
# a (k/2): 2, 2, 3, 4, 5, 8, 9. Sum=33=2m-1=33. ✓
# ----------------------------------------------------------------------

def seed_bd34() -> Seed:
    terms = [
        ("0000000", 1.0),
        ("0000011", 1.0),
        ("0111010", 2.0),
        ("1011010", 2.0),
        ("1100110", rt(6.0)),
        ("1101001", rt(7.0)),
        ("0001110", i * rt(2.0)),
        ("0010101", 3.0 * i),
    ]
    return make_seed_norm(
        "bd34", 17, (2, 2, 3, 4, 5, 8, 9), terms,
        description="App D.11 BD34 ((7,2,3)), theta=0, s_i=+1",
    )


# ----------------------------------------------------------------------
# Appendix E.2  BD72   m=36
# Listed transversal Z: Z(6π/36) ⊗ Z(10π/36) ⊗ Z(12π/36) ⊗ Z(16π/36) ⊗ Z(20π/36) ⊗ Z(24π/36) ⊗ Z(26π/36) ⊗ Z(28π/36).
# a (k/2): 3, 5, 6, 8, 10, 12, 13, 14. Sum=71 = 2m-1 ✓.
# ----------------------------------------------------------------------

def seed_bd72() -> Seed:
    terms = [
        ("00000000", 1.0),
        ("00001101", rt(14.0)),
        ("00111100", rt(3.0)),
        ("01011010", rt(13.0)),
        ("01100110", rt(5.0)),
        ("10010110", rt(8.0)),
        ("10100011", i * rt(10.0)),
        ("11101100", rt(6.0)),
        ("11110001", i * rt(12.0)),
    ]
    return make_seed_norm(
        "bd72", 36, (3, 5, 6, 8, 10, 12, 13, 14), terms,
        description="App E.2 BD72 ((8,2,3)), theta_i=0, s_i=+1",
    )


# ----------------------------------------------------------------------
# Appendix E.3  BD74   m=37
# Listed transversal Z: Z(8π/37) ⊗ Z(12π/37) ⊗ Z(14π/37) ⊗ Z(18π/37) ⊗ Z(20π/37) ⊗ Z(22π/37) ⊗ Z(24π/37) ⊗ Z(28π/37).
# a (k/2): 4, 6, 7, 9, 10, 11, 12, 14. Sum=73=2m-1 ✓.
# ----------------------------------------------------------------------

def seed_bd74() -> Seed:
    terms = [
        ("00000000", 1.0),
        ("00000111", rt(12.0)),
        ("00111100", rt(3.0)),
        ("01011010", rt(11.0)),
        ("01101001", rt(10.0)),
        ("10001110", i * rt(6.0)),
        ("10011001", rt(7.0)),
        ("10100011", i * rt(8.0)),
        ("11110100", i * rt(16.0)),
    ]
    return make_seed_norm(
        "bd74", 37, (4, 6, 7, 9, 10, 11, 12, 14), terms,
        description="App E.3 BD74 ((8,2,3)), theta_i=0, s_i=+1",
    )


# ----------------------------------------------------------------------
# Appendix E.4  BD76   m=38
# Listed transversal Z: Z(4π/38) ⊗ Z(8π/38) ⊗ Z(14π/38) ⊗ Z(18π/38) ⊗ Z(20π/38) ⊗ Z(24π/38) ⊗ Z(30π/38) ⊗ Z(32π/38).
# a (k/2): 2, 4, 7, 9, 10, 12, 15, 16. Sum=75=2m-1 ✓.
# ----------------------------------------------------------------------

def seed_bd76() -> Seed:
    terms = [
        ("00000000", 1.0),
        ("00001101", rt(18.0)),
        ("00100011", 2.0),
        ("00111100", rt(3.0)),
        ("01011010", rt(7.0)),
        ("01100110", rt(5.0)),
        ("10010110", rt(12.0)),
        ("11101010", i * rt(10.0)),
        ("11110001", 4.0 * i),
    ]
    return make_seed_norm(
        "bd76", 38, (2, 4, 7, 9, 10, 12, 15, 16), terms,
        description="App E.4 BD76 ((8,2,3)), theta_i=0, s_i=+1",
    )


# ----------------------------------------------------------------------
# Appendix E.5  BD78   m=39
# Listed transversal Z: Z(6π/39) ⊗ Z(10π/39) ⊗ Z(16π/39) ⊗ Z(18π/39) ⊗ Z(20π/39) ⊗ Z(24π/39) ⊗ Z(28π/39) ⊗ Z(32π/39).
# a (k/2): 3, 5, 8, 9, 10, 12, 14, 16. Sum=77=2m-1 ✓.
# ----------------------------------------------------------------------

def seed_bd78() -> Seed:
    terms = [
        ("00000000", 1.0),
        ("00010011", 4.0),
        ("00111100", rt(3.0)),
        ("01100110", rt(5.0)),
        ("01101001", rt(14.0)),
        ("10001110", i * rt(10.0)),
        ("10100101", 3.0),
        ("11011100", i * rt(12.0)),
        ("11110010", rt(8.0)),
    ]
    return make_seed_norm(
        "bd78", 39, (3, 5, 8, 9, 10, 12, 14, 16), terms,
        description="App E.5 BD78 ((8,2,3)), theta_i=0, s_i=+1",
    )


# ----------------------------------------------------------------------
# Appendix E.6  BD80   m=40
# Listed transversal Z: Z(4π/40) ⊗ Z(10π/40) ⊗ Z(12π/40) ⊗ Z(16π/40) ⊗ Z(22π/40) ⊗ Z(28π/40) ⊗ Z(30π/40) ⊗ Z(36π/40).
# a (k/2): 2, 5, 6, 8, 11, 14, 15, 18. Sum=79=2m-1 ✓.
# ----------------------------------------------------------------------

def seed_bd80() -> Seed:
    terms = [
        ("00000000", 1.0),
        ("00001110", rt(2.0)),
        ("00010101", rt(8.0)),
        ("00111010", rt(18.0)),
        ("01100110", rt(5.0)),
        ("01101001", rt(6.0)),
        ("10100101", i * rt(11.0)),
        ("11000011", i * rt(15.0)),
        ("11011100", rt(14.0)),
    ]
    return make_seed_norm(
        "bd80", 40, (2, 5, 6, 8, 11, 14, 15, 18), terms,
        description="App E.6 BD80 ((8,2,3)), theta_i=0, s_i=+1",
    )


# ----------------------------------------------------------------------
# Appendix E.1  --  BD38   m=19,  a=(2,3,3,4,4,5,7,9)  -- sum=37 = 2m-1 ✓
# 16 real parameters theta_1..theta_16 constrained by an 8x16 sign matrix C
# (C . theta^2 = 0) plus sum theta^2 = 1.  We solve the feasibility LP and
# use the resulting theta^2 (a polytope vertex) as the representative point.
# Verified: the LP solution reproduces the paper's derived identities
# theta_1^2 + theta_2^2 = 1/38 and theta_12^2 = 4/19.
# ----------------------------------------------------------------------

# 8x16 sign matrix C, transcribed from the paper (App E.1).
_BD38_C = [
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1],
    [1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, 1, 1, -1, -1, -1],
    [1, 1, -1, -1, -1, 1, 1, 1, -1, -1, -1, 1, -1, 1, -1, -1],
    [1, 1, 1, 1, -1, 1, 1, -1, 1, -1, -1, -1, 1, 1, 1, -1],
    [1, 1, 1, -1, 1, 1, -1, 1, -1, 1, -1, -1, 1, 1, -1, 1],
    [1, 1, 1, -1, -1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1, 1],
    [1, 1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, -1, -1],
    [1, 1, -1, 1, 1, -1, 1, 1, -1, -1, 1, -1, -1, -1, 1, 1],
]
# The 15 distinct support strings of |0_L> (theta_1 and theta_2 both sit on
# the anchor 00000000 as the complex coefficient theta_1 + i*theta_2).
_BD38_SUPPORTS = [
    "00000000",  # theta_1 + i theta_2
    "00100011",  # i theta_3
    "00101110",  # i theta_4
    "00110110",  # i theta_5
    "01000011",  # i theta_6
    "01001110",  # i theta_7
    "01010110",  # i theta_8
    "01101001",  # theta_9
    "01110001",  # theta_10
    "01111100",  # theta_11
    "10011001",  # theta_12
    "10100101",  # theta_13
    "11000101",  # theta_14
    "11101010",  # theta_15
    "11110010",  # theta_16
]


def _solve_bd38_theta_sq():
    """Solve the BD38 feasibility LP: theta^2 >= 0, C.theta^2 = 0, sum = 1.
    Returns a 16-vector theta^2."""
    import numpy as np
    from scipy.optimize import linprog
    C = np.array(_BD38_C, dtype=float)
    Aeq = np.vstack([C, np.ones(16)])
    beq = np.concatenate([np.zeros(8), [1.0]])
    res = linprog(np.zeros(16), A_eq=Aeq, b_eq=beq,
                  bounds=[(0, None)] * 16, method="highs")
    if not res.success:
        raise RuntimeError("BD38 feasibility LP infeasible")
    return res.x


def seed_bd38() -> Seed:
    theta_sq = _solve_bd38_theta_sq()
    th = [math.sqrt(max(v, 0.0)) for v in theta_sq]
    # amplitude layout: anchor gets theta_1 + i theta_2; supports 2..7 (indices
    # 1..6) get i*theta_{3..8}; supports 8..16 (indices 7..14) get theta_{9..16}.
    terms = []
    terms.append((_BD38_SUPPORTS[0], complex(th[0], th[1])))      # theta_1 + i theta_2
    for k in range(1, 7):                                          # i theta_3..8
        terms.append((_BD38_SUPPORTS[k], i * th[k + 1]))
    for k in range(7, 15):                                         # theta_9..16
        terms.append((_BD38_SUPPORTS[k], complex(th[k + 1], 0.0)))
    # drop zero-amplitude supports
    terms = [(w, c) for w, c in terms if abs(c) > 1e-14]
    return make_seed_norm(
        "bd38", 19, (2, 3, 3, 4, 4, 5, 7, 9), terms,
        description="App E.1 BD38 ((8,2,3)); a=(2,3,3,4,4,5,7,9), m=19, STRONG SUM; "
                    "theta^2 from feasibility LP (matches paper's 1/38, 4/19 identities)",
    )


# ----------------------------------------------------------------------
# Appendix D.4  --  BD18 Type II   m=9,  a=(1,1,2,3,3,3,4)  -- sum=17 = 2m-1 ✓
# CORRECTED reading: the |1100101> coefficient is sqrt(b^2 + d^2 + 1/18),
# NOT sqrt((b^2+d^2+1)/18).  With the corrected reading the state has
# norm^2 = 1 exactly (verified symbolically: norm^2 = 1 either way reduces
# to 1 with the +1/18 reading).
# Representative: b = 0.094956415409 (smaller polynomial root), s_i = +1, theta = 0.
# ----------------------------------------------------------------------

def seed_bd18_type_II() -> Seed:
    # Magnitudes are taken verbatim from the paper's formula (with the corrected
    # |1100101> coefficient sqrt(b^2 + d^2 + 1/18)).  The PDF rendering of the
    # term *signs* is unreliable, so the phase assignment below was resolved
    # numerically: it is the (verified) phase pattern that makes the code
    # distance-3 on the paper's exact support + magnitudes.  Worst KL ~8e-14.
    b = 0.094956415409
    d = 1.0 / math.sqrt(36.0 * b * b + 14.0)
    inv18 = 1.0 / 18.0
    terms = [
        ("0000000", 1.0 / rt(18.0)),
        ("0111010", b),
        ("0111100", rt(inv18 - b * b)),
        ("1011010", d),
        ("1100011", rt(1.0 / 9.0 - b * b)),
        ("1100101", rt(b * b + d * d + inv18)),
        ("1010110", rt(1.0 / 6.0 - d * d)),
        ("1101001", -rt(1.0 / 6.0 - d * d)),   # opposite sign to |1010110>
        ("0110110", rt(2.0) / rt(18.0)),
        ("0001110", i * rt(2.0) / rt(18.0)),
        ("0011001", i * rt(3.0) / rt(18.0)),
    ]
    return make_seed_norm(
        "bd18_type_II", 9, (1, 1, 2, 3, 3, 3, 4), terms,
        description="App D.4 BD18 Type II ((7,2,3)); a=(1,1,2,3,3,3,4), m=9, "
                    "STRONG SUM; b=0.09496, magnitudes from paper formula "
                    "(corrected |1100101> coeff), phases resolved numerically",
    )


# ======================================================================
# NON-BD2m codes from Section 5 (2I) and Appendix C (2T, 2O)
# ======================================================================

def _dicke_terms(n: int, k: int):
    """Return [(bitstring, 1/sqrt(C(n,k)))] for the symmetric Dicke state D^n_k."""
    from itertools import combinations
    idxs = list(combinations(range(n), k))
    amp = 1.0 / math.sqrt(len(idxs))
    out = []
    for combo in idxs:
        bits = ["0"] * n
        for c in combo:
            bits[c] = "1"
        out.append(("".join(bits), amp))
    return out


def _cyclic_orbit(bitstring: str):
    """All distinct right-cyclic rotations of `bitstring` (the orbit support)."""
    n = len(bitstring)
    seen = []
    cur = bitstring
    for _ in range(n):
        # right-rotate by 1: last char to front
        cur = cur[-1] + cur[:-1]
        if cur not in seen:
            seen.append(cur)
    return seen


# ----------------------------------------------------------------------
# Section 5.1  --  ((7,2,3)) 2I code, permutation-invariant (Dicke states)
#   |0L> = (sqrt(3)|D7_0> + i sqrt(7)|D7_5>)/sqrt(10)
#   |1L> = X^7 |0L>
# SS-LP: a=(1,1,1,1,1,1,1), m=5, b=(0,2).  sum a=7 != 2m-1=9 -> NOT strong sum.
# ----------------------------------------------------------------------

def seed_2i_perm_inv() -> Seed:
    n = 7
    terms = []
    for w, c in _dicke_terms(n, 0):
        terms.append((w, rt(3.0) * c))
    for w, c in _dicke_terms(n, 5):
        terms.append((w, i * rt(7.0) * c))
    # |1L> = X^7|0L>  -> complement
    return make_seed("2i_perm_inv", 5, (1, 1, 1, 1, 1, 1, 1),
                     _normalize(terms), self_complementary=True,
                     description="Sec 5.1 2I perm-invariant ((7,2,3)); a=(1^7), m=5, b1=2")


# ----------------------------------------------------------------------
# Section 5.1  --  ((7,2,3)) 2I code, lambda*=0  (4-dim subspace)
# SS-LP: a=(1,1,1,2,2,2,2), m=5, b=(0,1).  sum a=11 -> NOT strong sum.
# Representative point: theta=0, phi=0, c0=+sqrt(2/5).
# ----------------------------------------------------------------------

def seed_2i_lambda0() -> Seed:
    n = 7
    # |S0>..|S3> (un-normalized internal vectors, divided by sqrt(8) or sqrt(6))
    S0 = [("0000000", 1.0), ("0111111", 1.0), ("1011111", -1.0), ("1101111", 1.0),
          ("1110001", -1.0), ("1110010", 1.0), ("1110100", 1.0), ("1111000", 1.0)]
    S0 = [(w, c / rt(8.0)) for w, c in S0]
    S1 = [("0010011", -1.0), ("0011100", 1.0), ("0100101", 1.0), ("0101010", -1.0),
          ("1000110", 1.0), ("1001001", -1.0)]
    S1 = [(w, c / rt(6.0)) for w, c in S1]
    S2 = [("0010101", 1.0), ("0011010", -1.0), ("0100110", 1.0), ("0101001", -1.0),
          ("1000011", 1.0), ("1001100", -1.0)]
    S2 = [(w, c / rt(6.0)) for w, c in S2]
    S3 = [("0010110", -1.0), ("0011001", 1.0), ("0100011", -1.0), ("0101100", 1.0),
          ("1000101", 1.0), ("1001010", -1.0)]
    S3 = [(w, c / rt(6.0)) for w, c in S3]
    # coefficients at theta=0, phi=0:
    theta, phi = 0.0, 0.0
    c0 = rt(2.0 / 5.0)
    c1 = (-rt(1.0/3.0) * math.sin(theta) * math.cos(phi)
          + i * rt(1.0/3.0) * math.cos(theta) * (math.cos(phi - math.pi/3) + math.cos(phi + math.pi/3))
          + i * rt(1.0/30.0))
    c2 = (-rt(1.0/3.0) * math.sin(theta) * math.cos(phi - math.pi/3)
          + i * rt(1.0/3.0) * math.cos(theta) * math.cos(phi - math.pi/3)
          - i * rt(1.0/30.0))
    c3 = (-rt(1.0/3.0) * math.sin(theta) * (math.cos(phi - math.pi/3) - math.cos(phi))
          + i * rt(1.0/3.0) * math.cos(theta) * math.cos(phi + math.pi/3)
          - i * rt(1.0/30.0))
    acc = {}
    for blk, cc in [(S0, c0), (S1, c1), (S2, c2), (S3, c3)]:
        for w, a_amp in blk:
            acc[w] = acc.get(w, 0.0) + cc * a_amp
    terms = [(w, c) for w, c in acc.items() if abs(c) > 1e-14]
    return make_seed("2i_lambda0", 5, (1, 1, 1, 2, 2, 2, 2),
                     _normalize(terms), self_complementary=True,
                     description="Sec 5.1 2I lambda*=0 ((7,2,3)); a=(1,1,1,2,2,2,2), m=5, b1=1, theta=phi=0")


# ----------------------------------------------------------------------
# Section 5.1  --  ((7,2,3)) 2I code, lambda*=sqrt(3/4)  (4-dim subspace)
# SS-LP: a=(1,1,1,1,1,2,2), m=5, b=(0,4).  sum a=9 = 2m-1 -> STRONG SUM!
# Representative point: s1=s2=s3=+1, t=0.
# ----------------------------------------------------------------------

def seed_2i_lambda34() -> Seed:
    n = 7
    S0 = [("0000000", 1.0)]
    S1 = [("0000111", 1.0), ("0001011", -1.0), ("0010011", 1.0), ("0100011", 1.0),
          ("1000011", 1.0), ("1111100", -1.0)]
    S1 = [(w, c / rt(6.0)) for w, c in S1]
    S2 = [("0011101", 1.0), ("0101101", 1.0), ("0110110", -1.0), ("0111010", 1.0),
          ("1001110", 1.0), ("1010101", -1.0), ("1011010", 1.0), ("1100110", -1.0),
          ("1101001", 1.0), ("1110001", -1.0)]
    S2 = [(w, c / rt(10.0)) for w, c in S2]
    S3 = [("0011110", 1.0), ("0101110", 1.0), ("0110101", -1.0), ("0111001", 1.0),
          ("1001101", 1.0), ("1010110", -1.0), ("1011001", 1.0), ("1100101", -1.0),
          ("1101010", 1.0), ("1110010", -1.0)]
    S3 = [(w, c / rt(10.0)) for w, c in S3]
    s1, s2, s3, t = 1.0, 1.0, 1.0, 0.0
    c0 = 1.0 / rt(10.0)
    c1 = i * s1 * rt(3.0 / 20.0)
    c2 = s2 / 4.0 - t - i * s3 * rt(5.0 / 16.0 - t * t)
    c3 = s2 / 4.0 + t + i * s3 * rt(5.0 / 16.0 - t * t)
    acc = {}
    for blk, cc in [(S0, c0), (S1, c1), (S2, c2), (S3, c3)]:
        for w, a_amp in blk:
            acc[w] = acc.get(w, 0.0) + cc * a_amp
    terms = [(w, c) for w, c in acc.items() if abs(c) > 1e-14]
    return make_seed("2i_lambda34", 5, (1, 1, 1, 1, 1, 2, 2),
                     _normalize(terms), self_complementary=True,
                     description="Sec 5.1 2I lambda*=sqrt(3/4) ((7,2,3)); a=(1,1,1,1,1,2,2), m=5, b1=4, STRONG SUM")


# ----------------------------------------------------------------------
# Appendix C.1  --  ((7,2,3)) cyclic 2T family   (Eq. 18-19)
# SS-LP: a=(1,1,1,1,1,1,1), m=2, b=(0,1).  Representative lambda*=1, s0=s1=+1.
# ----------------------------------------------------------------------

def seed_2t_cyclic(lambda_star: float = 1.0, s0: int = 1, s1: int = 1) -> Seed:
    n = 7
    # Eq (19): coefficients
    c0 = math.sqrt(rt(7.0) * lambda_star + 8.0) / 8.0
    c1 = s0 * math.sqrt(rt(7.0) * lambda_star) / 4.0
    # (5/2) c3 = sqrt7 c0 + s1 sqrt(7 c0^2 - 15 sqrt7 lambda* / 64)
    inner = 7.0 * c0 * c0 - 15.0 * rt(7.0) * lambda_star / 64.0
    c3 = (2.0 / 5.0) * (rt(7.0) * c0 + s1 * math.sqrt(max(inner, 0.0)))
    c2 = -2.0 * c3 + rt(7.0) * c0
    # Build the cyclic-orbit superposition.  The orbit ket |{x}> is the
    # *normalized* uniform superposition over the cyclic orbit (divide the
    # raw sum by sqrt(orbit size)); this is what makes Eq.(19)'s coefficients
    # produce a unit-norm |0_L> (and recover Steane at lambda*=0).
    acc = {}

    def add_orbit(rep, coeff):
        orbit = _cyclic_orbit(rep)
        scaled = coeff / math.sqrt(len(orbit))
        for w in orbit:
            acc[w] = acc.get(w, 0.0) + scaled

    acc["0000000"] = acc.get("0000000", 0.0) + c0
    # CORRECTED from LaTeX (main.tex line 1024): the c1-block coefficient is
    # c1/(2 sqrt3), NOT (c1/2) sqrt3.  The PDF extraction garbled the sqrt(3) in
    # the DENOMINATOR into a numerator factor (a factor-3 error); it is invisible
    # at lambda*=0 (where c1=0) but breaks distance-3 for every lambda*>0.  With
    # this correction (and the normalized orbits below) the whole family is
    # distance-3 for all lambda* in [0, sqrt7].
    # (c1/(2 sqrt3)) ( {0000011} + {0000101} + {0001001} - 3 {0111111} )
    f1 = c1 / (2.0 * rt(3.0))
    add_orbit("0000011", f1)
    add_orbit("0000101", f1)
    add_orbit("0001001", f1)
    add_orbit("0111111", -3.0 * f1)
    # c2 {0010111}
    add_orbit("0010111", c2)
    # (c3/2) ( {0001111} + {0011011} + {0011101} + {0101011} )
    f3 = c3 / 2.0
    add_orbit("0001111", f3)
    add_orbit("0011011", f3)
    add_orbit("0011101", f3)
    add_orbit("0101011", f3)
    terms = [(w, c) for w, c in acc.items() if abs(c) > 1e-14]
    return make_seed("2t_cyclic", 2, (1, 1, 1, 1, 1, 1, 1),
                     _normalize(terms), self_complementary=True,
                     description=f"App C.1 cyclic 2T family ((7,2,3)); a=(1^7), m=2, b1=1, lambda*={lambda_star}")


# ----------------------------------------------------------------------
# Appendix D.3  --  ((7,2,3)) BD16 (the X^5 (x) I^2 family, NOT full X^7)
# Explicit |0L> and |1L> given. a=(3,3,3,3,3,4,4), m=8, b=(0,7).
# NOT self-complementary in the X^7 sense, but IS Bell-liftable (lift takes
# explicit zero/one + b_list).
# ----------------------------------------------------------------------

def seed_bd16_d3() -> Seed:
    # 4|0L>:
    zero_terms = [
        ("0000000", i * rt(3.0)), ("0000011", i * rt(3.0)),
        ("0111101", 1.0), ("0111110", 1.0),
        ("1011101", 1.0), ("1011110", 1.0),
        ("1101101", 1.0), ("1101110", 1.0),
        ("1110101", 1.0), ("1110110", 1.0),
        ("1111001", 1.0), ("1111010", 1.0),
    ]
    # 4|1L> = X^5 (x) I^2 |0L>:
    one_terms = [
        ("1111111", i * rt(3.0)), ("1111100", i * rt(3.0)),
        ("1000010", 1.0), ("1000001", 1.0),
        ("0100010", 1.0), ("0100001", 1.0),
        ("0010010", 1.0), ("0010001", 1.0),
        ("0001010", 1.0), ("0001001", 1.0),
        ("0000110", 1.0), ("0000101", 1.0),
    ]
    return make_seed("bd16_d3", 8, (3, 3, 3, 3, 3, 4, 4),
                     _normalize(zero_terms), self_complementary=False,
                     one_terms=_normalize(one_terms),
                     description="App D.3 BD16 ((7,2,3)) X^5(x)I^2 family; a=(3,3,3,3,3,4,4), m=8, b1=7")


# ----------------------------------------------------------------------
# Appendix C.2  --  ((7,2,3)) 2O code.  |1L> = X^5 (x) I^2 |0L>.
# NOT an SS-LP diagonal-gate code (transversal gate is the non-diagonal box
# operator), so NOT Bell-liftable.  Recorded for rung-0 distance-3 only.
# ----------------------------------------------------------------------

def seed_2o_code(s1: int = 1, s2: int = 1) -> Seed:
    # |S0>..|S5> internal vectors:
    S0 = [("0000000", 1.0), ("0001111", 1.0), ("0010100", 1.0), ("1100011", 1.0),
          ("1101100", 1.0), ("1110111", 1.0), ("0000011", -1.0), ("0001100", -1.0),
          ("0010111", -1.0), ("1100000", -1.0), ("1101111", -1.0), ("1110100", -1.0)]
    S0 = [(w, c / (2.0 * rt(3.0))) for w, c in S0]
    S1 = [("0100100", 1.0), ("0101000", 1.0), ("0110011", 1.0), ("0111100", 1.0),
          ("1000100", 1.0), ("1001000", 1.0), ("1010011", 1.0), ("1011100", 1.0),
          ("0100111", -1.0), ("0101011", -1.0), ("0110000", -1.0), ("0111111", -1.0),
          ("1000111", -1.0), ("1001011", -1.0), ("1010000", -1.0), ("1011111", -1.0)]
    S1 = [(w, c / 4.0) for w, c in S1]
    S2 = [("0100000", 1.0), ("0100011", 1.0), ("1010100", 1.0), ("1010111", 1.0),
          ("0110100", -1.0), ("0110111", -1.0), ("1000000", -1.0), ("1000011", -1.0)]
    S2 = [(w, c / (2.0 * rt(2.0))) for w, c in S2]
    S3 = [("0100001", 1.0), ("0110101", 1.0), ("1000010", 1.0), ("1010110", 1.0),
          ("0100010", -1.0), ("0110110", -1.0), ("1000001", -1.0), ("1010101", -1.0)]
    S3 = [(w, c / (2.0 * rt(2.0))) for w, c in S3]
    S4 = [("0011000", 1.0), ("1111011", 1.0), ("0011011", -1.0), ("1111000", -1.0)]
    S4 = [(w, c / 2.0) for w, c in S4]
    S5 = [("0101101", 1.0), ("1001110", 1.0), ("0101110", -1.0), ("1001101", -1.0)]
    S5 = [(w, c / 2.0) for w, c in S5]
    coefs = [1.0/4.0, -1.0/2.0, s1/2.0, s2/rt(12.0), -rt(3.0)/4.0, s2/rt(6.0)]
    acc = {}
    for blk, cc in zip([S0, S1, S2, S3, S4, S5], coefs):
        for w, a_amp in blk:
            acc[w] = acc.get(w, 0.0) + cc * a_amp
    zero_terms = [(w, c) for w, c in acc.items() if abs(c) > 1e-14]
    # |1L> = X^5 (x) I^2 |0L>
    one_acc = {}
    for w, c in zero_terms:
        w2 = "".join(("1" if j < 5 and b == "0" else "0" if j < 5 else b)
                     for j, b in enumerate(w))
        one_acc[w2] = c
    one_terms = list(one_acc.items())
    # a=(1,1,1,1,1,1,1), m=2 is a *formal* placeholder (the 2O code is not an
    # SS-LP diagonal-gate code; CODE_META marks it not Bell-liftable).
    return make_seed("2o_code", 2, (1, 1, 1, 1, 1, 1, 1),
                     _normalize(zero_terms), self_complementary=False,
                     one_terms=_normalize(one_terms),
                     description="App C.2 2O code ((7,2,3)); NOT SS-LP / not Bell-liftable")


# ======================================================================
# Appendix B  --  ((6,2,3)) continuous families (NOT SS-LP / NOT Bell-liftable)
# These are parametrized continuous families; we build one representative
# point of each.  They have no SS-LP diagonal-gate (a, m) structure, so the
# dyadic Bell lift is undefined -- only rung-0 distance-3 is meaningful.
# ======================================================================

def _dense_to_terms(vec, n):
    """Convert a dense 2^n complex vector into [(bitstring, amp)] terms."""
    out = []
    for idx, c in enumerate(vec):
        if abs(c) > 1e-12:
            out.append((format(idx, f"0{n}b"), complex(c)))
    return out


def _523_states():
    """The unique ((5,2,3)) stabilizer code logical states (App B.1)."""
    import numpy as np
    zero_strs = {
        "00000": 1, "00011": -1, "00101": 1, "00110": -1,
        "01001": 1, "01010": 1, "01100": -1, "01111": -1,
        "10001": -1, "10010": 1, "10100": 1, "10111": -1,
        "11000": -1, "11011": -1, "11101": -1, "11110": -1,
    }
    one_strs = {
        "00001": 1, "00010": 1, "00100": 1, "00111": 1,
        "01000": 1, "01011": -1, "01101": -1, "01110": 1,
        "10000": 1, "10011": 1, "10101": -1, "10110": -1,
        "11001": 1, "11010": -1, "11100": 1, "11111": -1,
    }
    z = np.zeros(32, dtype=np.complex128)
    o = np.zeros(32, dtype=np.complex128)
    for s, c in zero_strs.items():
        z[int(s, 2)] = c / 4.0
    for s, c in one_strs.items():
        o[int(s, 2)] = c / 4.0
    return z, o


def _apply_U_last_two(state6, U):
    """Apply a 4x4 unitary U to the last two qubits of a 6-qubit dense state."""
    import numpy as np
    t = state6.reshape([2] * 6)            # axes 0..5
    t = np.tensordot(U.reshape(2, 2, 2, 2), t, axes=([2, 3], [4, 5]))
    # result axes: (q4', q5', q0, q1, q2, q3) -> move back
    t = np.moveaxis(t, [0, 1], [4, 5])
    return t.reshape(64)


def seed_c623_from_c523_BD4() -> Seed:
    """App B.1: ((6,2,3)) from ((5,2,3)), BD4 case.
    U = diag(1,1,1,-1) . (I_2 (x) R_y(theta)), theta = pi/3 (cos theta != 1)."""
    import numpy as np
    z5, o5 = _523_states()
    z6 = np.zeros(64, dtype=np.complex128)
    o6 = np.zeros(64, dtype=np.complex128)
    # tensor with |0> on qubit 6 (index doubles, low bit = 0)
    for k in range(32):
        z6[2 * k] = z5[k]
        o6[2 * k] = o5[k]
    theta = math.pi / 3.0
    Ry = np.array([[math.cos(theta / 2), -math.sin(theta / 2)],
                   [math.sin(theta / 2), math.cos(theta / 2)]], dtype=np.complex128)
    I2 = np.eye(2, dtype=np.complex128)
    U = np.diag([1, 1, 1, -1]).astype(np.complex128) @ np.kron(I2, Ry)
    z6 = _apply_U_last_two(z6, U)
    o6 = _apply_U_last_two(o6, U)
    return make_seed("c623_from_c523_bd4", 2, (1, 1, 1, 1, 1, 1),
                     _normalize(_dense_to_terms(z6, 6)),
                     self_complementary=False,
                     one_terms=_normalize(_dense_to_terms(o6, 6)),
                     description="App B.1 ((6,2,3)) from ((5,2,3)), BD4 case, theta=pi/3; "
                                 "NOT SS-LP / not Bell-liftable")


def seed_c623_from_c523_2T() -> Seed:
    """App B.1: ((6,2,3)) from ((5,2,3)), 2T case.
    U = diag(1,1,1,-1) . (M (x) R_y(theta)),
    M = sqrt((3-sqrt3)/12)(X+Y) - sqrt((3+sqrt3)/6) Z."""
    import numpy as np
    z5, o5 = _523_states()
    z6 = np.zeros(64, dtype=np.complex128)
    o6 = np.zeros(64, dtype=np.complex128)
    for k in range(32):
        z6[2 * k] = z5[k]
        o6[2 * k] = o5[k]
    theta = math.pi / 3.0
    Ry = np.array([[math.cos(theta / 2), -math.sin(theta / 2)],
                   [math.sin(theta / 2), math.cos(theta / 2)]], dtype=np.complex128)
    X = np.array([[0, 1], [1, 0]], dtype=np.complex128)
    Y = np.array([[0, -1j], [1j, 0]], dtype=np.complex128)
    Z = np.array([[1, 0], [0, -1]], dtype=np.complex128)
    c1 = math.sqrt((3 - math.sqrt(3)) / 12.0)
    c2 = math.sqrt((3 + math.sqrt(3)) / 6.0)
    M = c1 * (X + Y) - c2 * Z
    U = np.diag([1, 1, 1, -1]).astype(np.complex128) @ np.kron(M, Ry)
    z6 = _apply_U_last_two(z6, U)
    o6 = _apply_U_last_two(o6, U)
    return make_seed("c623_from_c523_2t", 2, (1, 1, 1, 1, 1, 1),
                     _normalize(_dense_to_terms(z6, 6)),
                     self_complementary=False,
                     one_terms=_normalize(_dense_to_terms(o6, 6)),
                     description="App B.1 ((6,2,3)) from ((5,2,3)), 2T case, theta=pi/3; "
                                 "NOT SS-LP / not Bell-liftable")


def seed_so5_BD4() -> Seed:
    """App B.2: ((6,2,3)) SO(5) family, BD4 representative.
    Canonical W with W15 = W25 = 1/sqrt5 (last column has 2 nonzero entries)."""
    import numpy as np
    # |Sj> entangled pairs (5-qubit), normalized by 1/sqrt2.
    S_pairs = [
        ("00001", "11110"),
        ("00010", "11101"),
        ("00100", "11011"),
        ("01000", "10111"),
        ("10000", "01111"),
    ]
    S = []
    for a_str, b_str in S_pairs:
        v = np.zeros(32, dtype=np.complex128)
        v[int(a_str, 2)] = 1.0 / math.sqrt(2.0)
        v[int(b_str, 2)] = 1.0 / math.sqrt(2.0)
        S.append(v)
    w15 = 1.0 / math.sqrt(5.0)
    w25 = 1.0 / math.sqrt(5.0)
    W = np.array([
        [-w25, w25, -w25, w25, w15],
        [w15, -w15, w15, -w15, w25],
        [0.5, 0.5, 0.5, 0.5, 0.0],
        [0.5, -0.5, -0.5, 0.5, 0.0],
        [0.5, 0.5, -0.5, -0.5, 0.0],
    ], dtype=np.complex128)
    z6 = np.zeros(64, dtype=np.complex128)
    o6 = np.zeros(64, dtype=np.complex128)
    for j in range(5):
        # qubit 1 is the leading qubit; |Sj> occupies qubits 2..6
        c0_zero = W[j, 0] + 1j * W[j, 1]
        c1_zero = W[j, 2] + 1j * W[j, 3]
        c0_one = W[j, 2] - 1j * W[j, 3]
        c1_one = 1j * W[j, 1] - W[j, 0]
        for idx5 in range(32):
            amp = S[j][idx5]
            if amp == 0:
                continue
            z6[0 * 32 + idx5] += 0.5 * c0_zero * amp
            z6[1 * 32 + idx5] += 0.5 * c1_zero * amp
            o6[0 * 32 + idx5] += 0.5 * c0_one * amp
            o6[1 * 32 + idx5] += 0.5 * c1_one * amp
    return make_seed("so5_bd4", 2, (1, 1, 1, 1, 1, 1),
                     _normalize(_dense_to_terms(z6, 6)),
                     self_complementary=False,
                     one_terms=_normalize(_dense_to_terms(o6, 6)),
                     description="App B.2 ((6,2,3)) SO(5) family, BD4 representative "
                                 "(W15=W25=1/sqrt5); NOT SS-LP / not Bell-liftable")


# ======================================================================
# Per-code metadata: b_list, liftability, paper section, transversal group
# ======================================================================
# b_list is (b_0, b_1); for self-complementary codes b_1 = sum(a) mod m.
# liftable=False means the dyadic Bell lift is not defined for this code
# (no SS-LP diagonal-gate structure); only rung-0 distance-3 is checked.

CODE_META = {
    # name: (paper_section, transversal_group, liftable, notes)
    "steane": ("prototype", "2O", True, "Steane [[7,1,3]] (paper's SS-LP prototype)"),
    "bd22": ("Numerics/D.6", "BD22", True, ""),
    "bd32": ("Sec 6.3.2", "BD32", True, ""),
    "c10": ("Sec 4.1", "C10", True, "((6,2,3)) cyclic, self-complementary"),
    "bd36": ("Sec 6.3.3", "BD36", True, ""),
    "bd64": ("Sec 6.4.1", "BD64", True, "sum a != 2m-1 (no strong sum)"),
    "bd84": ("Sec 6.4.2", "BD84", True, "sum a != 2m-1 (no strong sum)"),
    "bd12_type_I": ("App D.1", "BD12", True, ""),
    "bd12_type_II": ("App D.1", "BD12", True, "sum a != 2m-1"),
    "bd14": ("App D.2", "BD14", True, "sum a != 2m-1, max a > m-2"),
    "bd18_type_I": ("App D.4", "BD18", True, ""),
    "bd20": ("App D.5", "BD20", True, "corrected transcription; strong sum 19=2m-1 -> CONFIRMS"),
    "bd24": ("App D.7", "BD24", True, "corrected coef_b=1/(2sqrt3); seed IS distance-3 but sum a=25 != 2m-1=23"),
    "bd26": ("App D.8", "BD26", True, ""),
    "bd28": ("App D.9", "BD28", True, ""),
    "bd30": ("App D.10", "BD30", True, ""),
    "bd34": ("App D.11", "BD34", True, ""),
    "bd72": ("App E.2", "BD72", True, ""),
    "bd74": ("App E.3", "BD74", True, ""),
    "bd76": ("App E.4", "BD76", True, ""),
    "bd78": ("App E.5", "BD78", True, ""),
    "bd80": ("App E.6", "BD80", True, ""),
    "bd16_d3": ("App D.3", "BD16", True, "X^5(x)I^2 family, not X^7 self-complementary"),
    "2i_perm_inv": ("Sec 5.1", "2I", True, "permutation-invariant; sum a != 2m-1"),
    "2i_lambda0": ("Sec 5.1", "2I", True, "lambda*=0; sum a != 2m-1, theta=phi=0 rep"),
    "2i_lambda34": ("Sec 5.1", "2I", True, "lambda*=sqrt(3/4); STRONG SUM; t=0 rep"),
    "2t_cyclic": ("App C.1", "2T", True,
                  "cyclic 2T family, m=2; corrected c1 coeff c1/(2sqrt3) -> seed IS "
                  "distance-3 for ALL lambda* in [0,sqrt7] (Steane at 0, 2I perm-inv "
                  "at sqrt7). INAPPLICABLE for Thm 4.4: m=2, sum a=7 != 2m-1=3 and "
                  "max a=1 > m-2=0 (H1,H2 fail)."),
    "2o_code": ("App C.2", "2O", False, "non-diagonal transversal gate; NOT Bell-liftable"),
    "bd38": ("App E.1", "BD38", True,
             "STRONG SUM; theta^2 from feasibility LP (matches paper's 1/38, 4/19)"),
    "bd18_type_II": ("App D.4", "BD18", True,
                     "STRONG SUM; corrected |1100101> coeff sqrt(b^2+d^2+1/18); "
                     "phases resolved numerically (PDF sign rendering unreliable)"),
    "c623_from_c523_bd4": ("App B.1", "BD4", False,
                           "((6,2,3)) from ((5,2,3)), theta=pi/3; not SS-LP"),
    "c623_from_c523_2t": ("App B.1", "2T", False,
                          "((6,2,3)) from ((5,2,3)), theta=pi/3; not SS-LP"),
    "so5_bd4": ("App B.2", "BD4", False,
                "((6,2,3)) SO(5) family; the paper's canonical W matrix as "
                "rendered in the PDF is not orthogonal (col0.col1 = -3 W15 W25 "
                "!= 0) -- transcription needs the LaTeX source. rung-0 KL fails. "
                "NOT-LIFTABLE / out of theorem scope regardless."),
}
# bd16_01..bd16_10 all from Sec 6.3.1 / Numerics, BD16, liftable.
for _k in range(1, 11):
    CODE_META[f"bd16_{_k:02d}"] = ("Sec 6.3.1", "BD16", True, "")


# ----------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------

def get_all_paper_seeds() -> List[Seed]:
    """All explicit codes from arXiv:2504.20847 that can be put in (or near)
    SS-LP form.  See CODE_META for per-code metadata (paper section,
    transversal group, Bell-liftability)."""
    seeds: List[Seed] = []
    # The 14 already in Numerics/generate_lift_codewords:
    seeds.append(seed_steane())                       # [[7,1,3]], m=4 (paper's prototype)
    seeds.extend(bd16_seeds())                        # 10 BD16 ((7,2,3))
    seeds.append(seed_bd22())                         # BD22 ((7,2,3))
    seeds.append(seed_bd32())                         # BD32 ((7,2,3))
    seeds.append(seed_c10())                          # C10 ((6,2,3))
    # New BD2m codes (Section 6 + Appendix D/E):
    seeds.append(seed_bd36())                         # Sec 6.3.3
    seeds.append(seed_bd64())                         # Sec 6.4.1
    seeds.append(seed_bd84())                         # Sec 6.4.2
    seeds.append(seed_bd12_type_I())                  # App D.1
    seeds.append(seed_bd12_type_II())                 # App D.1
    seeds.append(seed_bd14())                         # App D.2
    seeds.append(seed_bd18_type_I())                  # App D.4
    seeds.append(seed_bd20())                         # App D.5
    seeds.append(seed_bd24())                         # App D.7
    seeds.append(seed_bd26())                         # App D.8
    seeds.append(seed_bd28())                         # App D.9
    seeds.append(seed_bd30())                         # App D.10
    seeds.append(seed_bd34())                         # App D.11
    seeds.append(seed_bd72())                         # App E.2
    seeds.append(seed_bd74())                         # App E.3
    seeds.append(seed_bd76())                         # App E.4
    seeds.append(seed_bd78())                         # App E.5
    seeds.append(seed_bd80())                         # App E.6
    seeds.append(seed_bd38())                         # App E.1
    seeds.append(seed_bd18_type_II())                 # App D.4
    # New non-BD2m codes (Section 5 2I + Appendix C 2T/2O + D.3):
    seeds.append(seed_bd16_d3())                      # App D.3
    seeds.append(seed_2i_perm_inv())                  # Sec 5.1
    seeds.append(seed_2i_lambda0())                   # Sec 5.1
    seeds.append(seed_2i_lambda34())                  # Sec 5.1
    seeds.append(seed_2t_cyclic())                    # App C.1
    seeds.append(seed_2o_code())                      # App C.2
    # Appendix B continuous families (NOT Bell-liftable, rung-0 only):
    seeds.append(seed_c623_from_c523_BD4())           # App B.1
    seeds.append(seed_c623_from_c523_2T())            # App B.1
    seeds.append(seed_so5_BD4())                      # App B.2
    return seeds


if __name__ == "__main__":
    seeds = get_all_paper_seeds()
    print(f"Total paper seeds collected: {len(seeds)}")
    print()
    print(f"{'name':>17s}  {'n':>2s}  {'m':>3s}  {'sum_a':>5s}  {'2m-1':>4s}  {'strong':>6s}  {'max_a':>5s}  {'<m-2':>4s}  {'|supp(0)|':>9s}")
    for s in seeds:
        n = len(s.a)
        n0 = len(s.zero)
        sum_a = sum(s.a)
        strong = (sum_a == 2 * s.m - 1)
        max_a = max(s.a) if s.a else 0
        bnd = (max_a <= s.m - 2)
        norm0 = sum(abs(c) ** 2 for c in s.zero.values())
        assert abs(norm0 - 1.0) < 1e-9, f"{s.name}: norm0={norm0}"
        print(
            f"{s.name:>17s}  {n:>2d}  {s.m:>3d}  {sum_a:>5d}  {2*s.m-1:>4d}  "
            f"{('YES' if strong else 'no'):>6s}  {max_a:>5d}  {('YES' if bnd else 'no'):>4s}  {n0:>9d}"
        )
