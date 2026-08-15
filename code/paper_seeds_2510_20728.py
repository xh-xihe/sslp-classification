"""Hard-coded |0_L> codewords from arXiv:2510.20728 (He, Lu, Zeng 2026),
'Co-Designing Quantum Codes with Transversal Diagonal Gates via Multi-Agent
Systems', Appendix F (10 feasible ((7,2,3)) BD16 codes) and Appendix G
(2 no-go ((7,2,3)) BD16 candidates).

All twelve weight vectors are the same as in arXiv:2504.20847 (the 12 BD16
candidates in Sec. 6.3.1). Ten of them appear with explicit closed-form
|0_L> in 2510.20728 Appendix F; we encode them here as fresh
representatives (different points in the parametric families from
2504.20847's bd16_01..10). The remaining two weight vectors are proven
infeasible in 2510.20728 Appendix G: no |0_L> exists, so the dyadic Bell
lift is vacuous on them.

Convention: m = 8, residues (S_0, S_1) = (0, 7), self-complementary
|1_L> = X^7 |0_L>. The 10 fresh seeds are named bd16v2_a, ..., bd16v2_j
to indicate they are the 'v2' representatives from arXiv:2510.20728.
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

from generate_lift_codewords import Seed, make_seed  # noqa: E402


# ----------------------------------------------------------------------
# Helpers (mirror those of paper_seeds_2504_20847.py to keep behavior
# bit-identical wrt make_seed_norm).
# ----------------------------------------------------------------------

def _normalize(terms):
    s = math.sqrt(sum(abs(c) ** 2 for _, c in terms))
    if s == 0:
        return list(terms)
    return [(b, c / s) for b, c in terms]


def _verify_a_mod(name, n, m, a, supports):
    """Every displayed support s must satisfy A_a(s) ≡ 0 (mod m), i.e.\\ live
    in the residue-0 sector. (|1_L> = X^7|0_L> handles the top sector.)"""
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
    return make_seed(name, m, a, nterms, description=description,
                     self_complementary=True)


# Convenience aliases for compactness in the codeword tables below.
i = 1j
rt = math.sqrt


# ======================================================================
# Appendix F: 10 feasible BD16 codes (Lean-verified existence; we re-check
# Theorem 4.4 on these explicit representatives).
# ======================================================================

# ----- F.a: w = (1, 2, 2, 2, 2, 3, 3); 2-parameter family, alpha_i = 0 ---
def seed_bd16v2_a() -> Seed:
    """4|0_L> = e^{i a1}|0000000> + sqrt3|0111100> + sqrt3|1001110>
              + sqrt2|1010101> + sqrt2|1011001> + e^{i a2}|1110010>
              + 2i|0100011>,   default a1=a2=0;  Lambda^2 = 21/8."""
    terms = [
        ("0000000", 1.0),
        ("0111100", rt(3.0)),
        ("1001110", rt(3.0)),
        ("1010101", rt(2.0)),
        ("1011001", rt(2.0)),
        ("1110010", 1.0),
        ("0100011", 2.0 * i),
    ]
    return make_seed_norm(
        "bd16v2_a", 8, (1, 2, 2, 2, 2, 3, 3), terms,
        description="App F.a of arXiv:2510.20728; w=(1,2,2,2,2,3,3), "
                    "2-param family at a1=a2=0; Lambda^2=21/8",
    )


# ----- F.b: w = (1, 1, 2, 2, 2, 2, 5); 192-element discrete family -----
def seed_bd16v2_b() -> Seed:
    """4|0_L> = |0000000> - sqrt3|0011110>
              + i sqrt2 (|0100101> - |0110001> - |1000011> + |1001001>)
              + i (|1101110> + |1110110> + |1111010> + |1111100>);
       Lambda^2 = 33/16.  (Same representative as bd16_02 from 2504.20847;
       the PDF's nested parentheses are reconstructed from norm.)"""
    terms = [
        ("0000000",                       1.0),
        ("0011110",                      -rt(3.0)),
        ("0100101",     i * rt(2.0)),
        ("0110001",    -i * rt(2.0)),
        ("1000011",    -i * rt(2.0)),
        ("1001001",     i * rt(2.0)),
        ("1101110",     i),
        ("1110110",     i),
        ("1111010",     i),
        ("1111100",     i),
    ]
    return make_seed_norm(
        "bd16v2_b", 8, (1, 1, 2, 2, 2, 2, 5), terms,
        description="App F.b of arXiv:2510.20728; w=(1,1,2,2,2,2,5); "
                    "Lambda^2=33/16; matches bd16_02 of arXiv:2504.20847",
    )


# ----- F.c: w = (0, 1, 2, 2, 3, 3, 4); 3 isolated exact solutions ------
def seed_bd16v2_c() -> Seed:
    """4|0_L> = |0000000> + i sqrt2|0010110> - i sqrt3|0100011>
              - sqrt2|0111100> + sqrt2|1001110> - sqrt3|1011001>
              + sqrt2|1100101> + i|1111010>;
       Lambda^2 in {51/16, 23/16, 15/8} for the 3 representatives;
       we encode the first."""
    terms = [
        ("0000000",        1.0),
        ("0010110",   i * rt(2.0)),
        ("0100011",  -i * rt(3.0)),
        ("0111100",      -rt(2.0)),
        ("1001110",       rt(2.0)),
        ("1011001",      -rt(3.0)),
        ("1100101",       rt(2.0)),
        ("1111010",   i),
    ]
    return make_seed_norm(
        "bd16v2_c", 8, (0, 1, 2, 2, 3, 3, 4), terms,
        description="App F.c of arXiv:2510.20728; w=(0,1,2,2,3,3,4); "
                    "first of 3 isolated solutions",
    )


# ----- F.d: w = (1, 1, 2, 2, 3, 3, 3); 1-parameter family, alpha = 0 ---
def seed_bd16v2_d() -> Seed:
    """4|0_L>(alpha=0) = |0000000>
        + (sqrt2/1) e^{i a}|0001011> - (sqrt2/1) e^{i a}|0010011>
        + (i sqrt3/1) e^{i a}|0111100>
        + (i sqrt6/2) e^{i a}|1011001> - (i sqrt6/2) e^{i a}|1011010>
        - (i sqrt10/2) e^{i a}|1100101> - (i sqrt10/2) e^{i a}|1100110>;
        Lambda = 9 sqrt2 / 8."""
    terms = [
        ("0000000",                    1.0),
        ("0001011",         rt(2.0)),
        ("0010011",        -rt(2.0)),
        ("0111100",     i * rt(3.0)),
        ("1011001",    (i * rt(6.0)) / 2.0),
        ("1011010",   -(i * rt(6.0)) / 2.0),
        ("1100101",   -(i * rt(10.0)) / 2.0),
        ("1100110",   -(i * rt(10.0)) / 2.0),
    ]
    return make_seed_norm(
        "bd16v2_d", 8, (1, 1, 2, 2, 3, 3, 3), terms,
        description="App F.d of arXiv:2510.20728; w=(1,1,2,2,3,3,3); "
                    "1-param family at alpha=0; Lambda=9 sqrt2/8",
    )


# ----- F.e: w = (1, 1, 2, 2, 2, 3, 4); uniform-magnitude representative -
def seed_bd16v2_e() -> Seed:
    """4|0_L> = |0000000> - i|0001101> + i|0010101>
              - i|0011001> - i|0100011> - |0101110>
              + |0110110> + |0111010> - i|1000011>
              + |1001110> + |1010110> - |1011010>
              - |1100101> - |1101001> - |1110001> - i|1111100>;
       Lambda^2 in {7/16, 11/16, 19/16}; first representative."""
    terms = [
        ("0000000",  1.0),
        ("0001101", -i),
        ("0010101",  i),
        ("0011001", -i),
        ("0100011", -i),
        ("0101110", -1.0),
        ("0110110",  1.0),
        ("0111010",  1.0),
        ("1000011", -i),
        ("1001110",  1.0),
        ("1010110",  1.0),
        ("1011010", -1.0),
        ("1100101", -1.0),
        ("1101001", -1.0),
        ("1110001", -1.0),
        ("1111100", -i),
    ]
    return make_seed_norm(
        "bd16v2_e", 8, (1, 1, 2, 2, 2, 3, 4), terms,
        description="App F.e of arXiv:2510.20728; w=(1,1,2,2,2,3,4); "
                    "uniform-magnitude representative",
    )


# ----- F.f: w = (1, 1, 1, 2, 3, 3, 4); self-complementary -------------
def seed_bd16v2_f() -> Seed:
    """4|0_L> = |0000000> + (i sqrt2)|0001110> + sqrt2|0110110>
              + sqrt3|0111001> + (i sqrt10/2)|1000011>
              + (i sqrt10/2)|1000101> + (i sqrt6/2)|1111010>
              - (i sqrt6/2)|1111100>;
       Lambda^2 = 75/32."""
    terms = [
        ("0000000",                  1.0),
        ("0001110",     i * rt(2.0)),
        ("0110110",         rt(2.0)),
        ("0111001",         rt(3.0)),
        ("1000011",  (i * rt(10.0)) / 2.0),
        ("1000101",  (i * rt(10.0)) / 2.0),
        ("1111010",  (i * rt(6.0)) / 2.0),
        ("1111100", -(i * rt(6.0)) / 2.0),
    ]
    return make_seed_norm(
        "bd16v2_f", 8, (1, 1, 1, 2, 3, 3, 4), terms,
        description="App F.f of arXiv:2510.20728; w=(1,1,1,2,3,3,4); "
                    "self-complementary; Lambda^2=75/32",
    )


# ----- F.g: w = (1, 1, 1, 2, 2, 4, 4); uniform-magnitude solution -----
def seed_bd16v2_g() -> Seed:
    """4|0_L> has 16 basis terms, all magnitude 1/4, with sign/phase
       pattern as in App F.g (first of 3 uniform-magnitude solutions)."""
    terms = [
        ("0000000",  1.0),
        ("0000011", -1.0),
        ("0001101",  1.0),
        ("0001110",  1.0),
        ("0110101",  i),
        ("0110110", -i),
        ("0111001", -i),
        ("0111010",  i),
        ("1010101",  i),
        ("1010110",  i),
        ("1011001", -i),
        ("1011010", -i),
        ("1100101",  i),
        ("1100110", -i),
        ("1101001",  i),
        ("1101010", -i),
    ]
    return make_seed_norm(
        "bd16v2_g", 8, (1, 1, 1, 2, 2, 4, 4), terms,
        description="App F.g of arXiv:2510.20728; w=(1,1,1,2,2,4,4); "
                    "first of 3 uniform-magnitude solutions",
    )


# ----- F.h: w = (1, 1, 1, 2, 2, 3, 5); self-complementary -------------
def seed_bd16v2_h() -> Seed:
    """|0_L> = (1/4)|0000000> + (1/4)|0000011>
            - (i sqrt3/8) sum_{s in T3} |s>
            - (sqrt6/8) sum_{s in T6} |s>
            - (sqrt10/8)|1110001>
            + (i sqrt5/8)(|1110110> + |1111010>);
       Lambda^2 = 369/128.
       T3 = 6 strings of integer sum 9 ((8+1)/2 schema); T6 = 3 strings."""
    T3 = ["0010101", "0011001", "0100101",
          "0101001", "1000101", "1001001"]
    T6 = ["0011110", "0101110", "1001110"]
    terms = [
        ("0000000", 0.5),    # 1/4 normalized to 0.5 below (auto-normalizer)
        ("0000011", 0.5),
    ]
    # We encode using the displayed (un-normalized) amplitudes; make_seed_norm
    # auto-normalizes the whole vector.
    terms = [
        ("0000000",  1.0),
        ("0000011",  1.0),
    ]
    for s in T3:
        terms.append((s, -i * rt(3.0) / 2.0))  # (i sqrt3/8) * 4 = i sqrt3 / 2
    for s in T6:
        terms.append((s, -rt(6.0) / 2.0))
    terms.append(("1110001", -rt(10.0) / 2.0))
    terms.append(("1110110",  i * rt(5.0) / 2.0))
    terms.append(("1111010",  i * rt(5.0) / 2.0))
    return make_seed_norm(
        "bd16v2_h", 8, (1, 1, 1, 2, 2, 3, 5), terms,
        description="App F.h of arXiv:2510.20728; w=(1,1,1,2,2,3,5); "
                    "self-complementary; Lambda^2=369/128",
    )


# ----- F.i: w = (1, 1, 1, 1, 3, 4, 4); paste-ready representative ------
def seed_bd16v2_i() -> Seed:
    """4|0_L> = |0000000> + |0000011> + i|0001101> - i|0001110>
              + i|0010101> - i|0010110> + i|0100101> - i|0100110>
              + i|1000101> - i|1000110> + i sqrt3|1111001>
              + i sqrt3|1111010>;
       Lambda^2 = 31/8.  128-element family in total."""
    terms = [
        ("0000000",       1.0),
        ("0000011",       1.0),
        ("0001101",       i),
        ("0001110",      -i),
        ("0010101",       i),
        ("0010110",      -i),
        ("0100101",       i),
        ("0100110",      -i),
        ("1000101",       i),
        ("1000110",      -i),
        ("1111001",   i * rt(3.0)),
        ("1111010",   i * rt(3.0)),
    ]
    return make_seed_norm(
        "bd16v2_i", 8, (1, 1, 1, 1, 3, 4, 4), terms,
        description="App F.i of arXiv:2510.20728; w=(1,1,1,1,3,4,4); "
                    "paste-ready representative of 128-element family; "
                    "Lambda^2=31/8",
    )


# ----- F.j: w = (1, 1, 1, 1, 3, 3, 5); continuous (x,y,z) family -----
def seed_bd16v2_j() -> Seed:
    """8|0_L>(alpha=0) = 2(|0000000> - |0000011> - |0000101>)
                       + 2(|0011110> + |1100110>)         (e^{i alpha} = 1)
                       + (|0101110> + |1010110>)
                       + 3(|0110110> + |1001110>)         (integer 3, not sqrt3)
                       + sqrt6 (|1011001> + |1101001>
                                - |0111001> - |1110001>);
       Lambda^2 = 177/64.  (Same representative as bd16_10 from 2504.20847;
       the PDF's nested parentheses in the last sqrt6-group are reconstructed
       from norm.  Note: the '3/8' coefficient in App F.j is an integer 3,
       not sqrt3, which pdftotext rendered ambiguously.)"""
    terms = [
        # (1/4) group (3 terms, anchor + balance)
        ("0000000",                   2.0),
        ("0000011",                  -2.0),
        ("0000101",                  -2.0),
        # (1/4) group (2 terms, e^{i alpha} = 1 at alpha=0)
        ("0011110",                   2.0),
        ("1100110",                   2.0),
        # (1/8) group (2 terms)
        ("0101110",                   1.0),
        ("1010110",                   1.0),
        # (3/8) group (2 terms): integer 3, not sqrt3
        ("0110110",                   3.0),
        ("1001110",                   3.0),
        # (sqrt6/8) group (4 terms with signs)
        ("1011001",                   rt(6.0)),
        ("1101001",                   rt(6.0)),
        ("0111001",                  -rt(6.0)),
        ("1110001",                  -rt(6.0)),
    ]
    return make_seed_norm(
        "bd16v2_j", 8, (1, 1, 1, 1, 3, 3, 5), terms,
        description="App F.j of arXiv:2510.20728; w=(1,1,1,1,3,3,5); "
                    "closed-form representative at alpha=0; Lambda^2=177/64; "
                    "matches bd16_10 of arXiv:2504.20847",
    )


# ======================================================================
# Appendix G: 2 infeasible BD16 cases (no |0_L> exists).
# We record them as data (residue-0 support set + Lean-verified
# infeasibility note); they are NOT runnable seeds.
# ======================================================================

NO_GO_CASES = [
    {
        "name":  "bd16v2_nogo1",
        "n":     7,
        "m":     8,
        "a":     (1, 1, 1, 2, 2, 2, 6),
        "b":     (0, 7),
        "C0":    ["0000000", "0000011", "0000101", "0001001",
                  "0110001", "0111110", "1010001", "1011110",
                  "1100001", "1101110"],
        "n_eqs": 17,
        "proof_section": "Appendix G.1, Proposition 1",
        "description": "App G.1 of arXiv:2510.20728: 17-equation "
                       "subsystem proves no complex amplitudes on C_0 "
                       "satisfy weight-<=2 KL; lift is vacuous.",
    },
    {
        "name":  "bd16v2_nogo2",
        "n":     7,
        "m":     8,
        "a":     (0, 1, 1, 2, 3, 3, 5),
        "b":     (0, 7),
        "C0":    ["0000000", "0000011", "0000101", "0001110",
                  "0011001", "0101001", "0110110", "1000000",
                  "1000011", "1000101", "1001110", "1011001",
                  "1101001", "1110110"],
        "n_eqs": 19,
        "proof_section": "Appendix G.2, Proposition 2",
        "description": "App G.2 of arXiv:2510.20728: 19-equation "
                       "subsystem proves no complex amplitudes on C_0 "
                       "satisfy weight-<=2 KL; lift is vacuous.",
    },
]


# ======================================================================
# Public registries
# ======================================================================

# Map (paper section, transversal group, bell_liftable, note)
CODE_META_2510 = {
    "bd16v2_a": ("arXiv:2510 App F.a", "BD16", True, "w=(1,2,2,2,2,3,3)"),
    "bd16v2_b": ("arXiv:2510 App F.b", "BD16", True, "w=(1,1,2,2,2,2,5)"),
    "bd16v2_c": ("arXiv:2510 App F.c", "BD16", True, "w=(0,1,2,2,3,3,4)"),
    "bd16v2_d": ("arXiv:2510 App F.d", "BD16", True, "w=(1,1,2,2,3,3,3)"),
    "bd16v2_e": ("arXiv:2510 App F.e", "BD16", True, "w=(1,1,2,2,2,3,4)"),
    "bd16v2_f": ("arXiv:2510 App F.f", "BD16", True, "w=(1,1,1,2,3,3,4)"),
    "bd16v2_g": ("arXiv:2510 App F.g", "BD16", True, "w=(1,1,1,2,2,4,4)"),
    "bd16v2_h": ("arXiv:2510 App F.h", "BD16", True, "w=(1,1,1,2,2,3,5)"),
    "bd16v2_i": ("arXiv:2510 App F.i", "BD16", True, "w=(1,1,1,1,3,4,4)"),
    "bd16v2_j": ("arXiv:2510 App F.j", "BD16", True, "w=(1,1,1,1,3,3,5)"),
}


def get_all_2510_seeds() -> List[Seed]:
    """Return the 10 Appendix-F seeds in alphabetical order."""
    builders = [
        seed_bd16v2_a, seed_bd16v2_b, seed_bd16v2_c, seed_bd16v2_d,
        seed_bd16v2_e, seed_bd16v2_f, seed_bd16v2_g, seed_bd16v2_h,
        seed_bd16v2_i, seed_bd16v2_j,
    ]
    return [b() for b in builders]


if __name__ == "__main__":
    # Tiny self-test: just build and print norms.
    for s in get_all_2510_seeds():
        nz = sum(abs(c) ** 2 for c in s.zero.values())
        no = sum(abs(c) ** 2 for c in s.one.values())
        print(f"  {s.name:>12s}  |0|^2={nz:.6f}  |1|^2={no:.6f}  "
              f"|supp 0|={len(s.zero)}  |supp 1|={len(s.one)}")
