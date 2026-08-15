# sslp_acc/sslp_utils.py
# Self-contained utilities.  API-compatible with sslp_cpu/sslp_utils.py.
#
# Precision-preserving accelerations:
# * `fraction_str` accepts both stdlib `Fraction` and `gmpy2.mpq` (same
#   string output for the same rational number).
# * `min_hamming_distance_union` is vectorized with numpy broadcasting.

import os
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, product
from typing import Any, List, Optional, Tuple

import numpy as np

# gmpy2.mpq is an exact rational with the same API as Fraction but ~3x faster
# (GMP-backed).  We optionally accept it as a rational type everywhere.
try:
    from gmpy2 import mpq as _mpq  # type: ignore
    _RATIONAL_TYPES: Tuple[type, ...] = (Fraction, type(_mpq(0)))
    HAVE_GMPY2 = True
except ImportError:  # pragma: no cover
    _RATIONAL_TYPES = (Fraction,)
    HAVE_GMPY2 = False


# ----------------------------------------------------------------------
# Formatting (string output must match sslp_cpu byte-for-byte)
# ----------------------------------------------------------------------

def fraction_str(x: Any, max_den: int = 10**12) -> str:
    """Render a number as 'a/b' or 'a'.

    Accepts:
      * Fraction or gmpy2.mpq  -> exact (no rounding)
      * int                    -> str(x)
      * float                  -> best rational within `max_den` denominator
    """
    if isinstance(x, _RATIONAL_TYPES):
        num = int(x.numerator)
        den = int(x.denominator)
        return f"{num}" if den == 1 else f"{num}/{den}"
    try:
        xf = float(x)
    except Exception:
        return str(x)
    if abs(xf) < 1e-18:
        return "0"
    fr = Fraction(xf).limit_denominator(max_den)
    return f"{fr.numerator}" if fr.denominator == 1 else f"{fr.numerator}/{fr.denominator}"


def sqrt_fraction_str(prob: Any, max_den: int = 10**12) -> str:
    return f"√({fraction_str(prob, max_den)})"


def bits_to_ket(bits_row: np.ndarray) -> str:
    return f"|{''.join(str(int(b)) for b in bits_row)}⟩"


# ----------------------------------------------------------------------
# I/O helpers
# ----------------------------------------------------------------------

def ensure_dir(path: str) -> None:
    if path:
        d = path if os.path.isdir(path) else os.path.dirname(path)
        if d and not os.path.exists(d):
            os.makedirs(d, exist_ok=True)


# ----------------------------------------------------------------------
# Bitstrings & supports
# ----------------------------------------------------------------------

_BITS_CACHE_GLOBAL: dict = {}


def all_bitstrings(n: int) -> np.ndarray:
    """Return (2**n, n) int array of all bit strings in lexicographic order.

    Identical to the sslp_cpu version, just cached for repeated calls in the
    same process.  Position 0 (column 0) is the MSB of the integer index.
    """
    arr = _BITS_CACHE_GLOBAL.get(n)
    if arr is None:
        arr = np.array(list(product([0, 1], repeat=n)), dtype=int)
        _BITS_CACHE_GLOBAL[n] = arr
    return arr


def build_supports(n: int, a: List[int], m: int, s: int) -> Tuple[np.ndarray, np.ndarray]:
    bits = all_bitstrings(n)
    avec = np.array(a, dtype=int) % m
    sums = (bits @ avec) % m
    S_idx = np.where(sums == (s % m))[0]
    return bits, S_idx


def build_supports_multi(
    n: int, a: List[int], m: int, s_list: List[int]
) -> Tuple[np.ndarray, List[np.ndarray]]:
    """Return (bits, [S0_idx, S1_idx, ..., S_{K-1}_idx])."""
    bits = all_bitstrings(n)
    avec = np.array(a, dtype=int) % m
    sums = (bits @ avec) % m
    S_list = [np.where(sums == (s % m))[0] for s in s_list]
    return bits, S_list


# ----------------------------------------------------------------------
# Vectorized Hamming distance
# ----------------------------------------------------------------------

def min_hamming_distance_union(n: int, S_list: List[np.ndarray]) -> int:
    """Minimum Hamming distance between any two distinct bitstrings in the
    union of the support index sets.

    Same return value as the sslp_cpu version; vectorized for speed.
    """
    idxs: List[int] = []
    for S in S_list:
        idxs.extend(S.tolist())
    if len(idxs) < 2:
        return 0

    bits = all_bitstrings(n)
    sub = bits[idxs]  # (M, n)
    M = sub.shape[0]
    # Pairwise XOR Hamming distance via broadcasting; (M, M) int matrix.
    # Memory: M^2.  For M <= a few thousand this is tiny.
    diff = sub[:, None, :] != sub[None, :, :]
    hd = diff.sum(axis=-1)  # (M, M)
    # Mask diagonal to a large value so it doesn't get picked as min.
    np.fill_diagonal(hd, n + 1)
    md = int(hd.min())
    return md if md <= n else 0


# ----------------------------------------------------------------------
# Enumeration of candidate angle and residue vectors
# ----------------------------------------------------------------------

def iterate_all_monotone_a(n: int, m: int):
    """Yield all length-n monotone-nondecreasing tuples a_i in {1,..,m-1}.

    Identical iteration order to sslp_cpu/sslp_utils.iterate_all_monotone_a.
    """
    for comb in combinations_with_replacement(range(1, m), n):
        yield list(comb)


def iterate_all_increasing_s(m: int, K: int, require_coprime_sm: bool = True):
    """Yield tuples (s1, ..., s_{K-1}) with 1 <= s1 < ... < s_{K-1} <= m-1.

    Identical to sslp_cpu version.
    """
    cand = range(1, m)
    if require_coprime_sm:
        cand = [s for s in cand if np.gcd(s, m) == 1]
    for tup in combinations(cand, K - 1):
        yield list(tup)


def s_valid_against_a(a: List[int], m: int, s: int) -> bool:
    """Return True iff s differs from every +/- a_i mod m."""
    am = [x % m for x in a]
    return all((s - x) % m != 0 and (s + x) % m != 0 for x in am)


__all__ = [
    "HAVE_GMPY2",
    "fraction_str",
    "sqrt_fraction_str",
    "bits_to_ket",
    "ensure_dir",
    "all_bitstrings",
    "build_supports",
    "build_supports_multi",
    "min_hamming_distance_union",
    "iterate_all_monotone_a",
    "iterate_all_increasing_s",
    "s_valid_against_a",
]
