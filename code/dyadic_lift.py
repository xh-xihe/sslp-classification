# sslp_acc/dyadic_lift.py
# Dyadic Bell lift + distance-3 check.
#
# Given an SS-LP K=2 code with (n, m, a, b_list = (b_0, b_1)) and dense
# logical states |0_L>, |1_L>, this module applies the Bell lift recursively
# and verifies that each lifted code retains distance >= 3 in the
# Knill-Laflamme detection sense (every Pauli of weight <= 2 compresses to
# a scalar on the code subspace).
#
# Lift convention (matches sslp_cpu/Numerics/generate_lift_codewords.py and
# the paper's Section 3.1 generalized to arbitrary b_1):
#   m' = 2m,
#   a' = (a_1, ..., a_n, m, m),
#   For x in supp(|k_L>): A_a(x) mod m == b_k; high bit h_k = ((A_a(x) mod 2m)
#                          - b_k) / m in {0, 1}.
#   Parity p = h_k XOR k.  Append the Bell flag |Phi_p> where
#       |Phi_0> = (|00> + |11>) / sqrt(2),
#       |Phi_1> = (|01> + |10>) / sqrt(2).
#   New residue: b'_k = b_k + k*m  (so b'_0 = b_0, b'_1 = b_1 + m).
#
# Conventions for bit indexing: position 0 = column 0 of all_bitstrings =
# MSB of the integer index.  When we append 2 new qubits to the right, the
# integer index transforms as `new_x = (old_x << 2) | tag` where tag is
# the 2-bit integer encoding the Bell-flag basis element.

from __future__ import annotations

from itertools import combinations, product
from typing import Any, Dict, List, Optional, Tuple

import numpy as np

from sslp_utils import build_supports_multi


PAULI_LABELS = ("X", "Y", "Z")


# ----------------------------------------------------------------------
# Pauli action on a dense state vector (size 2^n complex128)
# ----------------------------------------------------------------------

def _popcount_arr(v: np.ndarray) -> np.ndarray:
    """Vectorized popcount for int64 arrays.  Uses numpy 2.0+ bitwise_count
    if available, else SWAR."""
    bc = getattr(np, "bitwise_count", None)
    if bc is not None:
        return bc(v)
    v = v - ((v >> 1) & np.int64(0x5555555555555555))
    v = (v & np.int64(0x3333333333333333)) + ((v >> 2) & np.int64(0x3333333333333333))
    v = (v + (v >> 4)) & np.int64(0x0F0F0F0F0F0F0F0F)
    return (v * np.int64(0x0101010101010101)) >> 56


def _enumerate_paulis(n: int, max_weight: int):
    """Yield Pauli strings of weight <= max_weight as dicts {pos: label}.
    pos is 0..n-1 with 0 = MSB of the integer index."""
    yield {}
    for w in range(1, max_weight + 1):
        for positions in combinations(range(n), w):
            for labels in product(PAULI_LABELS, repeat=w):
                yield dict(zip(positions, labels))


def _apply_pauli_dense(state: np.ndarray, ops: Dict[int, str], n: int) -> np.ndarray:
    """Apply Pauli string `ops` to dense state vector of length 2^n.

    `pos` keys in ops are 0-indexed with pos 0 = column 0 of all_bitstrings
    = MSB of the integer index.  Returns a fresh array (state is unchanged).
    """
    if not ops:
        return state
    d = 1 << n
    flip_mask = 0
    sign_mask = 0
    y_count = 0
    for pos, op in ops.items():
        bit = 1 << (n - 1 - pos)
        if op == "X":
            flip_mask |= bit
        elif op == "Y":
            flip_mask |= bit
            sign_mask |= bit
            y_count += 1
        elif op == "Z":
            sign_mask |= bit
        else:
            raise ValueError(f"bad Pauli label {op!r}")
    arange = np.arange(d, dtype=np.int64)
    input_idx = arange ^ np.int64(flip_mask)
    parity = (_popcount_arr(input_idx & np.int64(sign_mask)) & 1).astype(np.int8)
    sign_pm = np.where(parity == 0, 1.0, -1.0)
    if y_count % 4 == 0:
        i_factor = 1.0 + 0.0j
    elif y_count % 4 == 1:
        i_factor = 0.0 + 1.0j
    elif y_count % 4 == 2:
        i_factor = -1.0 + 0.0j
    else:
        i_factor = 0.0 - 1.0j
    factor = sign_pm.astype(np.complex128) * i_factor
    # (E|psi>)[x] = factor(x XOR flip_mask) * psi[x XOR flip_mask]
    return factor * state[input_idx]


# ----------------------------------------------------------------------
# Distance-3 check (weight-<=2 KL)
# ----------------------------------------------------------------------

def check_distance_at_least(
    zero: np.ndarray, one: np.ndarray, n: int, *,
    max_weight: int = 2,
    tol: float = 1e-8,
    full_scan: bool = False,
) -> Tuple[bool, Dict[str, Any]]:
    """Check KL conditions for every Pauli string of weight <= `max_weight`.

    Returns (passed, info).  max_weight=1 -> distance >= 2 check; max_weight=2
    -> distance >= 3 check; etc.

    If `full_scan` is False (default), the scan early-exits at the first Pauli
    whose violation exceeds `tol`, and `info['worst_violation']` is that
    first-encountered violation (cheap; pass/fail unaffected).  If `full_scan`
    is True, every weight-<=`max_weight` Pauli is scanned and
    `info['worst_violation']` is the TRUE global maximum violation (needed for
    accurate magnitude reporting on failing codes).  The pass/fail verdict is
    identical either way.
    """
    info: Dict[str, Any] = {}
    nz = float(np.vdot(zero, zero).real)
    no = float(np.vdot(one, one).real)
    iz = complex(np.vdot(zero, one))
    info["norm_zero"] = nz
    info["norm_one"] = no
    info["inner_zero_one"] = iz
    if (abs(nz - 1.0) > tol or abs(no - 1.0) > tol or abs(iz) > tol):
        info["reason"] = "norm/orth fail"
        info["worst_violation"] = max(abs(nz - 1.0), abs(no - 1.0), abs(iz))
        return False, info

    worst = 0.0
    worst_pauli: Optional[Dict[int, str]] = None
    worst_mat = None
    failed = False
    for ops in _enumerate_paulis(n, max_weight=max_weight):
        if ops:
            z_image = _apply_pauli_dense(zero, ops, n)
            o_image = _apply_pauli_dense(one, ops, n)
        else:
            z_image = zero
            o_image = one
        m00 = complex(np.vdot(zero, z_image))
        m01 = complex(np.vdot(zero, o_image))
        m10 = complex(np.vdot(one, z_image))
        m11 = complex(np.vdot(one, o_image))
        v = max(abs(m01), abs(m10), abs(m00 - m11))
        if v > worst:
            worst = v
            worst_pauli = ops
            worst_mat = (m00, m01, m10, m11)
        if v > tol:
            failed = True
            if not full_scan:
                info["reason"] = "kl_fail"
                info["worst_violation"] = v
                info["worst_pauli"] = ops
                info["worst_matrix"] = (m00, m01, m10, m11)
                return False, info
    info["worst_violation"] = worst
    info["worst_pauli"] = worst_pauli
    info["worst_matrix"] = worst_mat
    if failed:
        info["reason"] = "kl_fail"
        return False, info
    return True, info


def check_distance_3(
    zero: np.ndarray, one: np.ndarray, n: int, *, tol: float = 1e-8,
) -> Tuple[bool, Dict[str, Any]]:
    """Distance >= 3 check (KL on weight-<=2 Paulis).  Thin wrapper around
    `check_distance_at_least(max_weight=2)`."""
    return check_distance_at_least(zero, one, n, max_weight=2, tol=tol)


# ----------------------------------------------------------------------
# Generalized Bell lift (K=2, arbitrary b_1)
# ----------------------------------------------------------------------

def lift_once_dense(
    n: int, m: int, a: Tuple[int, ...],
    zero: np.ndarray, one: np.ndarray,
    b_list: Tuple[int, int],
) -> Tuple[int, int, Tuple[int, ...], np.ndarray, np.ndarray, Tuple[int, int]]:
    """Apply ONE Bell lift.  Returns (n', m', a', zero', one', b_list').

    Lift rule (paper's generalized two-state parity-tag lift with delta_k = k):
        new_x = (old_x << 2) | tag,  tag in {00, 11} for parity=0, {01, 10} for parity=1
        parity = h_k(x) XOR k
        h_k(x) = ((A_a(x) mod 2m) - b_k) / m
        new coefficient = old / sqrt(2)
    """
    new_m = 2 * m
    new_n = n + 2
    new_a = tuple(a) + (m, m)
    new_b = (b_list[0] + 0 * m, b_list[1] + 1 * m)

    d_old = 1 << n
    d_new = 1 << new_n

    # Precompute A_a(x) mod 2m for every old basis index x.
    avec = np.array(a, dtype=np.int64)
    # Build all old bitstrings as (d_old, n) int matrix.
    arange_old = np.arange(d_old, dtype=np.int64)
    # bits[x, i] = (x >> (n - 1 - i)) & 1, i.e. column i = MSB direction.
    cols = (n - 1 - np.arange(n))
    bits = ((arange_old[:, None] >> cols[None, :]) & 1).astype(np.int64)  # (d_old, n)
    A_x_mod_2m = (bits @ avec) % (2 * m)

    new_zero = np.zeros(d_new, dtype=np.complex128)
    new_one = np.zeros(d_new, dtype=np.complex128)

    inv_sqrt2 = 1.0 / np.sqrt(2.0)

    for k, codeword, out in [(0, zero, new_zero), (1, one, new_one)]:
        b_k = int(b_list[k])
        for x in range(d_old):
            coeff = codeword[x]
            if coeff == 0:
                continue
            r = int(A_x_mod_2m[x])
            if r == b_k:
                h = 0
            elif r == b_k + m:
                h = 1
            else:
                raise ValueError(
                    f"lift_once_dense: x={x:b} has A_a mod 2m = {r} but expected "
                    f"either b_k={b_k} or b_k+m={b_k + m} for sector k={k} "
                    f"(m={m}, a={a})"
                )
            parity = h ^ k
            if parity == 0:
                tags = (0b00, 0b11)
            else:
                tags = (0b01, 0b10)
            scaled = coeff * inv_sqrt2
            base = x << 2
            for tag in tags:
                out[base | tag] += scaled

    return new_n, new_m, new_a, new_zero, new_one, new_b


# ----------------------------------------------------------------------
# Seed state reconstruction from a sslp_acc hit dict
# ----------------------------------------------------------------------

def reconstruct_seed_state(hit: Dict[str, Any]) -> Tuple[
    int, int, Tuple[int, ...], np.ndarray, np.ndarray, Tuple[int, int]
]:
    """From a sslp_acc K=2 hit, build (n, m, a, zero_dense, one_dense, b_list).

    `zero_dense[idx]` is the (real, non-negative) amplitude at integer index idx.
    The reconstruction matches sslp_acc's build_states_from_probs with phase=0.
    """
    K = int(hit["K"])
    if K != 2:
        raise ValueError(f"reconstruct_seed_state requires K=2; got K={K}")
    n = int(hit["n"])
    m = int(hit["m"])
    a = tuple(int(x) for x in hit["a"])
    s_list = [int(x) for x in hit["s_list"]]
    b_list = (s_list[0], s_list[1])

    d = 1 << n

    if "support_W_0" in hit and "support_W_1" in hit:
        S_used = [
            np.asarray(hit["support_W_0"], dtype=np.int64),
            np.asarray(hit["support_W_1"], dtype=np.int64),
        ]
    else:
        _, S_used = build_supports_multi(n, list(a), m, s_list)

    zero = np.zeros(d, dtype=np.complex128)
    one = np.zeros(d, dtype=np.complex128)
    for j, out in enumerate([zero, one]):
        S = S_used[j]
        ps = hit["P_list"][j]
        if len(ps) != len(S):
            raise ValueError(
                f"reconstruct_seed_state: P_list[{j}] has {len(ps)} entries "
                f"but support has {len(S)} indices"
            )
        for idx, p in zip(S.tolist(), ps):
            out[int(idx)] = np.sqrt(max(float(p), 0.0))
    # Normalize (should already be normalized; do it for safety).
    nz = np.vdot(zero, zero).real
    no = np.vdot(one, one).real
    if nz > 0:
        zero /= np.sqrt(nz)
    if no > 0:
        one /= np.sqrt(no)
    return n, m, a, zero, one, b_list


# ----------------------------------------------------------------------
# Lift + distance chain
# ----------------------------------------------------------------------

def lift_check_chain(
    hit: Dict[str, Any],
    *,
    max_rungs: int = 4,
    tol: float = 1e-8,
    stop_at_first_fail: bool = False,
) -> Dict[str, Any]:
    """For one K=2 hit: check distance >= 3 at the seed, then apply Bell lifts
    up to max_rungs and check distance >= 3 at each rung.

    Parameters
    ----------
    stop_at_first_fail : if True, stop as soon as a rung fails (faster but
        less informative).  If False (default), always lift up to max_rungs
        and record each rung's verdict independently -- this captures the
        possibility that a failed seed becomes distance-3 after lifting,
        thanks to the carry-decomposition cancellations described in the
        paper's Definition 2.3 ("carry-dephased KL").

    Returns a structured dict with per-rung pass/fail info:
        seed_d3_pass:           bool   (== rungs[0]['passed'])
        consecutive_max_rung:   int    largest r s.t. rungs 0..r all pass; -1 otherwise
        any_pass_rungs:         list of rungs that pass individually
        rungs:                  list of per-rung dicts with worst_violation, passed
        error, fail_rung:       diagnostics
    """
    out: Dict[str, Any] = {
        "n": int(hit["n"]),
        "m": int(hit["m"]),
        "K": int(hit["K"]),
        "a": [int(x) for x in hit["a"]],
        "s_list": [int(x) for x in hit["s_list"]],
        "seed_d3_pass": None,
        "consecutive_max_rung": -1,
        "any_pass_rungs": [],
        "fail_rung": None,
        "rungs": [],
        "error": None,
    }
    try:
        n, m, a, zero, one, b_list = reconstruct_seed_state(hit)
    except Exception as e:
        out["error"] = f"reconstruct: {e}"
        return out

    # Seed (rung 0) check
    seed_ok, seed_info = check_distance_at_least(
        zero, one, n, max_weight=2, tol=tol,
    )
    out["seed_d3_pass"] = bool(seed_ok)
    out["rungs"].append({
        "rung": 0, "n": n, "m": m, "b_list": list(b_list),
        "passed": bool(seed_ok),
        "worst_violation": float(seed_info.get("worst_violation", 0.0)),
    })
    if seed_ok:
        out["any_pass_rungs"].append(0)
        out["consecutive_max_rung"] = 0
    elif stop_at_first_fail:
        out["fail_rung"] = 0
        return out

    consecutive_alive = bool(seed_ok)
    # Apply lifts and check
    for r in range(1, max_rungs + 1):
        try:
            n, m, a, zero, one, b_list = lift_once_dense(
                n, m, a, zero, one, b_list
            )
        except Exception as e:
            out["error"] = f"lift_at_rung_{r}: {e}"
            if out["fail_rung"] is None:
                out["fail_rung"] = r
            return out
        ok, info = check_distance_at_least(
            zero, one, n, max_weight=2, tol=tol,
        )
        out["rungs"].append({
            "rung": r, "n": n, "m": m, "b_list": list(b_list),
            "passed": bool(ok),
            "worst_violation": float(info.get("worst_violation", 0.0)),
        })
        if ok:
            out["any_pass_rungs"].append(r)
            if consecutive_alive:
                out["consecutive_max_rung"] = r
        else:
            consecutive_alive = False
            if out["fail_rung"] is None:
                out["fail_rung"] = r
            if stop_at_first_fail:
                return out

    return out


__all__ = [
    "lift_once_dense",
    "check_distance_at_least",
    "reconstruct_seed_state",
    "lift_check_chain",
]
