"""Sanity-check the lift+distance-3 pipeline against the paper's known
distance-3 seeds from `Numerics/generate_lift_codewords.py`:

  * Steane [[7,1,3]]
  * BD16 family (10 seeds at n=7, m=8)
  * BD22 family (n=7, m=11)
  * BD32 family (n=7, m=16)
  * C10 cyclic ((6,2,3)) seed (n=6, m=5)

Each seed is run through `dyadic_lift.lift_check_chain` with max_rungs=4 and
distance >= 3 is verified at every rung.  Expected: ALL pass at ALL rungs.
If they do, the pipeline is verified end-to-end on real distance-3 codes.
"""
from __future__ import annotations

import os
import sys

# Make Numerics/ importable so we can reuse the built-in seed definitions.
_HERE = os.path.dirname(os.path.abspath(__file__))
_NUMERICS = os.path.normpath(os.path.join(_HERE, "..", "..", "Numerics"))
if _NUMERICS not in sys.path:
    sys.path.insert(0, _NUMERICS)

import numpy as np

from dyadic_lift import check_distance_3, lift_once_dense


def _seed_to_dense(seed, n: int):
    """Convert a generate_lift_codewords.Seed (dict-keyed sparse) into a dense
    complex128 state of length 2^n."""
    d = 1 << n
    zero = np.zeros(d, dtype=np.complex128)
    one = np.zeros(d, dtype=np.complex128)
    for bitstr, coeff in seed.zero.items():
        zero[int(bitstr, 2)] = complex(coeff)
    for bitstr, coeff in seed.one.items():
        one[int(bitstr, 2)] = complex(coeff)
    # Normalize (the seeds in generate_lift_codewords are already normalized;
    # do it here in case of accumulated FP drift).
    nz = np.vdot(zero, zero).real
    no = np.vdot(one, one).real
    if nz > 0:
        zero /= np.sqrt(nz)
    if no > 0:
        one /= np.sqrt(no)
    return zero, one


def verify_seed(name: str, seed, b1_for_lift: int, max_rungs: int = 4, tol: float = 1e-8):
    n = len(seed.a)
    m = int(seed.m)
    a = tuple(int(x) for x in seed.a)
    b_list = (0, int(b1_for_lift))   # paper convention for sd lift: b_1 = m - 1
    zero, one = _seed_to_dense(seed, n)

    # Rung 0
    ok0, info0 = check_distance_3(zero, one, n, tol=tol)
    print(f"  rung 0  n={n:2d}  m={m:3d}  passed={ok0}  worst_viol={info0['worst_violation']:.2e}")
    if not ok0:
        print(f"    -> reason: {info0.get('reason', '?')}, pauli={info0.get('worst_pauli')}")
        return False

    all_pass = True
    for r in range(1, max_rungs + 1):
        n, m, a, zero, one, b_list = lift_once_dense(n, m, a, zero, one, b_list)
        ok, info = check_distance_3(zero, one, n, tol=tol)
        print(
            f"  rung {r}  n={n:2d}  m={m:3d}  passed={ok}  worst_viol={info['worst_violation']:.2e}"
        )
        if not ok:
            all_pass = False
            print(f"    -> reason: {info.get('reason', '?')}, pauli={info.get('worst_pauli')}")
            break
    return all_pass


def main() -> int:
    # Import paper's built-in seeds from generate_lift_codewords.
    from generate_lift_codewords import (
        seed_steane, bd16_seeds, seed_bd22, seed_bd32, seed_c10,
    )

    print("=" * 72)
    print("Verifying lift+distance-3 pipeline on paper's known distance-3 seeds")
    print("=" * 72)

    all_seeds_pass = True
    seeds = []

    s = seed_steane()
    seeds.append(("Steane", s, s.m - 1))

    for i, s in enumerate(bd16_seeds(), start=1):
        seeds.append((f"BD16-{i:02d}", s, s.m - 1))

    s = seed_bd22()
    seeds.append(("BD22 (theta=0)", s, s.m - 1))

    s = seed_bd32()
    seeds.append(("BD32 (theta=0)", s, s.m - 1))

    s = seed_c10()
    seeds.append(("C10", s, s.m - 1))

    print(f"Total seeds to verify: {len(seeds)}", flush=True)
    print()

    for name, seed, b1 in seeds:
        print(f"--- {name}  (n={len(seed.a)}, m={seed.m}, b_1={b1}) ---")
        ok = verify_seed(name, seed, b1, max_rungs=4)
        status = "OK" if ok else "FAIL"
        print(f"  RESULT: {status}\n")
        if not ok:
            all_seeds_pass = False

    print("=" * 72)
    if all_seeds_pass:
        print("[PASS] Every paper seed retains distance >= 3 through 4 Bell lifts.")
        print("       The lift + distance-3 check pipeline is verified end-to-end.")
        return 0
    else:
        print("[FAIL] At least one paper seed failed.  Investigate the pipeline.")
        return 1


if __name__ == "__main__":
    sys.exit(main())
