#!/usr/bin/env python3
"""Generate explicit dyadic Bell-lift codewords by recursion.

The script stores the seed codewords used in the accompanying note and can also
read a custom seed from JSON.  A codeword is represented sparsely as a map
    bitstring -> [real, imag].

Examples
--------
List built-in seeds:
    python generate_lift_codewords.py --list

Generate Steane rungs 0,1,2 as JSON files:
    python generate_lift_codewords.py --seed steane --rungs 0 1 2 --out-dir codewords

Generate all built-in seeds through the second lift:
    python generate_lift_codewords.py --all --rungs 0 1 2 --out-dir codewords

Print a LaTeX-like expansion of one rung:
    python generate_lift_codewords.py --seed c10 --rungs 2 --format text

Custom seed JSON format
-----------------------
{
  "name": "my_seed",
  "m": 8,
  "a": [1,1,1,2,2,4,4],
  "zero": {"0000000": [0.25, 0.0], ...},
  "one":  {"1111111": [0.25, 0.0], ...}
}
"""
from __future__ import annotations

import argparse
import json
import math
import cmath
from dataclasses import dataclass
from itertools import product
from pathlib import Path
from typing import Dict, Iterable, List, Mapping, MutableMapping, Tuple

ComplexDict = Dict[str, complex]


@dataclass(frozen=True)
class Seed:
    name: str
    m: int
    a: Tuple[int, ...]
    zero: ComplexDict
    one: ComplexDict
    description: str = ""


def cpair(z: complex) -> List[float]:
    """Complex number as a JSON-friendly [real, imag] pair."""
    r = 0.0 if abs(z.real) < 1e-15 else float(z.real)
    im = 0.0 if abs(z.imag) < 1e-15 else float(z.imag)
    return [r, im]


def from_pair(v: object) -> complex:
    if isinstance(v, (list, tuple)) and len(v) == 2:
        return complex(float(v[0]), float(v[1]))
    if isinstance(v, (int, float)):
        return complex(float(v), 0.0)
    raise TypeError(f"coefficient must be [real, imag], got {v!r}")


def add_term(d: MutableMapping[str, complex], s: str, c: complex) -> None:
    d[s] = d.get(s, 0.0j) + c
    if abs(d[s]) < 1e-15:
        del d[s]


def complement(s: str) -> str:
    return ''.join('1' if b == '0' else '0' for b in s)


def complement_codeword(zero: Mapping[str, complex]) -> ComplexDict:
    return {complement(s): c for s, c in zero.items()}


def lift_once(m: int, a: Iterable[int], zero: Mapping[str, complex], one: Mapping[str, complex]) -> Tuple[int, Tuple[int, ...], ComplexDict, ComplexDict]:
    """Apply one dyadic Bell lift.

    If a basis word s appears in logical sector k, its old subset-sum residue is
    b_k=0 for k=0 and b_k=m-1 for k=1.  The high bit h is defined by
        sum_j a_j s_j == b_k + h*m mod 2m.
    The appended Bell parity is h xor k.
    """
    a_tuple = tuple(int(x) for x in a)
    new_zero: ComplexDict = {}
    new_one: ComplexDict = {}

    for k, codeword, out in [(0, zero, new_zero), (1, one, new_one)]:
        b = 0 if k == 0 else m - 1
        for s, coeff in codeword.items():
            if len(s) != len(a_tuple):
                raise ValueError(f"word {s!r} has length {len(s)}, expected {len(a_tuple)}")
            A = sum(ai * (1 if bit == '1' else 0) for ai, bit in zip(a_tuple, s))
            if A % m != b:
                raise ValueError(
                    f"word {s} in logical {k} has subset sum {A}, residue {A % m}; expected {b} mod {m}"
                )
            r = A % (2 * m)
            h = (r - b) // m
            if h not in (0, 1) or b + h * m != r:
                raise ValueError(f"could not determine high bit for word {s}, sum {A}, residue {r}")
            parity = h ^ k
            tags = ("00", "11") if parity == 0 else ("01", "10")
            for tag in tags:
                add_term(out, s + tag, coeff / math.sqrt(2.0))

    return 2 * m, a_tuple + (m, m), new_zero, new_one


def lift_to_rung(seed: Seed, rung: int) -> Tuple[int, Tuple[int, ...], ComplexDict, ComplexDict]:
    if rung < 0:
        raise ValueError("rung must be nonnegative")
    m = seed.m
    a = seed.a
    zero = dict(seed.zero)
    one = dict(seed.one)
    for _ in range(rung):
        m, a, zero, one = lift_once(m, a, zero, one)
    return m, a, zero, one


def norm2(codeword: Mapping[str, complex]) -> float:
    return float(sum(abs(c) ** 2 for c in codeword.values()))


def inner(a: Mapping[str, complex], b: Mapping[str, complex]) -> complex:
    if len(a) > len(b):
        a, b = b, a
        return sum(b.get(s, 0.0j).conjugate() * c for s, c in a.items()).conjugate()
    return sum(c.conjugate() * b.get(s, 0.0j) for s, c in a.items())


def seed_steane() -> Seed:
    # Coordinates are ordered as 001,010,011,100,101,110,111.
    points = [(0, 0, 1), (0, 1, 0), (0, 1, 1), (1, 0, 0), (1, 0, 1), (1, 1, 0), (1, 1, 1)]
    zero: ComplexDict = {}
    for u in product([0, 1], repeat=3):
        word = ''.join(str((u[0]*p[0] + u[1]*p[1] + u[2]*p[2]) % 2) for p in points)
        zero[word] = 1 / math.sqrt(8.0)
    return Seed(
        name="steane",
        m=4,
        a=(1, 1, 1, 1, 1, 1, 1),
        zero=zero,
        one=complement_codeword(zero),
        description="Steane [[7,1,3]] simplex seed, BD8 convention",
    )


def make_seed(name: str, m: int, a: Iterable[int], terms: Iterable[Tuple[str, complex]], self_complementary: bool = True, one_terms: Iterable[Tuple[str, complex]] | None = None, description: str = "") -> Seed:
    zero: ComplexDict = {}
    for s, c in terms:
        add_term(zero, s, c)
    if self_complementary:
        one = complement_codeword(zero)
    else:
        if one_terms is None:
            raise ValueError("one_terms required for non-self-complementary seed")
        one = {}
        for s, c in one_terms:
            add_term(one, s, c)
    return Seed(name=name, m=m, a=tuple(a), zero=zero, one=one, description=description)


def bd16_seeds() -> List[Seed]:
    rt = math.sqrt
    i = 1j
    seeds: List[Seed] = []

    seeds.append(make_seed("bd16_01", 8, (1,2,2,2,2,3,3), [
        ("0000000", 1/4),
        ("0111100", rt(3)/4),
        ("1001110", rt(3)/4),
        ("1010101", rt(2)/4),
        ("1011001", rt(2)/4),
        ("1110010", 1/4),
        ("0100011", 2*i/4),
    ], description="BD16 seed 1"))

    T = ["1101110", "1110110", "1111010", "1111100"]
    terms = [
        ("0000000", 1/4),
        ("0011110", -rt(3)/4),
        ("0100101", i*rt(2)/4),
        ("0110001", -i*rt(2)/4),
        ("1000011", -i*rt(2)/4),
        ("1001001", i*rt(2)/4),
    ] + [(t, i/4) for t in T]
    seeds.append(make_seed("bd16_02", 8, (1,1,2,2,2,2,5), terms, description="BD16 seed 2"))

    seeds.append(make_seed("bd16_03", 8, (0,1,2,2,3,3,4), [
        ("0000000", 1/4),
        ("0010110", i*rt(2)/4),
        ("0100011", -i*rt(3)/4),
        ("0111100", -rt(2)/4),
        ("1001110", rt(2)/4),
        ("1011001", -rt(3)/4),
        ("1100101", rt(2)/4),
        ("1111010", i/4),
    ], description="BD16 seed 3"))

    seeds.append(make_seed("bd16_04", 8, (1,1,2,2,3,3,3), [
        ("0000000", 1/4),
        ("0001011", rt(2)/4),
        ("0010011", -rt(2)/4),
        ("0111100", i*rt(3)/4),
        ("1011001", i*rt(6)/8),
        ("1011010", -i*rt(6)/8),
        ("1100101", -i*rt(10)/8),
        ("1100110", -i*rt(10)/8),
    ], description="BD16 seed 4"))

    seeds.append(make_seed("bd16_05", 8, (1,1,2,2,2,3,4), [
        ("0000000", 1/4),
        ("0001101", -i/4),
        ("0010101", i/4),
        ("0011001", -i/4),
        ("0100011", -i/4),
        ("0101110", -1/4),
        ("0110110", 1/4),
        ("0111010", 1/4),
        ("1000011", -i/4),
        ("1001110", 1/4),
        ("1010110", 1/4),
        ("1011010", -1/4),
        ("1100101", -1/4),
        ("1101001", -1/4),
        ("1110001", -1/4),
        ("1111100", -i/4),
    ], description="BD16 seed 5"))

    seeds.append(make_seed("bd16_06", 8, (1,1,1,2,3,3,4), [
        ("0000000", 1/4),
        ("0001110", i*rt(2)/4),
        ("0110110", rt(2)/4),
        ("0111001", rt(3)/4),
        ("1000011", i*rt(10)/8),
        ("1000101", i*rt(10)/8),
        ("1111010", i*rt(6)/8),
        ("1111100", -i*rt(6)/8),
    ], description="BD16 seed 6"))

    seeds.append(make_seed("bd16_07", 8, (1,1,1,2,2,4,4), [
        ("0000000", 1/4),
        ("0000011", 1/4),
        ("0001101", 1/4),
        ("0001110", 1/4),
        ("0110101", i/4),
        ("0110110", i/4),
        ("0111001", -i/4),
        ("0111010", -i/4),
        ("1010101", -i/4),
        ("1010110", -i/4),
        ("1011001", -i/4),
        ("1011010", -i/4),
        ("1100101", -i/4),
        ("1100110", i/4),
        ("1101001", -i/4),
        ("1101010", i/4),
    ], description="BD16 seed 7 / worked example"))

    T3 = ["0010101", "0011001", "0100101", "0101001", "1000101", "1001001"]
    T6 = ["0011110", "0101110", "1001110"]
    terms = [("0000000", 1/4), ("0000011", 1/4)]
    terms += [(t, -i*rt(3)/8) for t in T3]
    terms += [(t, -rt(6)/8) for t in T6]
    terms += [("1110001", -rt(10)/8), ("1110110", i*rt(5)/8), ("1111010", i*rt(5)/8)]
    seeds.append(make_seed("bd16_08", 8, (1,1,1,2,2,3,5), terms, description="BD16 seed 8"))

    seeds.append(make_seed("bd16_09", 8, (1,1,1,1,3,4,4), [
        ("0000000", 1/4),
        ("0000011", 1/4),
        ("0001101", i/4),
        ("0001110", -i/4),
        ("0010101", i/4),
        ("0010110", -i/4),
        ("0100101", i/4),
        ("0100110", -i/4),
        ("1000101", i/4),
        ("1000110", -i/4),
        ("1111001", i*rt(3)/4),
        ("1111010", i*rt(3)/4),
    ], description="BD16 seed 9"))

    seeds.append(make_seed("bd16_10", 8, (1,1,1,1,3,3,5), [
        ("0000000", 1/4),
        ("0000011", -1/4),
        ("0000101", -1/4),
        ("0011110", 1/4),
        ("1100110", 1/4),
        ("0101110", 1/8),
        ("1010110", 1/8),
        ("0110110", 3/8),
        ("1001110", 3/8),
        ("1011001", rt(6)/8),
        ("1101001", rt(6)/8),
        ("0111001", -rt(6)/8),
        ("1110001", -rt(6)/8),
    ], description="BD16 seed 10"))

    return seeds


def seed_bd32(theta: float = 0.0) -> Seed:
    rt = math.sqrt
    i = 1j
    if theta < -1e-12 or theta > math.sqrt(1/8) + 1e-12:
        raise ValueError("bd32 theta must lie in [0, sqrt(1/8)]")
    terms = [
        ("0000000", 1/rt(32)),
        ("0001101", i*rt(2 + 32*theta*theta)/rt(32)),
        ("0010101", i*rt(6 - 32*theta*theta)/rt(32)),
        ("0100011", 2*i/rt(32)),
        ("0111100", rt(3)/rt(32)),
        ("1011010", rt(7)/rt(32)),
        ("1100110", rt(5)/rt(32)),
        ("1101001", rt(4 - 32*theta*theta)/rt(32)),
        ("1110001", theta),
    ]
    return make_seed("bd32", 16, (2,3,4,4,5,6,7), terms, description=f"BD32 family at theta={theta}")


def seed_bd22(theta: float = 0.0) -> Seed:
    rt = math.sqrt
    i = 1j
    if theta < -1e-12 or theta > math.sqrt(3/22) + 1e-12:
        raise ValueError("bd22 theta must lie in [0, sqrt(3/22)]")
    terms = [
        ("0000000", rt(1/22)),
        ("1011010", rt(2/22)),
        ("0111100", rt(3/22)),
        ("0100011", 2*i*rt(1/22)),
        ("0001101", i*theta),
        ("0010101", i*rt(3/22 - theta*theta)),
        ("1001110", (rt(5)/3)*rt(3/11 - theta*theta)),
        ("1101001", (2/3)*rt(3/11 - theta*theta)),
        ("1010110", (rt(5)/3)*rt(3/22 + theta*theta)),
        ("1110001", -(2/3)*rt(3/22 + theta*theta)),
    ]
    return make_seed("bd22", 11, (1,2,3,3,3,4,5), terms, description=f"repaired BD22 family at theta={theta}")


def seed_c10() -> Seed:
    rt = math.sqrt
    omega = cmath.exp(2j * math.pi / 3)
    zero_terms = [
        ("000000", rt(3)/rt(30)),
        ("000011", rt(3)/rt(30)),
        ("011110", rt(3)/rt(30)),
        ("101110", rt(3)*omega/rt(30)),
        ("110110", rt(3)*omega**2/rt(30)),
        ("111010", rt(3)/rt(30)),
        ("001101", rt(2)/rt(30)),
        ("010101", rt(2)/rt(30)),
        ("011001", rt(2)/rt(30)),
        ("100101", rt(2)/rt(30)),
        ("101001", rt(2)*omega**2/rt(30)),
        ("110001", rt(2)*omega/rt(30)),
    ]
    one_terms = [
        ("111111", rt(3)/rt(30)),
        ("111100", rt(3)/rt(30)),
        ("100001", -rt(3)/rt(30)),
        ("010001", -rt(3)*omega**2/rt(30)),
        ("001001", -rt(3)*omega/rt(30)),
        ("000101", -rt(3)/rt(30)),
        ("110010", -rt(2)/rt(30)),
        ("101010", -rt(2)/rt(30)),
        ("100110", -rt(2)/rt(30)),
        ("011010", -rt(2)/rt(30)),
        ("010110", -rt(2)*omega/rt(30)),
        ("001110", -rt(2)*omega**2/rt(30)),
    ]
    return make_seed("c10", 5, (1,1,1,1,2,3), zero_terms, self_complementary=False, one_terms=one_terms, description="cyclic C10 ((6,2,3)) seed")


def built_in_seeds(theta_bd22: float = 0.0, theta_bd32: float = 0.0) -> Dict[str, Seed]:
    seeds = {"steane": seed_steane(), "c10": seed_c10(), "bd22": seed_bd22(theta_bd22), "bd32": seed_bd32(theta_bd32)}
    for s in bd16_seeds():
        seeds[s.name] = s
    return seeds


def validate_codeword_pair(zero: Mapping[str, complex], one: Mapping[str, complex], tol: float = 1e-8) -> None:
    n0 = {len(s) for s in zero}
    n1 = {len(s) for s in one}
    if len(n0) != 1 or len(n1) != 1 or n0 != n1:
        raise ValueError("all codeword bitstrings must have the same length")
    if abs(norm2(zero) - 1.0) > tol:
        raise ValueError(f"logical zero is not normalized: norm^2={norm2(zero)}")
    if abs(norm2(one) - 1.0) > tol:
        raise ValueError(f"logical one is not normalized: norm^2={norm2(one)}")
    if abs(inner(zero, one)) > tol:
        raise ValueError(f"logical states are not orthogonal: inner={inner(zero, one)}")


def write_json(seed: Seed, rung: int, out_dir: Path) -> Path:
    m, a, zero, one = lift_to_rung(seed, rung)
    validate_codeword_pair(zero, one)
    n = len(a)
    payload = {
        "name": seed.name,
        "description": seed.description,
        "rung": rung,
        "n": n,
        "m": m,
        "a": list(a),
        "zero": {s: cpair(c) for s, c in sorted(zero.items())},
        "one": {s: cpair(c) for s, c in sorted(one.items())},
    }
    out_dir.mkdir(parents=True, exist_ok=True)
    path = out_dir / f"{seed.name}_r{rung}_n{n}_m{m}.json"
    with path.open("w", encoding="utf-8") as f:
        json.dump(payload, f, indent=2, sort_keys=True)
    return path


def coeff_to_text(z: complex, digits: int = 12) -> str:
    r, im = z.real, z.imag
    if abs(r) < 10**(-digits+2):
        r = 0.0
    if abs(im) < 10**(-digits+2):
        im = 0.0
    if im == 0.0:
        return f"{r:.{digits}g}"
    if r == 0.0:
        return f"{im:.{digits}g}j"
    sign = "+" if im >= 0 else "-"
    return f"{r:.{digits}g}{sign}{abs(im):.{digits}g}j"


def print_text(seed: Seed, rung: int) -> None:
    m, a, zero, one = lift_to_rung(seed, rung)
    validate_codeword_pair(zero, one)
    print(f"# {seed.name}, rung={rung}, n={len(a)}, m={m}, a={list(a)}")
    for label, cw in [("zero", zero), ("one", one)]:
        print(f"{label}:")
        for s, c in sorted(cw.items()):
            print(f"  {coeff_to_text(c):>18}  |{s}>")


def load_custom_seed(path: Path) -> Seed:
    with path.open("r", encoding="utf-8") as f:
        payload = json.load(f)
    try:
        name = str(payload.get("name", path.stem))
        m = int(payload["m"])
        a = tuple(int(x) for x in payload["a"])
        zero = {str(s): from_pair(v) for s, v in payload["zero"].items()}
        one = {str(s): from_pair(v) for s, v in payload["one"].items()}
    except KeyError as exc:
        raise ValueError(f"missing key in custom seed JSON: {exc}") from exc
    return Seed(name=name, m=m, a=a, zero=zero, one=one, description=f"custom seed from {path}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--list", action="store_true", help="list built-in seeds and exit")
    parser.add_argument("--seed", help="built-in seed name")
    parser.add_argument("--all", action="store_true", help="generate all built-in seeds")
    parser.add_argument("--custom-seed", type=Path, help="JSON file containing a custom seed")
    parser.add_argument("--rungs", type=int, nargs="+", default=[0, 1, 2], help="rungs to generate; default: 0 1 2")
    parser.add_argument("--out-dir", type=Path, default=Path("generated_codewords"), help="output directory for JSON files")
    parser.add_argument("--format", choices=["json", "text"], default="json", help="output format; text prints to stdout")
    parser.add_argument("--theta-bd22", type=float, default=0.0, help="theta for built-in bd22 family")
    parser.add_argument("--theta-bd32", type=float, default=0.0, help="theta for built-in bd32 family")
    args = parser.parse_args()

    seeds = built_in_seeds(theta_bd22=args.theta_bd22, theta_bd32=args.theta_bd32)

    if args.list:
        for key in sorted(seeds):
            s = seeds[key]
            print(f"{key:10s} n={len(s.a):2d} m={s.m:2d} a={list(s.a)}  {s.description}")
        return

    selected: List[Seed] = []
    if args.custom_seed is not None:
        selected.append(load_custom_seed(args.custom_seed))
    if args.all:
        selected.extend(seeds[k] for k in sorted(seeds))
    if args.seed:
        if args.seed not in seeds:
            raise SystemExit(f"unknown seed {args.seed!r}; use --list")
        selected.append(seeds[args.seed])
    if not selected:
        raise SystemExit("choose --seed NAME, --all, --custom-seed FILE, or --list")

    for seed in selected:
        for rung in args.rungs:
            if args.format == "json":
                path = write_json(seed, rung, args.out_dir)
                print(path)
            else:
                print_text(seed, rung)
                print()


if __name__ == "__main__":
    main()
