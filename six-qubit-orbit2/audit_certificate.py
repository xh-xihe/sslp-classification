#!/usr/bin/env python3
"""Independent exact checks of the packaged data and TeX characteristic table.
A fixed finite certificate audit, not a search or a formal Lean proof.
"""
from pathlib import Path
import importlib.util
import json
import sys
sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('orbit2_exact', ROOT / 'orbit2_exact_certificate.py')
v = importlib.util.module_from_spec(spec)
spec.loader.exec_module(v)


def polynomial_product(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return out


def from_factors(factors):
    out = [1]
    for factor, multiplicity in factors:
        for _ in range(multiplicity):
            out = polynomial_product(out, factor)
    return out


def charpoly(A):
    # Faddeev-LeVerrier: exact integer matrix multiplication and exact division.
    n = len(A)
    B = [[int(i == j) for j in range(n)] for i in range(n)]
    coefficients = [1]
    for k in range(1, n+1):
        AB = [[sum(A[i][l]*B[l][j] for l in range(n)) for j in range(n)] for i in range(n)]
        trace = sum(AB[i][i] for i in range(n))
        assert trace % k == 0
        c = -trace // k
        coefficients.append(c)
        B = [[AB[i][j] + c*(i == j) for j in range(n)] for i in range(n)]
    return coefficients


TABLE = {
    (0, 0, 24): [([1,-424],1),([1,-192],4),([1,-24],11),([1,-16],2),([1,-48,192],3)],
    (1, 0, 3): [([1,-384],1),([1,-48],2)],
    (2, 2, 3): [([1,-52],1),([1,-460,47872],1)],
    (3, 2, 4): [([1,-50],1),([1,-46],1),([1,-248,10716],1)],
    (2, 0, 8): [([1,-32],1),([1,-24],1),([1,-408,9856],1),([1,-352,9216],2)],
    (3, 0, 12): [([1,-136],1),([1,-48],1),([1,-352,9216],3),([1,-64,720],2)],
    (4, 2, 4): [([1,-56],1),([1,-44],1),([1,-380,23936],1)],
}


def main():
    data = json.loads((ROOT / 'orbit2_certificate_blocks.json').read_text())
    M = v.build_integer_certificate()
    assert data['pauli_order'] == [v.label_string(p) for p in v.T_LABELS]
    assert data['monomials'] == [list(m) for m in v.MONOMIALS]
    zeros = {i for i,(a,b) in enumerate(v.MONOMIALS) if not v.IS_B[a] and not v.IS_B[b]}
    assert set(data['zero_monomials']) == zeros
    seen = set()
    reconstructed = {}
    for block in data['blocks']:
        indices = block['monomial_indices']
        assert len(set(indices)) == len(indices)
        assert not seen.intersection(indices)
        seen.update(indices)
        A = block['matrix']
        for i,r in enumerate(indices):
            for j,c in enumerate(indices):
                assert A[i][j] == M.get((r,c),0)
                if A[i][j]:
                    reconstructed[r,c] = A[i][j]
        shifted = [[x-4*(i==j) for j,x in enumerate(row)] for i,row in enumerate(A)]
        assert block['ldlt_pivots_of_matrix_minus_4I'] == [str(p) for p in v.exact_ldlt_positive(shifted)]
        label = tuple('IXYZ'.index(a) for a in block['character'])
        signature = (v.weight(label), v.transverse_count(label), len(indices))
        assert charpoly(A) == from_factors(TABLE[signature]), block['character']
    assert seen == set(range(528))-zeros
    assert reconstructed == M
    print('PASS: supplied JSON equals independently regenerated integer matrix and rational pivots.')
    print('PASS: all 111 characteristic polynomials equal the seven TeX table formulas.')
    print('PASS: all 528 monomials partition into 36 zero and 492 positive coordinates.')


if __name__ == '__main__':
    main()
