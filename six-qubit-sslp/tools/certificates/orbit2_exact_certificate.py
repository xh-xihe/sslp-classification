#!/usr/bin/env python3
"""Exact global Orbit-2 common-J rigidity certificate.

This verifier uses only the Python standard library. All coefficient arithmetic
is integer arithmetic; positive definiteness is verified by rational LDL^T.
No numerical optimization, floating-point eigenvalues, or random tests are used.

It constructs M from the polynomial identity in orbit2_enumerator_section.tex
(also included in orbit2_enumerator_section_preview.tex) and
checks:
  (i) M has integer entries and vanishes on all T1*T1 monomials;
 (ii) M is block diagonal in Pauli-conjugation characters;
(iii) every remaining block satisfies M_block - 4 I > 0, exactly.

Run: python3 orbit2_exact_certificate.py
Optional: --json regenerated_blocks.json to export every exact integer block.
"""
from __future__ import annotations
import argparse
from collections import Counter, defaultdict
from fractions import Fraction
from hashlib import sha256
from itertools import combinations, product
import json
import time

# P_a P_b = i**PHASE[a][b] P_MULT[a][b], with I,X,Y,Z = 0,1,2,3.
P_MULT = ((0,1,2,3), (1,0,3,2), (2,3,0,1), (3,2,1,0))
PHASE = ((0,0,0,0), (0,0,1,3), (0,3,0,1), (0,1,3,0))
LABELS = list(product(range(4), repeat=4))
LABEL_INDEX = {p:i for i,p in enumerate(LABELS)}

def weight(p):
    return sum(a != 0 for a in p)

def transverse_count(p):
    return sum(a in (1,2) for a in p)

def label_string(p):
    return ''.join('IXYZ'[a] for a in p)

MUL = [[0]*256 for _ in range(256)]
EXP = [[0]*256 for _ in range(256)]
for a,p in enumerate(LABELS):
    for b,q in enumerate(LABELS):
        MUL[a][b] = LABEL_INDEX[tuple(P_MULT[x][y] for x,y in zip(p,q))]
        EXP[a][b] = sum(PHASE[x][y] for x,y in zip(p,q)) % 4


def trace_phase(indices):
    """Return phase exponent of normalized Pauli trace, or None if zero."""
    p = 0
    e = 0
    for q in indices:
        e = (e + EXP[p][q]) % 4
        p = MUL[p][q]
    return e if p == 0 else None


def real_sign(e):
    """An exact real phase, rejecting an unexpected imaginary coefficient."""
    assert e is not None and e % 2 == 0, ('nonreal phase', e)
    return 1 if e % 4 == 0 else -1

T_LABELS = [p for p in LABELS if transverse_count(p)==1 and weight(p) in (1,3)]
T_IDS = [LABEL_INDEX[p] for p in T_LABELS]
T_LOCAL = {p:i for i,p in enumerate(T_IDS)}
IS_B = [weight(p)==3 for p in T_LABELS]
MONOMIALS = list(combinations(range(32),2)) + [(i,i) for i in range(32)]
MONOMIALS.sort()
MONOMIAL_INDEX = {m:i for i,m in enumerate(MONOMIALS)}
assert len(T_LABELS)==32 and len(MONOMIALS)==528


def mon(a,b):
    return MONOMIAL_INDEX[(min(a,b),max(a,b))]


CTERMS = defaultdict(list)
for a,p in enumerate(T_IDS):
    for b,q in enumerate(T_IDS):
        CTERMS[MUL[p][q]].append((a,b,EXP[p][q]))

V_IDS = [i for i,p in enumerate(LABELS) if transverse_count(p)==2 and weight(p)==3]
assert len(V_IDS)==48

# Each matrix D below represents sum D[r,c] conjugate(z_r) z_c.

def add_entry(D,r,c,v):
    if v:
        D[(r,c)] += v


def coeff_product(left,right):
    D = defaultdict(int)
    for a,b,e1 in left:
        for c,d,e2 in right:
            add_entry(D,mon(b,d),mon(a,c),real_sign((e1+e2)%4))
    return D


def add_scaled(D,E,scale):
    for (r,c),v in E.items():
        add_entry(D,r,c,scale*v)


def add_symmetrized(D,E,scale):
    """Add scale*(E+E^T), in exact integer arithmetic."""
    for (r,c),v in E.items():
        add_entry(D,r,c,scale*v)
        add_entry(D,c,r,scale*v)


def projection_B_polynomial():
    """Raw Re tau(B^dagger (T T^dagger T - 2 N T)); symmetrize later."""
    G = defaultdict(int)
    for p,pp in enumerate(T_IDS):
        if not IS_B[p]:
            continue
        for a,pa in enumerate(T_IDS):
            for b,pb in enumerate(T_IDS):
                pc = MUL[MUL[pp][pa]][pb]
                if pc not in T_LOCAL:
                    continue
                c = T_LOCAL[pc]
                v = real_sign(trace_phase((pp,pa,pb,pc)))
                add_entry(G,mon(p,b),mon(a,c),v)
        for a in range(32):
            add_entry(G,mon(p,a),mon(p,a),-2)
    return G


J_WEIGHTS = {
    # These are 12 times the scalar multipliers in the proof.
    'XY3_Z': 5,
    'Z3_trans': 10,
    'XY3_trans': 7,
    'XY1_trans': 18,
    'Z1_trans': -18,
}


def common_J_polynomials():
    """Expand the defining six-Pauli traces literally, not by a fitted formula."""
    out = {name:defaultdict(int) for name in J_WEIGHTS}
    for site in range(4):
        for ax in (1,2,3):
            sl = tuple(ax if j==site else 0 for j in range(4))
            si = LABEL_INDEX[sl]
            for p,pp in enumerate(T_IDS):
                pl = T_LABELS[p]
                role = ('I' if pl[site]==0 else 'Z' if pl[site]==3
                        else 'same' if pl[site]==ax else 'trans')
                name = ('Z' if ax==3 else 'XY') + str(weight(pl)) + '_' + role
                if name not in out:
                    continue
                G = out[name]
                for a,pa in enumerate(T_IDS):
                    for b,pb in enumerate(T_IDS):
                        pc = MUL[MUL[pp][pa]][pb]
                        if pc not in T_LOCAL:
                            continue
                        c = T_LOCAL[pc]
                        e1 = trace_phase((pp,si,pa,pb,si,pc))
                        e2 = trace_phase((pp,si,pa,si,pb,pc))
                        v = real_sign(e1) - real_sign(e2)
                        add_entry(G,mon(p,b),mon(a,c),v)
                # -4 c_sigma tau((sigma t_p P_p)^dagger T).
                pc = MUL[pp][si]
                if pc in T_LOCAL:
                    c = T_LOCAL[pc]
                    e2 = trace_phase((pp,si,pc))
                    assert e2 is not None
                    for a,b,e1 in CTERMS[si]:
                        add_entry(G,mon(p,b),mon(a,c),-4*real_sign((e1+e2)%4))
    return out


def forbidden_class(p):
    w, f = weight(p), transverse_count(p)
    if f==0 and w==2:
        return 'ZZ'
    if f==0 and w==3:
        return 'ZZZ'
    if f==2 and w==4:
        return 'TTZZ'
    return None


def forbidden_polynomial(category,subtype):
    D = defaultdict(int)
    for r,terms in CTERMS.items():
        if forbidden_class(LABELS[r]) != category:
            continue
        if subtype=='13':
            sub = [(a,b,e) for a,b,e in terms if IS_B[a] != IS_B[b]]
        elif subtype=='33':
            sub = [(a,b,e) for a,b,e in terms if IS_B[a] and IS_B[b]]
        else:
            raise ValueError(subtype)
        add_scaled(D,coeff_product(terms,sub),1)
    assert all(v==D.get((c,r),0) for (r,c),v in D.items())
    return D


def build_integer_certificate():
    """Construct 24H, then divide exactly by two to obtain M=12H."""
    twice_M = defaultdict(int)
    for r in V_IDS:
        add_scaled(twice_M,coeff_product(CTERMS[r],CTERMS[r]),-24)
    for name,G in common_J_polynomials().items():
        add_symmetrized(twice_M,G,J_WEIGHTS[name])
    add_symmetrized(twice_M,projection_B_polynomial(),6)
    for category,subtype,w in [('TTZZ','13',34),('TTZZ','33',38),
                               ('ZZZ','13',50),('ZZ','33',4)]:
        add_scaled(twice_M,forbidden_polynomial(category,subtype),2*w)
    assert all(v%2==0 for v in twice_M.values())
    M = {(r,c):v//2 for (r,c),v in twice_M.items() if v}
    assert all(v==M.get((c,r),0) for (r,c),v in M.items())
    return M


def exact_ldlt_positive(A):
    """Exact SPD check by positive rational Schur-complement pivots."""
    n = len(A)
    Q = [[Fraction(x) for x in row] for row in A]
    pivots = []
    for k in range(n):
        pivot = Q[k][k]
        assert pivot > 0, ('nonpositive exact LDL pivot',k,pivot)
        pivots.append(pivot)
        for i in range(k+1,n):
            for j in range(i,n):
                v = Q[i][j] - Q[i][k]*Q[k][j]/pivot
                Q[i][j] = Q[j][i] = v
    return pivots


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--json',help='Export all exact blocks and rational LDL pivots')
    args = parser.parse_args()
    start = time.monotonic()
    M = build_integer_certificate()
    aa = {i for i,(a,b) in enumerate(MONOMIALS) if not IS_B[a] and not IS_B[b]}
    assert len(aa)==36
    assert all(r not in aa and c not in aa for r,c in M)
    chars = [MUL[T_IDS[a]][T_IDS[b]] for a,b in MONOMIALS]
    assert all(chars[r]==chars[c] for r,c in M)
    groups = defaultdict(list)
    for i,ch in enumerate(chars):
        if i not in aa:
            groups[ch].append(i)
    assert len(groups)==111 and sum(map(len,groups.values()))==492
    histogram = Counter()
    exports = []
    for ch,indices in sorted(groups.items()):
        block = [[M.get((r,c),0) for c in indices] for r in indices]
        shifted = [[x-4*(i==j) for j,x in enumerate(row)] for i,row in enumerate(block)]
        pivots = exact_ldlt_positive(shifted)
        signature=(weight(LABELS[ch]),transverse_count(LABELS[ch]),len(indices))
        histogram[signature] += 1
        exports.append({'character':label_string(LABELS[ch]),'monomial_indices':indices,
                        'matrix':block,'ldlt_pivots_of_matrix_minus_4I':[str(p) for p in pivots]})
    payload=json.dumps(sorted((r,c,v) for (r,c),v in M.items()),separators=(',',':'))
    digest=sha256(payload.encode()).hexdigest()
    print('EXACT CERTIFICATE VERIFIED')
    print('Arithmetic: integer polynomial coefficients and Fraction LDL^T pivots.')
    print('T basis: 8 weight-one and 24 weight-three complex coefficients.')
    print('Holomorphic quadratic monomials: 528.')
    print('Exact zero rows/columns (T1*T1): 36.')
    print('Positive blocks: 111, total dimension 492.')
    print('Every nonzero block satisfies M_block - 4I > 0, exactly.')
    print('Block signatures (Pauli weight, transverse count, size):')
    for sig,count in sorted(histogram.items()):
        print(' ',sig,'multiplicity',count)
    print('Nonzero integer matrix entries:',len(M))
    print('SHA256 of sparse M:',digest)
    print('Conclusion: on the stated constraints, -sum(c_V^2) = z^* M z / 12 >= 0.')
    print('Therefore all c_V vanish, and the positive blocks also force T3=0.')
    print('Elapsed seconds (not part of proof):',round(time.monotonic()-start,3))
    if args.json:
        data={'description':'Exact Orbit-2 global common-J rigidity certificate',
              'pauli_order':[label_string(p) for p in T_LABELS],
              'monomials':MONOMIALS,'zero_monomials':sorted(aa),
              'sparse_matrix_sha256':digest,'blocks':exports}
        with open(args.json,'w',encoding='utf-8') as f:
            json.dump(data,f,indent=2)
        print('Exported exact blocks:',args.json)

if __name__=='__main__':
    main()
