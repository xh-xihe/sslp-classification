"""Prepare untrusted exact primal/dual candidates for all orbit-31 supports.

This deliberately does not claim Lean acceptance. Numeric linear programming
only searches for small rational candidates; every candidate is rechecked
with integer/Fraction arithmetic here and still requires a Lean certificate.
No vertex-completeness theorem is assumed: rejected masks receive explicit
dual separators, including zero-right-hand-side forced-zero certificates.
"""
import argparse
from fractions import Fraction
from functools import reduce
from itertools import combinations, permutations
import json
from math import gcd, lcm
from pathlib import Path
import time

import numpy as np
from scipy.optimize import linprog

EVEN = [(0,0,0),(0,1,1),(1,0,1),(1,1,0)]
WORDS = [(0,0,0)+e for e in EVEN]+[
    tuple(0 if j==i else 1 for j in range(3))+tuple(1-x for x in e)
    for i in range(3) for e in EVEN]
MATRIX = [[1]*16]+[[x[j] for x in WORDS] for j in range(6)]
RHS = [Fraction(1)]+[Fraction(1,2)]*6
FULL = (1<<16)-1


def primitive(values):
    rationals = [Fraction(float(v)).limit_denominator(4096) for v in values]
    denominator = lcm(*(v.denominator for v in rationals))
    ints = [int(v*denominator) for v in rationals]
    divisor = reduce(gcd,(abs(v) for v in ints))
    if divisor:
        ints = [v//divisor for v in ints]
    return ints


def vertices():
    matrix = np.asarray(MATRIX,dtype=float)
    rhs = np.asarray(RHS,dtype=float)
    found = {}
    for basis in combinations(range(16),7):
        try:
            candidate = np.linalg.solve(matrix[:,basis],rhs)
        except np.linalg.LinAlgError:
            continue
        if not np.all(np.isfinite(candidate)) or min(candidate)<-1e-8:
            continue
        exact = [Fraction(float(v)).limit_denominator(4096) for v in candidate]
        if min(exact)<0:
            continue
        point = [Fraction(0)]*16
        for j,value in zip(basis,exact):
            point[j] = value
        if any(sum(a*x for a,x in zip(row,point))!=b for row,b in zip(MATRIX,RHS)):
            continue
        mask = sum(1<<j for j,x in enumerate(point) if x>0)
        if mask in found:
            assert found[mask]==point
        else:
            found[mask]=point
    assert len(found)==204
    assert sum(m.bit_count()==6 for m in found)==108
    assert sum(m.bit_count()==7 for m in found)==96
    return sorted(found.items())


def dual_data(y):
    coeffs = [sum(MATRIX[i][j]*y[i] for i in range(7)) for j in range(16)]
    b2 = 2*y[0]+sum(y[1:])
    return {'multipliers':y,'coefficients':coeffs,'rhs_twice':b2,
            'negative_mask':sum(1<<j for j,v in enumerate(coeffs) if v<0),
            'positive_mask':sum(1<<j for j,v in enumerate(coeffs) if v>0)}


def excludes(dual,mask):
    return ((dual['negative_mask']&mask)==0 and
            (dual['rhs_twice']<0 or
             (dual['rhs_twice']==0 and (dual['positive_mask']&mask)!=0)))


def find_dual(mask,union):
    indices = [j for j in range(16) if (mask>>j)&1]
    matrix = np.asarray(MATRIX,dtype=float)
    inequalities = -matrix[:,indices].T if indices else None
    rhs = np.asarray(RHS,dtype=float)
    result = linprog(np.zeros(7),A_ub=inequalities,
                     b_ub=np.zeros(len(indices)) if indices else None,
                     A_eq=rhs.reshape(1,7),b_eq=[-1.0],
                     bounds=[(None,None)]*7,method='highs')
    if not result.success:
        missing = mask & (FULL ^ union)
        assert missing, ('Unclassified mask',mask,union)
        j = (missing&-missing).bit_length()-1
        result = linprog(np.zeros(7),A_ub=inequalities,
                         b_ub=np.zeros(len(indices)) if indices else None,
                         A_eq=np.vstack([rhs,matrix[:,j]]),b_eq=[0.0,1.0],
                         bounds=[(None,None)]*7,method='highs')
    if not result.success:
        raise RuntimeError(('No exact-separator candidate',mask,result.message))
    dual = dual_data(primitive(result.x))
    if not excludes(dual,mask):
        raise RuntimeError(('Floating candidate failed exact recheck',mask,dual))
    return dual


def no_singleton(mask):
    return all(sum(bool(mask&(1<<j)) and bool(mask&(1<<(4+4*i+j)))
                   for j in range(4))!=1 for i in range(3))


def graph(mask):
    edges = []
    def active(j):
        return bool(mask&(1<<j))
    for i in range(3):
        for e in range(4):
            if active(e) and active(4+4*i+e):
                edges.append((e,4+4*i+e,0))
    for i,j in combinations(range(3),2):
        for e,f in combinations(range(4),2):
            left = active(4+4*i+e) and active(4+4*j+f)
            right = active(4+4*i+f) and active(4+4*j+e)
            if left and not right:
                edges.append((4+4*i+e,4+4*j+f,1))
            if right and not left:
                edges.append((4+4*i+f,4+4*j+e,1))
    return edges


def coloring_or_cycle(mask):
    edges = graph(mask)
    adjacent = [[] for _ in range(16)]
    for k,(u,v,sign) in enumerate(edges):
        adjacent[u].append((v,sign,k))
        adjacent[v].append((u,sign,k))
    colors = [None]*16
    paths = [[] for _ in range(16)]
    for root in range(16):
        if colors[root] is not None:
            continue
        colors[root] = 0
        todo = [root]
        while todo:
            u = todo.pop()
            for v,sign,k in adjacent[u]:
                color = colors[u]^sign
                if colors[v] is None:
                    colors[v] = color
                    paths[v] = paths[u]+[k]
                    todo.append(v)
                elif colors[v]!=color:
                    walk = paths[u]+[k]+list(reversed(paths[v]))
                    assert sum(edges[e][2] for e in walk)%2==1
                    return {'odd_cycle_edges':walk}
    assert all(colors[u]^colors[v]==sign for u,v,sign in edges)
    return {'colors':colors}


def transform(mask,rp,cp):
    result = 0
    for e in range(4):
        if mask&(1<<e):
            result |= 1<<cp[e]
    for i in range(3):
        for e in range(4):
            if mask&(1<<(4+4*i+e)):
                result |= 1<<(4+4*rp[i]+cp[e])
    return result


def generate():
    start = time.perf_counter()
    primal = vertices()
    union = [0]*(1<<16)
    primal_indices = [None]*(1<<16)
    moment_masks = []
    for mask in range(1<<16):
        chosen = []
        for i,(support,_) in enumerate(primal):
            if support&~mask==0 and support&~union[mask]:
                chosen.append(i)
                union[mask] |= support
        if mask and union[mask]==mask:
            primal_indices[mask] = chosen
            moment_masks.append(mask)
    assert len(moment_masks)==15603
    rejected = set(range(1<<16))-set(moment_masks)
    selectors = [None]*(1<<16)
    duals = []
    order = sorted(rejected,key=lambda m:(-m.bit_count(),m))
    for mask in order:
        if mask not in rejected:
            continue
        dual = find_dual(mask,union[mask])
        selected = [m for m in rejected if excludes(dual,m)]
        assert mask in selected
        k = len(duals)
        duals.append(dual)
        for m in selected:
            selectors[m]=k
        rejected.difference_update(selected)
        if k%50==0:
            print('Untrusted candidate search:',k+1,'dual profiles;',len(rejected),
                  'masks remaining;',round(time.perf_counter()-start,1),'s',flush=True)
    assert not rejected
    stage1 = [m for m in moment_masks if no_singleton(m)]
    assert len(stage1)==2903
    phase = {m:coloring_or_cycle(m) for m in stage1}
    stage2 = [m for m in stage1 if 'colors' in phase[m]]
    assert len(stage2)==311
    perms = [(rp,cp) for rp in permutations(range(3)) for cp in permutations(range(4))]
    canonical = {m:min((transform(m,rp,cp),i) for i,(rp,cp) in enumerate(perms)) for m in stage2}
    representatives = sorted({r for r,_ in canonical.values()})
    assert len(representatives)==16
    for mask,(rep,k) in canonical.items():
        assert transform(mask,*perms[k])==rep and rep in stage2
    return {'schema':1,'status':'untrusted_exact_candidates_only_kernel_proof_pending',
            'scope':'No Python calculation or LP result is a Lean proof or a correspondence acceptance.',
            'words':WORDS,'matrix':MATRIX,'rhs':[[v.numerator,v.denominator] for v in RHS],
            'primals':[{'mask':mask,'point':[[v.numerator,v.denominator] for v in point]}
                       for mask,point in primal],
            'primal_selectors':primal_indices,'duals':duals,'dual_selectors':selectors,
            'moment_masks':moment_masks,'no_singleton_masks':stage1,
            'phase_candidates':phase,'phase_consistent_masks':stage2,
            'symmetry_permutations':perms,'symmetry_selectors':canonical,
            'support_representatives':representatives,
            'elapsed_seconds':time.perf_counter()-start}


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    if args.output.exists():
        raise SystemExit('Refusing to overwrite candidate evidence')
    data=generate()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(data,separators=(',',':'))+'\n',encoding='utf8')
    print('Untrusted exact candidates:',len(data['primals']),'primals,',len(data['duals']),
          'dual profiles;',len(data['moment_masks']),'moment supports;',
          len(data['no_singleton_masks']),'no-singleton supports;',
          len(data['phase_consistent_masks']),'phase supports;',
          len(data['support_representatives']),'symmetry types. Lean proof pending.',flush=True)
