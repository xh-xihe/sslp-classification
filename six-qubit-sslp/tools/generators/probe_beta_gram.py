"""Exact-integer discovery probe for high-determinant binary matrices.

This is NOT a Lean certificate.  It measures a proposed search before any
trusted proof interface is written.  A sign matrix is built row by row, with
its first row positive.  Column permutations fixing previous rows allow the
next row to be sorted within each equal-column-pattern block.  Negating its
row permits at most half its entries to be negative.  These reductions leave
at least one representative of every sign-matrix equivalence class.

For each positive Gram prefix G of size k, the necessary completion bound is
det(G) * n**(n-k) >= ((bound+1)*2**(n-1))**2 (Gram/Fischer/Hadamard).
Every arithmetic search decision below uses integers.  The Gram adjugate
updates are fraction-free Schur complement identities.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import time

import numpy as np
from numba import njit


@njit(cache=True)
def popcount(x):
    count = 0
    while x:
        x &= x - 1
        count += 1
    return count


@njit(cache=True)
def visit(n, threshold, budget, k, rows, adj, det, powers, nodes, rejected, leaves):
    if nodes.sum() >= budget:
        return False
    nodes[k] += 1
    if k == n:
        # The square root is used only as a bucket proposal and is checked.
        d = int(np.sqrt(det) + 0.5)
        assert d*d == det
        assert d % (1 << (n-1)) == 0
        leaves[d // (1 << (n-1))] += 1
        return True
    patterns = np.zeros(n, dtype=np.int64)
    for j in range(n):
        for i in range(k):
            patterns[j] = 2*patterns[j] + ((rows[i] >> j) & 1)
    vector = np.zeros(n, dtype=np.int64)
    product = np.zeros(n, dtype=np.int64)
    child = np.zeros((n,n), dtype=np.int64)
    for mask in range(1, 1 << n):
        if popcount(mask) > n//2:
            continue
        canonical = True
        for j in range(1,n):
            if patterns[j] == patterns[j-1] and ((mask >> (j-1)) & 1) > ((mask >> j) & 1):
                canonical = False
                break
        if not canonical:
            continue
        for i in range(k):
            vector[i] = n - 2*popcount(rows[i] ^ mask)
        for i in range(k):
            product[i] = 0
            for j in range(k):
                product[i] += adj[i,j]*vector[j]
        next_det = n*det
        for i in range(k):
            next_det -= vector[i]*product[i]
        if next_det <= 0 or next_det*powers[n-k-1] < threshold:
            rejected[k+1] += 1
            continue
        if k+1 < n:
            for i in range(k):
                for j in range(k):
                    numerator = next_det*adj[i,j] + product[i]*product[j]
                    assert numerator % det == 0
                    child[i,j] = numerator // det
                child[i,k] = -product[i]
                child[k,i] = -product[i]
            child[k,k] = det
        rows[k] = mask
        if not visit(n,threshold,budget,k+1,rows,child,next_det,powers,nodes,rejected,leaves):
            return False
    return True


def probe(n, bound, budget):
    if not 2 <= n <= 10:
        raise ValueError('Exact int64 arithmetic bounds established only for2<=n<=10')
    nodes = np.zeros(n+1,dtype=np.int64)
    rejected = np.zeros(n+1,dtype=np.int64)
    leaves = np.zeros(1025,dtype=np.int64)
    rows = np.zeros(n,dtype=np.int64)
    adj = np.zeros((n,n),dtype=np.int64)
    adj[0,0] = 1
    powers = np.array([n**i for i in range(n+1)],dtype=np.int64)
    start = time.monotonic()
    complete = visit(n,((bound+1)*(1 << (n-1)))**2,budget,1,rows,adj,n,powers,nodes,rejected,leaves)
    return dict(sign_order=n,binary_order=n-1,beta_candidate=bound,node_budget=budget,
                complete=bool(complete),elapsed_seconds=time.monotonic()-start,
                prefix_nodes=[int(x) for x in nodes],pruned=[int(x) for x in rejected],
                high_det_leaves={str(i):int(x) for i,x in enumerate(leaves) if x},
                status='discovery-only; no kernel coverage or pruning theorem yet')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sign-order',type=int,required=True)
    parser.add_argument('--bound',type=int,required=True)
    parser.add_argument('--node-budget',type=int,default=10000000)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    result=probe(args.sign_order,args.bound,args.node_budget)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2),flush=True)


if __name__=='__main__':
    main()
