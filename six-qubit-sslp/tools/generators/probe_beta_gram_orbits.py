"""Untrusted discovery of a small signed-permutation Gram search DAG.

Every possible next sign row is considered.  Graph isomorphism only proposes
explicit row/column signed permutations, which are checked entrywise here and
will be checked again by Lean.  No graph canonicalization theorem is needed
for the eventual coverage proof.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
import json
from math import gcd, isqrt
from pathlib import Path
import time

import networkx as nx
import sympy as sp


def entry(mask,j):
    return 1-2*((mask>>j)&1)


def gram(rows,n):
    return [[n-2*(a^b).bit_count() for b in rows] for a in rows]


def signed_graph(rows,n):
    k=len(rows)
    rg=gram(rows,n)
    cols=[sum(((rows[i]>>j)&1)<<i for i in range(k)) for j in range(n)]
    cg=gram(cols,k)
    rcolors=[('r',tuple(sorted(abs(x) for x in row))) for row in rg]
    ccolors=[('c',tuple(sorted(abs(x) for x in row))) for row in cg]
    key=(tuple(sorted(rcolors)),tuple(sorted(ccolors)))
    graph=nx.Graph()
    for i,color in enumerate(rcolors+ccolors):
        graph.add_node(2*i,color=color)
        graph.add_node(2*i+1,color=color)
        graph.add_edge(2*i,2*i+1)
    for i,mask in enumerate(rows):
        for j in range(n):
            bit=(mask>>j)&1
            graph.add_edge(2*i,2*(k+j)+bit)
            graph.add_edge(2*i+1,2*(k+j)+(1-bit))
    return key,graph


def witness(mapping,rows,target,n):
    k=len(rows)
    rp=[mapping[2*i]//2 for i in range(k)]
    rs=[mapping[2*i]%2 for i in range(k)]
    cp=[mapping[2*(k+j)]//2-k for j in range(n)]
    cs=[mapping[2*(k+j)]%2 for j in range(n)]
    assert sorted(rp)==list(range(k)) and sorted(cp)==list(range(n))
    for i in range(k):
        for j in range(n):
            assert entry(rows[i],j)==(-1)**(rs[i]+cs[j])*entry(target[rp[i]],cp[j])
    return dict(row_perm=rp,row_sign=rs,column_perm=cp,column_sign=cs)


def cleared_inverse(rows,n):
    binary=[]
    for mask in rows[1:]:
        mask=mask^((1<<n)-1) if mask&1 else mask
        binary.append([((mask>>j)&1) for j in range(1,n)])
    A=sp.Matrix(binary)
    d=abs(int(A.det()))
    inverse=A.inv()
    denominator=sp.ilcm(*[x.q for x in inverse])
    integer=denominator*inverse
    assert all(x.q==1 for x in integer)
    assert A*integer==denominator*sp.eye(n-1)
    return dict(binary=binary,det_abs=d,denominator=int(denominator),
                cleared_inverse=[[int(integer[i,j]) for j in range(n-1)] for i in range(n-1)])


def build(n,bound,output):
    start=time.monotonic()
    threshold=((bound+1)*(1<<(n-1)))**2
    levels=[[dict(rows=[0],det=n)]]
    stats=[]
    for k in range(1,n):
        buckets=defaultdict(list)
        next_level=[]
        edges=[]
        rejected=0
        for source,node in enumerate(levels[-1]):
            rows=node['rows']
            G=sp.Matrix(gram(rows,n))
            det=int(G.det())
            adj=[[int(x) for x in row] for row in G.adjugate().tolist()]
            assert det==node['det']
            node_edges=[]
            for mask in range(1<<n):
                vector=[n-2*(row^mask).bit_count() for row in rows]
                prod=[sum(adj[i][j]*vector[j] for j in range(k)) for i in range(k)]
                child_det=n*det-sum(x*y for x,y in zip(vector,prod))
                if child_det<=0 or child_det*n**(n-k-1)<threshold:
                    rejected+=1
                    node_edges.append(dict(mask=mask,pruned=True,det=child_det))
                    continue
                candidate=rows+[mask]
                key,graph=signed_graph(candidate,n)
                target_index=None
                transport=None
                for index,target_graph in buckets[key]:
                    matcher=nx.algorithms.isomorphism.GraphMatcher(graph,target_graph,
                        node_match=lambda a,b:a['color']==b['color'])
                    if matcher.is_isomorphic():
                        target_index=index
                        transport=witness(matcher.mapping,candidate,next_level[index]['rows'],n)
                        break
                if target_index is None:
                    target_index=len(next_level)
                    next_level.append(dict(rows=candidate,det=child_det))
                    buckets[key].append((target_index,graph))
                    transport=witness({i:i for i in graph},candidate,candidate,n)
                node_edges.append(dict(mask=mask,target=target_index,transport=transport))
            edges.append(node_edges)
        for node,node_edges in zip(levels[-1],edges):
            node['edges']=node_edges
        levels.append(next_level)
        row=dict(depth=k+1,representatives=len(next_level),parents=len(levels[-2]),
                 candidates=len(levels[-2])*(1<<n),pruned=rejected,
                 elapsed_seconds=round(time.monotonic()-start,3))
        stats.append(row)
        print(json.dumps(row),flush=True)
    for node in levels[-1]:
        node['leaf']=cleared_inverse(node['rows'],n)
        assert node['leaf']['denominator']<=bound,node
    result=dict(sign_order=n,binary_order=n-1,bound=bound,threshold_squared=threshold,
                levels=levels,stats=stats,elapsed_seconds=time.monotonic()-start,
                status='untrusted proposal; exact transports and leaf identities checked; no Lean coverage yet')
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(result,separators=(',',':'))+'\n',encoding='utf-8')
    print('COMPLETE',len(levels[-1]),'leaf representatives',round(time.monotonic()-start,3),'seconds',flush=True)
    print('Leaf determinant/denominator pairs:',sorted({(x['leaf']['det_abs'],x['leaf']['denominator']) for x in levels[-1]}),flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sign-order',type=int,required=True)
    parser.add_argument('--bound',type=int,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    if not 2<=args.sign_order<=10:
        parser.error('only sign orders2..10 supported')
    build(args.sign_order,args.bound,args.output)
